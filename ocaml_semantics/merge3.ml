open Types
open Utils

type mark =
    |Seen1
    |Seen2
    |LCA
    |SeenBoth

module K = struct 
    type t = hash
    let compare = compare
    let hash = Hashtbl.hash (*print_string "need to change this hash fun"; (fun x -> 5)*)
    let equal = (==) (*print_string "need to change this equal  fun"; (fun x y -> true)*)
end

module KSet = Set.Make(K)
module KHashtbl = Hashtbl.Make(K)

type state = {
    marks : mark KHashtbl.t;
    (* marks of commits already explored *)
    parents : KSet.t KHashtbl.t;
    (* parents of commits already explored *)
    layers : (int, KSet.t) Hashtbl.t;
    (* layers of commit, sorted by depth *)
    c1 : hash;
    (* initial state 1 *)
    c2 : hash;
    (* initial state 2 *)
    mutable depth : int;
    (* the current exploration depth *)
    mutable lcas : int;
    (* number of commit marked with LCA *)
    mutable complete : bool; (* is the exploration complete? *)
  }

  let get_mark_exn t elt = KHashtbl.find t.marks elt
  
  let get_mark t elt = try Some (get_mark_exn t elt) with Not_found -> None
  
  let set_mark t elt mark = KHashtbl.replace t.marks elt mark
  
  let get_layer t d = try Hashtbl.find t.layers d with Not_found -> KSet.empty
  
  let add_to_layer t d k =
    Hashtbl.replace t.layers d (KSet.add k (get_layer t d))
  
  let add_parent t c p = KHashtbl.add t.parents c p
  
  let get_parent t c =
    try KHashtbl.find t.parents c with Not_found -> KSet.empty
  
  let incr_lcas t = t.lcas <- t.lcas + 1
  
  let decr_lcas t = t.lcas <- t.lcas - 1
  
  let both_seen t k =
    match get_mark t k with
    | None | Some Seen1 | Some Seen2 -> false
    | _ -> true

let equal_keys = (=)
  let lca_calls = ref 0

  let empty_state c1 c2 =
    let t =
      {
        marks = KHashtbl.create 10;
        parents = KHashtbl.create 10;
        layers = Hashtbl.create 10;
        c1;
        c2;
        depth = 0;
        lcas = 0;
        complete = false;
      }
    in
    set_mark t c1 Seen1;
    set_mark t c2 Seen2;
    t

let update_mark t mark commit =
    let new_mark =
      match (mark, get_mark t commit) with
      | Seen1, Some Seen1 | Seen1, None -> Seen1
      | Seen2, Some Seen2 | Seen2, None -> Seen2
      | SeenBoth, Some LCA ->
          decr_lcas t;
          SeenBoth
      | SeenBoth, _ -> SeenBoth
      | Seen1, Some Seen2 | Seen2, Some Seen1 ->
          incr_lcas t;
          LCA
      | _, Some LCA -> LCA
      | _ -> SeenBoth
    in
    (* check for fast-forwards *)
    let is_init () = equal_keys commit t.c1 || equal_keys commit t.c2 in
    let is_shared () = new_mark = SeenBoth || new_mark = LCA in
    if is_shared () && is_init () then (
      (* Logs.debug (fun f -> f "fast-forward"); *)
      t.complete <- true);
    set_mark t commit new_mark;
    new_mark

  let update_ancestors_marks t mark commit =
    let todo = Queue.create () in
    Queue.add commit todo;
    let rec loop mark =
      if Queue.is_empty todo then ()
      else
        let a = Queue.pop todo in
        let old_mark = get_mark t a in
        let mark = update_mark t mark a in
        let () =
          match old_mark with
          | Some (SeenBoth | LCA) -> () (* Can't be an LCA lower down *)
          | Some old when old = mark -> () (* No change *)
          | _ -> KSet.iter (fun x -> Queue.push x todo) (get_parent t a)
        in
        loop (if mark = LCA then SeenBoth else mark)
    in
    loop mark

let update_parents t depth commit parents =
    add_parent t commit parents;
    add_to_layer t depth commit;
    if depth <> t.depth then (
      assert (depth = t.depth + 1);
      (* before starting to explore a new layer, check if we really
         have some work to do, ie. do we still have a commit seen only
         by one node? *)
      let layer = get_layer t t.depth in
      let complete = KSet.for_all (both_seen t) layer in
      if complete then t.complete <- true else t.depth <- depth);
    let mark = get_mark_exn t commit in
    KSet.iter (update_ancestors_marks t mark) parents

 let lcas t =
    KHashtbl.fold (fun k v acc -> if v = LCA then k :: acc else acc) t.marks []


  let check ~max_depth ~n t =
    if t.depth > max_depth then `Max_depth_reached
    else if t.lcas > n then `Too_many_lcas
    else if t.lcas = n || t.complete then `Stop
    else `Continue

let read_parents commit blockstore =
    (* match (S.find t commit) with
    | None -> KSet.empty
    | Some c -> KSet.of_list (S.Val.parents c) *)
    let commit_node = BlockMap.find commit blockstore in 
    (match commit_node with
    |Value_commit (Commit (parents, _)) -> parents)

let rec unqueue todo seen =
    if Queue.is_empty todo then None
    else
      let ((_, commit) as pop) = Queue.pop todo in
      if KSet.mem commit seen then unqueue todo seen else Some pop

  let traverse_bfs blockstore ~f ~check ~init ~return =
    let todo = Queue.create () in
    let add_todo d x = Queue.add (d, x) todo in
    KSet.iter (add_todo 0) init;
    let rec aux seen =
      match check () with
      | (`Too_many_lcas | `Max_depth_reached) as x -> Error x
      | `Stop -> return ()
      | `Continue -> (
          match unqueue todo seen with
          | None -> return ()
          | Some (depth, commit) ->
              (* Log.debug "lca %d: %s.%d %a"
                 !lca_calls (pp_key commit) depth force (pp ()); *)
              let seen = KSet.add commit seen in
              (* read_parents t commit >>= fun parents -> *)
              let parents = read_parents commit blockstore in 
              let parents = KSet.of_list parents in 
              let () = f depth commit parents in
              let parents = KSet.diff parents seen in
              KSet.iter (add_todo (depth + 1)) parents;
              aux seen)
    in
    aux KSet.empty

let find_lca ?(max_depth = max_int) ?(n = max_int) c1 c2 blockstore tagstore = 
    incr lca_calls;
    if max_depth < 0 then Error `Max_depth_reached
    else if n <= 0 then Error `Too_many_lcas
    else if equal_keys c1 c2 then Ok [ c1 ]
    else
      let init = KSet.of_list [ c1; c2 ] in
      let s = empty_state c1 c2 in
      let check () = check ~max_depth ~n s in
      (* let pp () = pp_state s in *)
      let return () = Ok (lcas s) in
        traverse_bfs blockstore ~f:(update_parents s) ~check ~init ~return
      (* let t0 = Sys.time () in
      Lwt.finalize
        (fun () ->
          traverse_bfs t ~f:(update_parents s) ~pp ~check ~init ~return)
        (fun () ->
          let t1 = Sys.time () -. t0 in
          Log.debug (fun f ->
              f "lcas %d: depth=%d time=%.4fs" !lca_calls s.depth t1);
          Lwt.return_unit) *)


(* let rec list_prev_commits commit_hash blockstore commit_list =
  let commit = read_blockstore commit_hash blockstore in
  match commit with 
  | Value_commit(Commit([], cmt)) -> commit :: commit_list
  | Value_commit(Commit(h::t, cmt)) -> 
              (let lst = commit :: commit_list in
              list_prev_commits h blockstore lst) *)
              
  (*| Value_commit(Commit(h::t, cmt)) -> log("list_prev_commits : multiple parents in commit"); (*fix this*)
                                      failwith "multiple parents in commit"*)


(* let rec match_commit commit_lst commit_hash blockstore =
  let commit = read_blockstore commit_hash blockstore in
  match commit with
  | Value_commit(Commit([], cmt)) -> commit_hash (*create initial commit as empty, to make this work correctly*)  (*fix this*)
                                          (*if (List.exists (fun x -> x == cmt) commit_lst) then cmt else (return dummy commit here*)
  | Value_commit(Commit(h::t, cmt)) -> if (List.exists (fun x -> x = commit) commit_lst) then commit_hash else match_commit commit_lst h blockstore *)


let resolve_conflict lca v1 v2 key blockstore =
  (*(v1 ^ "_" ^ x) *)
  let lca_treelist = find_treelist lca blockstore in
  let v = findKeyInTree key lca_treelist in 
  match v with 
  |Hash_block "" -> (v1 ^ "_" ^ v2)
  |Hash_block x -> print_string ("key : " ^ key ^ " lca : " ^ x ^ " v1 : " ^ v1 ^ " v2 : " ^ v2); 
                    ("'" ^ x ^ "'_" ^ v1 ^ "_" ^ v2)

(*add_redlist is to add the keys which are present only in second branch*)
let rec add_redlist newtreelist redlist treelist =
  let newtreelist =
    match treelist with
    | [] -> newtreelist
    | (c, p, v) :: t ->
        if check_exist p redlist then add_redlist newtreelist redlist t
        else
          let newtreelist = (c, p, v) :: newtreelist in
          add_redlist newtreelist redlist t
  in
  newtreelist


let rec merge_trees treelist1 treelist2 new_tree_list red_list lca blockstore = 
  match treelist1 with
  | [] -> blockstore, add_redlist new_tree_list red_list treelist2 (*blockstore, new_tree_list *)
  | (c, p, Hash_block v1) :: t ->
      let v2 = findKeyInTree p treelist2 in

      let new_tree_list, red_list, blockstore =
        match v2 with
        | Hash_block "" ->
            (c, p, Hash_block v1) :: new_tree_list, red_list, blockstore
        | Hash_block x ->
            if String.compare v1 x == 0 then
              let red_list = p :: red_list in
              (c, p, Hash_block v1) :: new_tree_list, red_list, blockstore
            else
              let conflict_string = resolve_conflict lca v1 x p blockstore in 
              let blockstore = BlockMap.add (Hash_block conflict_string) (Value_block (Block conflict_string)) blockstore in
              print_string ("\nin merge " ^ p ^ " " ^ conflict_string ^ "\n");
              let red_list = p :: red_list in
              (c, p, Hash_block conflict_string) :: new_tree_list, red_list, blockstore
      in

      merge_trees t treelist2 new_tree_list red_list lca blockstore


let rec three_way_merge c1 c2 ?max_depth ?n blockstore tagstore =
    if equal_keys c1 c2 then c1
    else
      let lcas = find_lca ?max_depth ?n c1 c2 blockstore tagstore in

      let old () =
        match lcas with
        | Error `Too_many_lcas -> failwith "Too many lcas"
        | Error `Max_depth_reached -> failwith "Max depth reached"
        | Ok [] -> None (* no common ancestor *)
        | Ok (old :: olds) ->
            let rec aux acc = function
              | [] -> (Some acc)
              | old :: olds ->
                  let acc = three_way_merge acc old blockstore tagstore in 
                  aux acc olds
            in
            aux old olds
      in

      let lca = old () in 
      match lca with 
      |Some x -> x
      |None -> failwith "no lca found"  (*fix this: c1 should be replaced with some suitable value*)
      

let merge_branches guestBranch hostBranch blockstore tagstore =
  let c1 =
    match findtag guestBranch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch1"
  in
  let c2 =
    match findtag hostBranch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch2"
  in

  let lca = three_way_merge c1 c2 blockstore tagstore in

  let treelist1 = find_treelist c1 blockstore in 
  let treelist2 = find_treelist c2 blockstore in  

  let blockstore, new_tree_node = merge_trees treelist1 treelist2 [] [] lca blockstore in
  
  let blockstore =
    BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
      blockstore
  in

  let new_commit_node = ([ c2;c1 ], Hash_tree new_tree_node) in (*parent commit of host branch will appear first in the list to find lca easily*)
  (*parent is still dummy, because we are fillingin only types, not values: (hash list * hash) list * hash*)
  let blockstore =
    BlockMap.add (Hash_commit new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in

  let tagstore =
  	print_string ("merging: host branch " ^ hostBranch ^ "\n");
    TagMap.add (Branch hostBranch) (Hash_commit new_commit_node) tagstore
  in

 (blockstore, tagstore)