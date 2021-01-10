open Types
open Utils


let rec list_prev_commits commit_hash blockstore commit_list =
  let commit = read_blockstore commit_hash blockstore in
  match commit with 
  | Value_commit(Commit([], cmt)) -> commit :: commit_list
  | Value_commit(Commit(h::t, cmt)) -> 
              (let lst = commit :: commit_list in
              list_prev_commits h blockstore lst)
  (*| Value_commit(Commit(h::t, cmt)) -> log("list_prev_commits : multiple parents in commit"); (*fix this*)
                                      failwith "multiple parents in commit"*)


let rec match_commit commit_lst commit_hash blockstore =
  let commit = read_blockstore commit_hash blockstore in
  match commit with
  | Value_commit(Commit([], cmt)) -> commit_hash (*create initial commit as empty, to make this work correctly*)  (*fix this*)
                                          (*if (List.exists (fun x -> x == cmt) commit_lst) then cmt else (return dummy commit here*)
  | Value_commit(Commit(h::[], cmt)) -> if (List.exists (fun x -> x = commit) commit_lst) then commit_hash else match_commit commit_lst h blockstore


let resolve_conflict lca v1 v2 key blockstore =
  (*(v1 ^ "_" ^ x) *)
  let lca_treelist = find_treelist lca blockstore in
  let v = findKeyInTree key lca_treelist in 
  match v with 
  |Hash_block "" -> (v1 ^ "_" ^ v2)
  |Hash_block x -> (x ^ "_" ^ v1 ^ "_" ^ v2)

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


(*storing the list of commits from latest to root of one of the branches and 
then matching that list with the commits of second branch from latest to root. 
First match is returned as LCA*)
let find_lca c1 c2 blockstore tagstore =
  let commit_lst1 = list_prev_commits c1 blockstore [] in
  let lca = match_commit commit_lst1 c2 blockstore in
  lca


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

  (*finding LCA of the two branches*)
  let lca = find_lca c1 c2 blockstore tagstore in
  
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
