type content = Node | Content

type branch = Branch of string

type commit = Commit of (int list * int)

type tree = Tree of (content * string * int) list

type block = Block of string

type value =
  | Value_commit of commit
  | Value_tree of tree
  | Value_block of block

module Tag_module = struct
  type t = branch

  let compare t1 t2 = compare t1 t2
end

module TagMap = Map.Make (Tag_module)

module Block_module = struct
  type t = int

  let compare t1 t2 = compare t1 t2
end

module BlockMap = Map.Make (Block_module)

let read_tagstore br tagstore =
  try Some (TagMap.find br tagstore) with _ -> None

let read_blockstore node_hash blockstore = BlockMap.find node_hash blockstore

let get_tree_hash commit_node =
  let _, tree_hash = commit_node in
  tree_hash

let findtag branch tagstore =
  try Some (TagMap.find (Branch branch) tagstore) with _ -> None

let banyan_add_first branch key value blockstore tagstore =
  let blob_hash = Hashtbl.hash value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in
  let new_tree_node = [ (Content, key, blob_hash) ] in
  let blockstore =
    BlockMap.add
      (Hashtbl.hash new_tree_node)
      (Value_tree (Tree new_tree_node)) blockstore
  in
  let new_commit_node = ([], Hashtbl.hash new_tree_node) in
  let blockstore =
    BlockMap.add
      (Hashtbl.hash new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in
  let tagstore =
    TagMap.add (Branch branch) (Hashtbl.hash new_commit_node) tagstore
  in
  (blockstore, tagstore)

let banyan_add_new commit_hash branch key value blockstore tagstore =
  let commit_node = read_blockstore commit_hash blockstore in
  match commit_node with
  | Value_commit (Commit commit_node) ->
      let _, tree_hash = commit_node in
      let tree_node_value = BlockMap.find tree_hash blockstore in

      let tree_node =
        match tree_node_value with
        (*tree_node is new_tree_node*)
        | Value_tree (Tree x) -> x
      in

      let blob_hash = Hashtbl.hash value in
      let blockstore =
        BlockMap.add blob_hash (Value_block (Block value)) blockstore
      in

      let new_tree_node = (Content, key, blob_hash) in
      let tree_node' = new_tree_node :: tree_node in
      let blockstore =
        BlockMap.add (Hashtbl.hash tree_node') (Value_tree (Tree tree_node'))
          blockstore
      in

      let new_commit_node = ([ -1 ], Hashtbl.hash tree_node') in

      let blockstore =
        BlockMap.add
          (Hashtbl.hash new_commit_node)
          (Value_commit (Commit new_commit_node)) blockstore
      in

      let tagstore =
        TagMap.add (Branch branch) (Hashtbl.hash new_commit_node) tagstore
      in

      (blockstore, tagstore)

let banyan_add branch key value blockstore tagstore =
  let blockstore, tagstore =
    match findtag branch tagstore with
    | Some commit_hash ->
        banyan_add_new commit_hash branch key value blockstore tagstore
    | None -> banyan_add_first branch key value blockstore tagstore
  in
  (blockstore, tagstore)

let rec find_tree_node key treelist =
  match treelist with
  | [] -> Hashtbl.hash ""
  | [ (_, k, v) ] -> if String.compare k key == 0 then v else Hashtbl.hash ""
  | (_, k, v) :: t ->
      if String.compare k key == 0 then v else find_tree_node key t

let banyan_read branch key blockstore tagstore =
  let commit_hash = findtag branch tagstore in
  let commit_hash = match commit_hash with Some x -> x | None -> -1 in
  if commit_hash != -1 then
    let commit_node = read_blockstore commit_hash blockstore in
    match commit_node with
    | Value_commit (Commit commit_node) -> (
        let _, tree_hash = commit_node in
        let treenode = read_blockstore tree_hash blockstore in
        match treenode with
        | Value_tree (Tree treelist) -> (
            let val_hash = find_tree_node key treelist in

            let blocknode = read_blockstore val_hash blockstore in
            match blocknode with
            | Value_block (Block x) -> print_string ("value found: " ^ x ^ "\n")
            | _ -> print_string "string didnt match\n" ) )
  else print_string "\nwrong branch\n"

let find_treelist commit_hash blockstore =
  if commit_hash != -1 then
    let commit_node = read_blockstore commit_hash blockstore in
    match commit_node with
    | Value_commit (Commit commit_node) -> (
        let _, tree_hash = commit_node in
        let treenode = read_blockstore tree_hash blockstore in
        match treenode with Value_tree (Tree treelist) -> treelist )
  else []

let check_exist p redlist =
  List.exists (fun x -> String.compare x p == 0) redlist

(* match
     List.exists
       (fun x ->
         print_string ("**inside check exists: " ^ x ^ " " ^ p);
         String.compare x p == 0)
       redlist
   with
   | true ->
       print_string "\ncheck exists returns true";
       true
   | false ->
       print_string "\ncheck exists returns false";
       false *)

(* let rec testree treelist =
  print_string "\ntest tree: ";
  match treelist with
  | [] -> print_string "ist over"
  | (_, p, _) :: t ->
      print_string p;
      testree t *)

let rec add_redlist newtreelist redlist treelist =
  let newtreelist =
    match treelist with
    | [] -> newtreelist
    | (c, p, v) :: t ->
        if check_exist p redlist then
          add_redlist newtreelist redlist t
        else
          let newtreelist = (c, p, v) :: newtreelist in
          add_redlist newtreelist redlist t
  in

  newtreelist

(* let test valhash blockstore =
  print_string "\ntest";
  print_string "blockstore cardinality: ";
  print_int (BlockMap.cardinal blockstore);
  match BlockMap.mem valhash blockstore with
  | true -> print_string "true"
  | false -> print_string "false" *)

(* let rec testreecontent treelist blockstore =
  print_string "\nin testtreecontent, length = ";
  print_int (List.length treelist);
  match treelist with
  | [] -> print_string "\nlist over"
  | (_, p, blockhash) :: t -> (
      let v = BlockMap.find blockhash blockstore in
      match v with
      | Value_block (Block x) ->
          print_string ("\n" ^ p ^ "  " ^ x);
          testreecontent t blockstore ) *)

let rec merge_trees treelist1 treelist2 new_tree_list red_list blockstore
    conflict_string ops =
  match treelist1 with
  | [] -> (add_redlist new_tree_list red_list treelist2, conflict_string)
  | (c, p, val_hash1) :: t -> (
      let val_hash2 = find_tree_node p treelist2 in

      match val_hash2 with
      | 0 ->
          ((c, p, val_hash1) :: new_tree_list, conflict_string);
          merge_trees t treelist2 new_tree_list red_list blockstore
            conflict_string ops
      | _ -> (
          let v1 = read_blockstore val_hash1 blockstore in
          let v2 = read_blockstore val_hash2 blockstore in
          match (v1, v2) with
          | Value_block (Block value1), Value_block (Block value2) ->
              if String.compare value1 value2 == 0 then
                let red_list = p :: red_list in
                let new_tree_list, conflict_string =
                  ((c, p, val_hash1) :: new_tree_list, conflict_string)
                in
                merge_trees t treelist2 new_tree_list red_list blockstore
                  conflict_string ops
              else if ops = "publish" then
                let conflict_string = value1 ^ "_" ^ value2 in

                let red_list = p :: red_list in

                let new_tree_list, conflict_string =
                  ( (c, p, Hashtbl.hash conflict_string) :: new_tree_list,
                    conflict_string )
                in

                merge_trees t treelist2 new_tree_list red_list blockstore
                  conflict_string ops
              else
                let conflict_string = value1 in

                let red_list = p :: red_list in

                let new_tree_list, conflict_string =
                  ( (c, p, Hashtbl.hash conflict_string) :: new_tree_list,
                    conflict_string )
                in

                merge_trees t treelist2 new_tree_list red_list blockstore
                  conflict_string ops ) )

(* let temptest key new_tree_node blockstore =
  print_string "\nin temptest: ";
  let new_tree_node = find_tree_node key new_tree_node in
  print_string "treehash = ";
  print_int (Hashtbl.hash new_tree_node);
  let a = BlockMap.find (Hashtbl.hash new_tree_node) blockstore in
  print_string "***";
  match a with
  | Value_tree (Tree ((_, _, x) :: _)) -> (
      print_string "  matched in test";
      let y = BlockMap.find x blockstore in
      match y with Value_block (Block x) -> print_string x ) *)

let merge_branches branch1 branch2 blockstore tagstore ops =
  let c1 =
    match findtag branch1 tagstore with
    | Some x -> x
    | None -> failwith "illegal branch1"
  in
  let c2 =
    match findtag branch2 tagstore with
    | Some x -> x
    | None -> failwith "illegar branch2"
  in

  let treelist1 = find_treelist c1 blockstore in
  let treelist2 = find_treelist c2 blockstore in

  (* print_string "\n\ncheckout treelist1";
       testreecontent treelist1 blockstore;
       print_string "\n\ncheckout treelist2";
       testreecontent treelist2 blockstore;
     print_string "\ntree checkout done"; *)

  let new_tree_node, conflict_string =
    merge_trees treelist1 treelist2 [] [] blockstore "" ops
  in

  let blockstore =
    if conflict_string != "" then
      BlockMap.add
        (Hashtbl.hash conflict_string)
        (Value_block (Block conflict_string)) blockstore
    else blockstore
  in

  let blockstore =
    BlockMap.add
      (Hashtbl.hash new_tree_node)
      (Value_tree (Tree new_tree_node)) blockstore
  in

  let new_commit_node = ([ c1; c2 ], Hashtbl.hash new_tree_node) in

  let blockstore =
    BlockMap.add
      (Hashtbl.hash new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in

  let tagstore =
    TagMap.add (Branch branch2) (Hashtbl.hash new_commit_node) tagstore
  in

  (blockstore, tagstore)

let banyan_op branch key value blockstore tagstore =
  let blockstore, tagstore = banyan_add branch key value blockstore tagstore in
  (blockstore, tagstore)

let publish_to_public private_branch public_branch blockstore tagstore =
  merge_branches private_branch public_branch blockstore tagstore "publish"

let publish branch replica blockstore tagstore =
  let latest_commit = findtag replica tagstore in
  match latest_commit with
  | Some _ ->
      let blockstore, tagstore =
        publish_to_public branch replica blockstore tagstore
      in
      (blockstore, tagstore)
  | None ->
      let commit =
        match findtag branch tagstore with
        | None -> failwith "illegal branch to merge"
        | Some x -> x
      in
      let tagstore = TagMap.add (Branch replica) commit tagstore in

      (blockstore, tagstore)

let refresh branch replica blockstore tagstore =
  let latest_commit = findtag replica tagstore in
  match latest_commit with
  | Some _ ->
      let blockstore, tagstore =
        merge_branches replica branch blockstore tagstore "refresh"
      in
      (blockstore, tagstore)
  | None -> (blockstore, tagstore)

let test_banyan_read branch key value blockstore tagstore =
  let commit_hash = findtag branch tagstore in
  let commit_hash = match commit_hash with Some x -> x | None -> -1 in
  if commit_hash != -1 then
    let commit_node = read_blockstore commit_hash blockstore in
    match commit_node with
    | Value_commit (Commit commit_node) -> (
        let _, tree_hash = commit_node in
        let treenode = read_blockstore tree_hash blockstore in
        match treenode with
        | Value_tree (Tree treelist) -> (
            let blockhash = find_tree_node key treelist in
            let blocknode = read_blockstore blockhash blockstore in
            match blocknode with
            | Value_block (Block x) -> (
                match String.compare x value with
                | 0 -> print_string ("\nread test passed: " ^ x ^ "\n")
                | _ -> print_string ("\nread test failed: " ^ x ^ "\n") ) ) )
  else print_string "\nread test failed: commit not found\n"

let _ =
  let tagstore = TagMap.empty in
  let blockstore = BlockMap.empty in

  let blockstore, tagstore =
    banyan_op "branch" "key1" "value1" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "branch" "key2" "value2" blockstore tagstore
  in

  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key1" "value1" blockstore tagstore in
  let _ = test_banyan_read "replica1" "key1" "value1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key2" "value2" blockstore tagstore in
  let _ = test_banyan_read "replica1" "key2" "value2" blockstore tagstore in

  let blockstore, tagstore =
    banyan_op "branch1" "key1" "value3" blockstore tagstore
  in
  print_string "\npublishing2\n";
  let blockstore, tagstore = publish "branch1" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch1" "key1" "value3" blockstore tagstore in
  let _ =
    test_banyan_read "replica1" "key1" "value3_value1" blockstore tagstore
  in

  (* let _ = test_banyan_read "branch1" "key3" "value3" blockstore tagstore in
     let _ = test_banyan_read  "replica1" "key3" "value3" blockstore tagstore in *)

  (* let blockstore, tagstore =
       banyan_op "branch" "key4" "value3" blockstore tagstore
     in
     print_string "\npublishing\n";
     let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
     let _ = test_banyan_read "branch" "key4" "value3" blockstore tagstore in
     let _ = test_banyan_read  "replica1" "key4" "value3" blockstore tagstore in *)
  print_string "\ntesting refresh\n";
  let blockstore, tagstore = refresh "branch" "replica1" blockstore tagstore in
  let _ =
    test_banyan_read "branch" "key1" "value3_value1" blockstore tagstore
  in
  let _ = test_banyan_read "branch" "key2" "value2" blockstore tagstore in
  (* let _ = test_banyan_read "branch" "key3" "value3" blockstore tagstore in *)
  ()
