type content = Node | Content

type branch = Branch of string

(*for keys*)
type hash =
  | Hash_block of string
  | Hash_tree of (content * string * hash) list
  | Hash_commit of (hash list * hash)
  | Hash_dummy

(*for values*)
type commit = Commit of (hash list * hash)

type tree = Tree of (content * string * hash) list

type block = Block of string

type value =
  | Value_commit of commit
  | Value_tree of tree
  | Value_block of block

module Tag_module = struct
  type t = branch

  let compare t1 t2 =
    match (t1, t2) with Branch b1, Branch b2 -> String.compare b1 b2
end

module TagMap = Map.Make (Tag_module)

module Block_module = struct
  type t = hash

  let rec compare t1 t2 =
    match (t1, t2) with
    | Hash_block x, Hash_block y -> String.compare x y
    | Hash_block x, Hash_tree y -> 1
    | Hash_block x, Hash_commit y -> 1
    | Hash_tree x, Hash_block y -> 1
    | ( Hash_tree ((a, b, Hash_block c) :: _),
        Hash_tree ((d, e, Hash_block f) :: _) ) ->
        String.compare c f (*pass different values for every key*)
    | Hash_tree x, Hash_commit y -> 1
    | Hash_commit x, Hash_block y -> 1
    | Hash_commit x, Hash_tree y -> 1
    | Hash_commit (x, y), Hash_commit (a, b) -> compare y b
end

module BlockMap = Map.Make (Block_module)

let read_tagstore br tagstore =
  try Some (TagMap.find br tagstore) with _ -> None

(*Commit ([Hash_dummy], Hash_dummy)*)

let read_blockstore node_hash blockstore = BlockMap.find node_hash blockstore

let get_tree_hash commit_node =
  let _, tree_hash = commit_node in
  tree_hash

let findtag branch tagstore =
  try Some (TagMap.find (Branch branch) tagstore) with _ -> None

let banyan_add_first branch key value blockstore tagstore =
  let blob_hash = Hash_block value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in
  let new_tree_node = [ (Content, key, blob_hash) ] in
  let blockstore =
    BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
      blockstore
  in
  let new_commit_node = ([ Hash_dummy ], Hash_tree new_tree_node) in
  let blockstore =
    BlockMap.add (Hash_commit new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in
  let tagstore =
    TagMap.add (Branch branch) (Hash_commit new_commit_node) tagstore
  in
  (blockstore, tagstore)

let banyan_add_new commit_hash branch key value blockstore tagstore =
  let commit_node = match commit_hash with Hash_commit node -> node in
  (*node is equivalent to new_commit_node in Hash_commit(new_commit_node))*)
  let _, tree_hash = commit_node in
  (*tree hash is equivalent to Hash_tree(new_tree_node)*)
  let tree_node_value = BlockMap.find tree_hash blockstore in
  (*tree_node_value should be (Value_tree (Tree (new_tree_node)))*)
  let tree_node =
    match tree_node_value with
    (*tree_node is new_tree_node*)
    | Value_tree (Tree x) -> x
  in

  let blob_hash = Hash_block value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in

  let new_tree_node = (Content, key, blob_hash) in
  let tree_node' = new_tree_node :: tree_node in
  let blockstore =
    BlockMap.add (Hash_tree tree_node') (Value_tree (Tree tree_node'))
      blockstore
  in

  let new_commit_node = ([ Hash_dummy ], Hash_tree tree_node') in
  (*parent is still dummy, because we are fillingin only types, not values: (hash list * hash) list * hash*)
  let blockstore =
    BlockMap.add (Hash_commit new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in

  let tagstore =
    TagMap.add (Branch branch) (Hash_commit new_commit_node) tagstore
  in

  (blockstore, tagstore)

let banyan_add branch key value blockstore tagstore =
  let blockstore, tagstore =
    match findtag branch tagstore with
    | Some commit_hash ->
        print_string "some ";
        banyan_add_new commit_hash branch key value blockstore tagstore
    | None ->
        print_string "none ";
        banyan_add_first branch key value blockstore tagstore
  in
  (blockstore, tagstore)

let rec find_tree_node key treelist =
  match treelist with
  | [] -> Hash_block ""
  | [ (_, k, v) ] -> if String.compare k key == 0 then v else Hash_block ""
  | (_, k, v) :: t ->
      if String.compare k key == 0 then v else find_tree_node key t

let banyan_read branch key blockstore tagstore =
  let item =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch"
  in

  let item =
    match item with
    | Hash_commit (_, x) -> (
        match x with
        | Hash_tree treelist -> (
            let v = find_tree_node key treelist in
            match v with
            | Hash_block z -> (
                match z with
                | value -> print_string ("value found: " ^ value ^ "\n")
                | _ -> print_string "string didnt match\n" ) ) )
  in

  ()

(*testing*)
let test_banyan_add_first branch key value blockstore tagstore =
  let blockstore, tagstore =
    banyan_add_first branch key value blockstore tagstore
  in

  let item =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch"
  in
  let item =
    match item with
    | Hash_commit (_, x) -> (
        match x with
        | Hash_tree treelist -> (
            let v = find_tree_node key treelist in
            match v with
            | Hash_block z -> (
                match z with
                | value -> print_string "tag commit matched\n"
                | _ -> print_string "string didnt match" ) ) )
  in

  ()

let test_banyan_read branch key value blockstore tagstore =
  let item =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch"
  in
  let item =
    match item with
    | Hash_commit (_, x) -> (
        match x with
        | Hash_tree treelist -> (
            let v = find_tree_node key treelist in
            match v with
            | Hash_block z ->
                if String.compare z value == 0 then
                  print_string ("read test passed: " ^ value ^ "\n")
                else print_string "read test failed" ) )
  in

  ()

(*testing*)

let find_treelist commit =
  let treelist =
    match commit with
    | Hash_commit (_, x) -> ( match x with Hash_tree treelist -> treelist )
  in

  treelist

let check_exist p redlist =
  List.exists (fun x -> String.compare x p == 0) redlist

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

let rec merge_trees treelist1 treelist2 new_tree_list red_list =
  match treelist1 with
  | [] -> add_redlist new_tree_list red_list treelist2
  | (c, p, Hash_block v1) :: t ->
      let v2 = find_tree_node p treelist2 in

      let new_tree_list =
        match v2 with
        | Hash_block "" ->
            print_string ("in merge " ^ v1 ^ "\n");
            (c, p, Hash_block v1) :: new_tree_list
        | Hash_block x ->
            print_string ("\nin merge " ^ v1 ^ "\n");
            if String.compare v1 x == 0 then
              let red_list = p :: red_list in
              (c, p, Hash_block v1) :: new_tree_list
            else
              let conflict_string = v1 ^ "_" ^ x in
              print_string ("\nin merge " ^ conflict_string ^ "\n");
              let red_list = p :: red_list in
              (c, p, Hash_block conflict_string) :: new_tree_list
      in

      merge_trees t treelist2 new_tree_list red_list

let merge_branches branch1 branch2 tagstore =
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

  let treelist1 = find_treelist c1 in
  let treelist2 = find_treelist c2 in

  let new_treelist = merge_trees treelist1 treelist2 [] [] in

  let v = find_tree_node "key" new_treelist in
  ( match v with
  | Hash_block z ->
      if String.compare z "value3" == 0 then
        print_string ("read test passed: " ^ z ^ "\n")
      else print_string ("read test failed " ^ z) );

  let v = find_tree_node "key2" new_treelist in
  ( match v with
  | Hash_block z ->
      if String.compare z "value2" == 0 then
        print_string ("read test passed: " ^ z ^ "\n")
      else print_string "read test failed" );

  ()

let banyan_op branch key value blockstore tagstore =
  let blockstore, tagstore = banyan_add branch key value blockstore tagstore in
  (blockstore, tagstore)

let _ =
  let tagstore = TagMap.empty in
  let blockstore = BlockMap.empty in

  let blockstore, tagstore =
    banyan_op "branch" "key" "value3" blockstore tagstore
  in
  let blockstore, tagstore =
    banyan_op "branch" "key1" "value1" blockstore tagstore
  in
  let blockstore, tagstore =
    banyan_op "branch1" "key2" "value2" blockstore tagstore
  in

  let _ = banyan_read "branch" "key1" blockstore tagstore in
  let _ = banyan_read "branch" "key1" blockstore tagstore in
  let _ = banyan_read "branch" "key" blockstore tagstore in

  let _ = test_banyan_read "branch" "key" "value3" blockstore tagstore in
  let _ = test_banyan_read "branch1" "key2" "value2" blockstore tagstore in

  print_string "\nmerging branches\n";

  let _ = merge_branches "branch" "branch1" tagstore in
  ()

(*--------------------------------------------------------------------------------------------------------------*)

(*
	let filldummy blockstore tagstore =
	let blockstore = BlockMap.add (Hash_block("value")) (Value_block (Block ("value"))) blockstore in 
	
	let item1 = BlockMap.find (Hash_block("value")) blockstore in 
	let item = match item1 with
	|Value_block x -> print_string "block matched\n"
	|_ -> print_string "not matched" in 
		
	
	let dummytree = [Content, "path", Hash_block("value")] in
	let blockstore = BlockMap.add (Hash_tree(dummytree)) (Value_tree (Tree (dummytree))) blockstore in
	
	let item = match item1 with
	|Value_block x -> print_string "block matched\n"
	|_ -> print_string "not matched" in 
	
	let item = BlockMap.find (Hash_tree(dummytree)) blockstore in 
	let item = match item with
	|Value_tree x -> print_string "tree matched\n" in
	
	let dummycommit = ([Hash_dummy], Hash_tree(dummytree)) in
	let blockstore = BlockMap.add (Hash_commit(dummycommit)) (Value_commit (Commit (dummycommit))) blockstore in
	
	let item = BlockMap.find (Hash_commit(dummycommit)) blockstore in
	let item = match item with
	|Value_commit x -> print_string "commit matched\n" in
	
	let tagstore = TagMap.add (Branch "ss") (Hash_commit(dummycommit)) tagstore in 
	
	let item = TagMap.find (Branch "ss") tagstore in
	let item = match item with 
	|Hash_commit (_, x) -> match x with 
		|Hash_tree ((_, _, y)::[]) -> match y with
			|Hash_block z -> match z with 
				|"value" -> print_string "tag commit matched\n" 
				|_ -> print_string "string didnt match" in	
	 
	(blockstore, tagstore)
	
	
	let tagstore = TagMap.add (Branch "branch") (Hash_commit([], Tree_hash(Content, "path", *)

(*let (blockstore, tagstore) = filldummy blockstore tagstore in  (*total discreat testing*)

  (match (BlockMap.is_empty blockstore) with
  | true -> print_string "blockstore is empty"
  | false -> print_string "block store is not empty\n") ;

  (match (TagMap.is_empty tagstore) with
  | true -> print_string "tagstore is empty"
  | false -> print_string "tagstore is not empty\n") ;

  let item1 = BlockMap.find (Hash_block("value")) blockstore in
  let item = (match item1 with
  |Value_block x -> print_string "block matched at end\n"
  |_ -> print_string "block not matched at end\n" ) in

  let dummytree = [Content, "path", Hash_block("value")] in
  let item = BlockMap.find (Hash_tree(dummytree)) blockstore in
  let item = (match item with
  |Value_tree x -> print_string "tree matched at end\n"
  |_ -> print_string "tree not matched at end\n" ) in

  let dummycommit = ([Hash_dummy], Hash_tree(dummytree)) in

  let item = BlockMap.find (Hash_commit(dummycommit)) blockstore in
  let item = (match item with
  |Value_commit x -> print_string "commit matched at end\n"
  |_ -> print_string "tree not matched at end\n" ) in

  let item = TagMap.find (Branch "ss") tagstore in
  let item = match item with
  |Hash_commit (_, x) -> match x with
  	|Hash_tree ((_, _, y)::[]) -> match y with
  		|Hash_block z -> match z with
  			|"value" -> print_string "tag commit matched at end\n"
  			|_ -> print_string "string didnt match at end" in

  ()
*)
