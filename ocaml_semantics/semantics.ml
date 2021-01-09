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

  let compare t1 t2 = compare t1 t2
   (*) match (t1, t2) with
    | Hash_block x, Hash_block y -> print_string "9 ";String.compare x y
    | Hash_block x, Hash_tree y -> print_string "1 ";1
    | Hash_block x, Hash_commit y -> print_string "2 ";1
    | Hash_tree x, Hash_block y -> print_string "8 ";1
    | ( Hash_tree ((a, b, Hash_block c) :: _),
        Hash_tree ((d, e, Hash_block f) :: _) ) ->
        print_string "3 -> comparig c and f: "; print_string (c ^ f ^ " "); String.compare c f (*pass different values for every key*)
    | Hash_tree x, Hash_commit y -> print_string "4 ";1
    | Hash_commit x, Hash_block y -> print_string "5 ";1
    | Hash_commit x, Hash_tree y -> print_string "6 ";1
    | Hash_commit (x, y), Hash_commit (a, b) -> print_string "7 ";compare y b*)
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

let banyan_add_new commit_hash branch key value blockstore tagstore = print_string "1";
  let commit_node = match commit_hash with Hash_commit node -> node in print_string "2";
  (*node is equivalent to new_commit_node in Hash_commit(new_commit_node))*)
  let _, tree_hash = commit_node in print_string "3";
  (*tree hash is equivalent to Hash_tree(new_tree_node)*)
  let tree_node_value = BlockMap.find tree_hash blockstore in print_string "4"; (*problem here*)
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
  let commit_hash =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith ("illegal branch "^branch)
  in

  let commit_node = BlockMap.find commit_hash blockstore in 
  (match commit_node with
  |Value_commit (Commit (_, tree_hash)) -> 
    let tree_node = BlockMap.find tree_hash blockstore in 
    match tree_node with
    |Value_tree (Tree (treelist)) -> 
      let val_hash = find_tree_node key treelist in
      let v = BlockMap.find val_hash blockstore in
        (match v with
            | Value_block (Block (value)) -> print_string ("value found: " ^ value ^ "\n")
            | _ -> print_string "string didnt match\n" )
    
);
  (*let _ =
    match commit_hash with
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
*)
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
  let commit_hash =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch"
  in
  let commit_node = BlockMap.find commit_hash blockstore in 
  (match commit_node with
  |Value_commit (Commit (_, tree_hash)) -> 
    let tree_node = BlockMap.find tree_hash blockstore in 
    match tree_node with
    |Value_tree (Tree (treelist)) -> 
      let val_hash = find_tree_node key treelist in
      let v = BlockMap.find val_hash blockstore in
        (match v with
            | Value_block (Block (valu)) -> 
              match (String.compare valu value) with 
              | 0 -> print_string ("\nread test passed: " ^ valu ^ "\n")
              | _ -> print_string ("\nread test failed: " ^ valu ^ "\n" ))
    
);
  

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
            (* print_string ("in merge " ^ v1 ^ "\n"); *)
            (c, p, Hash_block v1) :: new_tree_list
        | Hash_block x ->
            (* print_string ("\nin merge " ^ v1 ^ "\n"); *)
            if String.compare v1 x == 0 then
              let red_list = p :: red_list in
              (c, p, Hash_block v1) :: new_tree_list
            else
              let conflict_string = v1 ^ "_" ^ x in
              print_string ("\nin merge " ^ p ^ " " ^ conflict_string ^ "\n");
              let red_list = p :: red_list in
              (c, p, Hash_block conflict_string) :: new_tree_list
      in

      merge_trees t treelist2 new_tree_list red_list

let rec find_commit_list current_commit_hash blockstore commit_list =
  let current_commit = read_blockstore current_commit_hash blockstore in
  match current_commit with 
  | Commit ([], c) -> c :: commit_list
  | Commit (h::[], c) -> 
      (let commit_list = c :: commit_list in 
      find_commit_list h blockstore commit_list)
  | Commit (_, c) -> c :: commit_list   (*fix this to include multiple commits in the parent list*)

let match_commit commit_lst commit_arg_hash =
  let current_arg_commit = read_blockstore commit_arg_hash blockstore in
  match current_arg_commit with
  | Commit ([], c) -> check_list commit_lst current_arg_commit
  



(*storing the list of commits from latest to root of one of the branches and 
then matching that list with the commits of second branch from latest to root. 
First match is returned as LCA*)
let find_lca c1 c2 blockstore tagstore =
  let commit_lst1 = find_commit_list c1 blockstore [] in
  let lca = match_commit commit_lst1 c2  

let merge_branches branch1 branch2 blockstore tagstore =
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

  (*finding LCA of the two branches*)
  let lca = find_lca c1 c2 blockstore tagstore in
  
  let treelist1 = find_treelist c1 in
  let treelist2 = find_treelist c2 in

  let new_tree_node = merge_trees treelist1 treelist2 [] [] in
  
  let blockstore =
    BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
      blockstore
  in

  let new_commit_node = ([ Hash_dummy ], Hash_tree new_tree_node) in
  (*parent is still dummy, because we are fillingin only types, not values: (hash list * hash) list * hash*)
  let blockstore =
    BlockMap.add (Hash_commit new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in

  let tagstore =
  	print_string ("merging: host branch " ^ branch2 ^ "\n");
    TagMap.add (Branch branch2) (Hash_commit new_commit_node) tagstore
  in

 (blockstore, tagstore)


let banyan_op branch key value blockstore tagstore =
  let blockstore, tagstore = banyan_add branch key value blockstore tagstore in
  (blockstore, tagstore)

let publish_to_public private_branch public_branch blockstore tagstore =
	merge_branches private_branch public_branch blockstore tagstore

let publish branch replica blockstore tagstore =

	(* let public_branch = (branch ^ "_public") in *)
	let latest_commit =(findtag replica tagstore) in
	match latest_commit with
	|Some _ -> (
		let blockstore, tagstore = publish_to_public 
		branch replica blockstore tagstore in
		(blockstore, tagstore)
	)
	|None ->
		(let commit = 
			(match (findtag branch tagstore) with
			|None -> failwith "illegal branch to merge"
			|Some x -> x) in 
			let tagstore = TagMap.add (Branch replica) commit tagstore in 

      (* banyan_op "branch" "key3" "value3" blockstore tagstore;     *)
		(blockstore, tagstore)
	)

let refresh branch replica blockstore tagstore =
  let latest_commit = (findtag replica tagstore) in
  (match latest_commit with 
  |Some _ -> let blockstore, tagstore = merge_branches replica branch blockstore tagstore in blockstore, tagstore
  |None -> print_string "\nno published items\n"; blockstore, tagstore)

let _ =
  let tagstore = TagMap.empty in
  let blockstore = BlockMap.empty in
  
  let blockstore, tagstore =
    banyan_op "branch" "key1" "value1" blockstore tagstore
  in
  let blockstore, tagstore =
    banyan_op "branch" "key1" "value5" blockstore tagstore
  in
  
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key1" "value5" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key1" "value5" blockstore tagstore in 
  
  let blockstore, tagstore =
    banyan_op "branch1" "key2" "value2" blockstore tagstore
  in
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch1" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch1" "key2" "value2" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key2" "value2" blockstore tagstore in 
  
  let blockstore, tagstore =
    banyan_op "branch" "key3" "value3" blockstore tagstore
  in
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key3" "value3" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key3" "value3" blockstore tagstore in 

  print_string "\ntesting refresh\n";
  let blockstore, tagstore = refresh "branch" "replica1" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key1" "value5" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key2" "value2" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key3" "value3" blockstore tagstore in 

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

