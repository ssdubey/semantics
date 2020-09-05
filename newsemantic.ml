type content =
|Node
|Content

type branch =
|Branch of string

(*for keys*)
type hash = 
|Hash_block of string
|Hash_tree of ((content * string * hash) list)
|Hash_commit of ((hash list) * hash)
|Hash_dummy

(*for values*)
type commit =
|Commit of ((hash list) * hash)

type tree = 
|Tree of ((content * string * hash) list)

type block = 
|Block of string

type value =
|Value_commit of commit
|Value_tree of tree
|Value_block of block

module Tag_module = 
	struct
		type t = branch
		let compare t1 t2 = 
			match t1, t2 with
			|Branch (b1), Branch (b2) -> String.compare b1 b2
	end

module TagMap = Map.Make (Tag_module)


module Block_module = 
	struct
		type t = hash
		let rec compare t1 t2 = 
			match t1, t2 with
			|Hash_block x, Hash_block y -> String.compare x y
			|Hash_block x, Hash_tree y -> 1
			|Hash_block x, Hash_commit y -> 1
			|Hash_tree x, Hash_block y -> 1
			|Hash_tree ((a,b,Hash_block(c))::_), Hash_tree ((d,e,Hash_block(f))::_) -> String.compare c f	(*pass different values for every key*)
			|Hash_tree x, Hash_commit y -> 1
			|Hash_commit x, Hash_block y -> 1
			|Hash_commit x, Hash_tree y -> 1
			|Hash_commit (x, y), Hash_commit (a, b) -> compare y b
	end

module BlockMap = Map.Make (Block_module)


let read_tagstore br tagstore =
	try 
	Some (TagMap.find br tagstore)
	with
	_ -> None (*Commit ([Hash_dummy], Hash_dummy)*)

let read_blockstore node_hash blockstore =
	BlockMap.find node_hash blockstore


let get_tree_hash commit_node =
	let _, tree_hash = commit_node in 
	tree_hash

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
	
	(*let tagstore = TagMap.add (Branch "branch") (Hash_commit([], Tree_hash(Content, "path", *)


let banyan_add_first branch key value blockstore tagstore =
	let blob_hash = Hash_block(value) in
	let blockstore = BlockMap.add blob_hash (Value_block (Block (value))) blockstore in 
	let new_tree_node = [Content, key, blob_hash] in
	let blockstore = BlockMap.add (Hash_tree(new_tree_node)) (Value_tree (Tree (new_tree_node))) blockstore in
	let new_commit_node = ([Hash_dummy], Hash_tree(new_tree_node)) in
	let blockstore = BlockMap.add (Hash_commit(new_commit_node)) (Value_commit (Commit (new_commit_node))) blockstore in
	let tagstore = TagMap.add (Branch branch) (Hash_commit(new_commit_node)) tagstore in 
	blockstore, tagstore

let _ = 
	let tagstore = TagMap.empty in
	let blockstore = BlockMap.empty in
	
	let (blockstore, tagstore) = banyan_add "branch" "key" "value" blockstore tagstore in
	
	let item = TagMap.find (Branch "branch") tagstore in
	let item = match item with 
	|Hash_commit (_, x) -> match x with 
		|Hash_tree ((_, _, y)::[]) -> match y with
			|Hash_block z -> match z with 
				|"value" -> print_string "tag commit matched\n" 
				|_ -> print_string "string didnt match" in	
	 
	 
	()
	
	
	
	(*let (blockstore, tagstore) = filldummy blockstore tagstore in
	
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




	
	
	
	
	
	
	
	
