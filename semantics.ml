type branch =
|Branch of string

type hash = 
|Hash

(*type key =
|Key of string
*)
(*type value =
|Value of string
*)
type content =
|Node
|Content

module Tag_module = 
	struct
		type t = branch
		let compare t1 t2 = 0
	end

module TagMap = Map.Make (Tag_module)
let tagstore = TagMap.empty


module Block_module = 
	struct
		type t = hash
		let compare t1 t2 = 0
	end

module BlockMap = Map.Make (Block_module)
let blockstore = BlockMap.empty

type node =
[`Commit of ((hash list) * hash)
|`Tree of ((content * string * hash) list)
|`Block of string]


let createHash v =
	Hash 
	
let add_blob v =
	let h = createHash v in 
	let blockstore = 
		BlockMap.add h (`Block v) blockstore in 
		(h, blockstore)


let add_tree v =
	let h = createHash v in 
	let blockstore = 
		BlockMap.add h (`Tree v) blockstore in 
		(h, blockstore)


let add_commit br v =
	let h = createHash v in 
	let blockstore = 
	BlockMap.add h (`Commit v) blockstore in 
	let tagstore = TagMap.add br h tagstore in
	()


let read_tagstore br =
	TagMap.find br tagstore


let read_blockstore node_hash =
	BlockMap.find node_hash blockstore


let rec patternMatch node =
	match node with
	|`Commit (hlist, h) -> (hlist, h)
	|`Block blk -> blk
	|`Tree ((cnt, path, h)::lst) -> 
		match cnt with
		|Content -> (path, h)
		|Node -> (
				let node' = read_blockstore h in 
				patternMatch node')


let banyan_add br k v =
	let blob_hash, blockstore = add_blob v in
	let latest_commit = read_tagstore br in
	let node = read_blockstore latest_commit in
	let parentlist, tree_hash = patternMatch node in
	let tree_node = read_blockstore tree_hash in 
	let path, datahash = patternMatch tree_node in 
	let new_tree_list = (Content, path, blob_hash)::tree_node in 
	let tree_hash' = add_tree new_tree_list in
	let new_commit_node = `Commit (parentlist, tree_hash) in
	add_commit br new_commit_node
	
	
	
	
	
	
	
	
	
	
	
	
