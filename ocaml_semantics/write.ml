open Types
open Utils

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
  let new_commit_node = ([], Hash_tree new_tree_node) in
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

  let filteredTreeNode = removeKeyFromTreeList key tree_node in

  let blob_hash = Hash_block value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in

  let new_tree_node = (Content, key, blob_hash) in
  let tree_node' = new_tree_node :: filteredTreeNode in
  let blockstore =
    BlockMap.add (Hash_tree tree_node') (Value_tree (Tree tree_node'))
      blockstore
  in

  let new_commit_node = ([commit_hash], Hash_tree tree_node') in
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
        log "write -> not a first entry in this branch\n ";
        banyan_add_new commit_hash branch key value blockstore tagstore
    | None ->
        log "write -> first entry in this branch\n ";
        banyan_add_first branch key value blockstore tagstore
  in
  (blockstore, tagstore)


let banyan_op branch key value blockstore tagstore =
  let blockstore, tagstore = banyan_add branch key value blockstore tagstore in
  (blockstore, tagstore)
