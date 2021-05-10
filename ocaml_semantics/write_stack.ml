open Types
open Utils

let rec searchTreeList keyterm treelist =
  match treelist with
  |[] -> None 
  |(c, p, v)::t -> 
    if (String.compare keyterm p == 0) then
      Some (p, ((c, p, v)::t))
    else
      searchTreeList keyterm t

let rec fill_ap_stack key ap_stack =
  match key with
  |[] -> ap_stack
  |h::t ->
    log ("pushing "^h^" to ap_stack");
    Stack.push h ap_stack;
    fill_ap_stack (List.tl key) ap_stack

let rec fillStacks key tree_hash bp_stack ap_stack blockstore =
  match key with 
  |[] -> (bp_stack, ap_stack)
  |_ -> (
    let treenode = BlockMap.find tree_hash blockstore in
    let keyterm = List.hd key in 
    let (bp_stack, ap_stack) = (
      match treenode with
      |Value_tree(Tree treelist) -> 
        let tuple = searchTreeList keyterm treelist in
        match tuple with
        |Some (p, ((c, k, v)::t)) -> 
          log ("pushing "^p^" to bp_stack");
          Stack.push (p, ((c, k, v)::t)) bp_stack;
          fillStacks (List.tl key) v bp_stack ap_stack blockstore
          (*readTreeHash (List.tl key) v blockstore*)
        |None -> 
          let ap_stack = fill_ap_stack key ap_stack in
          (bp_stack, ap_stack)
    ) in
    (bp_stack, ap_stack)
  )
  
let rec create_fill_ap_treenode ap_stack treehash blockstore =
  if (Stack.is_empty ap_stack) then
    let () = log "create_fill_ap_treenode: stack empty" in
    (treehash, blockstore)
  else 
    let () = log "create_fill_ap_treenode: stack has values" in
    let k = Stack.pop ap_stack in
    log ("creating tree node for " ^ k);
    let treenode = [(Node, k , treehash)] in
    let treehash = (Hash_tree(treenode)) in
    let blockstore =
      BlockMap.add treehash (Value_tree (Tree treenode)) blockstore
    in
    create_fill_ap_treenode ap_stack treehash blockstore

let rec search_replace k lst treehash new_treelist =
  match lst with
  |[] -> new_treelist
  |(c, p, v)::t -> 
    if(String.compare p k == 0) then
      let new_treelist = ((Node, p, treehash)::t)@new_treelist in
      new_treelist
    else
      let new_treelist = (c, p, v)::new_treelist in
      search_replace k t treehash new_treelist


let rec create_fill_bp_treenode bp_stack treehash blockstore =
  if (Stack.is_empty bp_stack) then
    let () = log "create_fill_bp_treenode: stack empty" in
    (treehash, blockstore)
  else
    let tuplelist = Stack.pop bp_stack in
    match tuplelist with
    |(p, lst) -> 
      let new_treenode = search_replace p lst treehash [] in
      log ("create_fill_bp_treenode: creating tree node for " ^ p);
      let treehash = Hash_tree new_treenode in
      let blockstore =
        BlockMap.add treehash (Value_tree (Tree new_treenode)) blockstore
      in
      create_fill_bp_treenode bp_stack treehash blockstore

let create_fill_ap_bp_treenode ap_stack bp_stack value blockstore =
  let blob_hash = Hash_block value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in
  let k = Stack.pop ap_stack in
  log ("creating tree node for "^k);
  let treenode = [(Content, k, blob_hash)] in
  let treehash = Hash_tree treenode in
  let blockstore =
    BlockMap.add treehash (Value_tree (Tree treenode)) blockstore
  in
  let (treehash, blockstore) = create_fill_ap_treenode ap_stack treehash blockstore in (*the returned treehash will go as argument to prev key term*)
  let (treehash, blockstore) = create_fill_bp_treenode bp_stack treehash blockstore in
  (treehash, blockstore)



let rec search_key_replace_tuple p lst newtuple newtreelist =
match lst with
|(c, k, v)::t -> 
  if (String.compare p k == 0) then
    let newtreelist = ((newtuple::t)@newtreelist) in
    newtreelist
  else
    let newtreelist = (c, k, v)::newtreelist in
    search_key_replace_tuple p lst newtuple newtreelist


let rec create_fill_only_bp_treenode bp_stack treehash blockstore =
  if (Stack.is_empty bp_stack) then
    (treehash, blockstore)
  else
    let tuplelist = Stack.pop bp_stack in
    match tuplelist with
    |(p, lst) -> 
      let newtuple = (Node, p, treehash) in
      let newtreelist = search_key_replace_tuple p lst newtuple [] in
      let treehash = Hash_tree( newtreelist) in
      let blockstore =
              BlockMap.add treehash (Value_tree (Tree newtreelist))
              blockstore
      in
      create_fill_only_bp_treenode bp_stack treehash blockstore


let rec create_fill_only_ap_treenode ap_stack treehash blockstore =
  if (Stack.is_empty ap_stack) then
    (treehash, blockstore)
  else
    let p = Stack.pop ap_stack in
    let newtreelist = [(Node, p, treehash)] in
    let treehash = Hash_tree( newtreelist) in
    let blockstore =
            BlockMap.add treehash (Value_tree (Tree newtreelist))
            blockstore
    in
    create_fill_only_ap_treenode ap_stack treehash blockstore



let banyan_add_new commit_hash branch key value blockstore tagstore =
  let bp_stack = Stack.create () in
  let ap_stack = Stack.create () in
  
  let commit_node = BlockMap.find commit_hash blockstore in
  let root_tree_hash = 
    match commit_node with
    | Value_commit (Commit (_, th)) -> th 
    | _ -> failwith "write_multikey:50 -> commit node parsing error" 
  in
  
  let bp_stack, ap_stack = fillStacks key root_tree_hash bp_stack ap_stack blockstore in

  if (Stack.is_empty ap_stack) then
    let blob_hash = Hash_block value in
    let blockstore =
      BlockMap.add blob_hash (Value_block (Block value)) blockstore
    in
    
    let tuplelist = Stack.pop bp_stack in
    match tuplelist with
    |(p, lst) -> 
      let newtuple = (Content, p, blob_hash) in
      let newtreelist = search_key_replace_tuple p lst newtuple [] in
      let treehash = Hash_tree( newtreelist) in
      let blockstore =
            BlockMap.add treehash (Value_tree (Tree newtreelist))
            blockstore
      in
      let (treehash, blockstore) = create_fill_only_bp_treenode bp_stack treehash blockstore in
      
      let new_commit_node = ([commit_hash], treehash) in
      let blockstore =
          BlockMap.add (Hash_commit new_commit_node)
              (Value_commit (Commit new_commit_node)) blockstore
      in
      let tagstore =
          TagMap.add (Branch branch) (Hash_commit new_commit_node) tagstore
      in
      (blockstore, tagstore)
  
  else if (Stack.is_empty bp_stack) then
    (*insert all independently and add the final one to root *)
    let blob_hash = Hash_block value in
    let blockstore =
      BlockMap.add blob_hash (Value_block (Block value)) blockstore
    in
    let p = Stack.pop ap_stack in
    let newtreelist = [(Content, p, blob_hash)] in
      let treehash = Hash_tree( newtreelist) in
      let blockstore =
              BlockMap.add treehash (Value_tree (Tree newtreelist))
              blockstore
      in

    let (treehash, blockstore) = create_fill_only_ap_treenode ap_stack treehash blockstore in

    let new_commit_node = ([commit_hash], treehash) in
      let blockstore =
          BlockMap.add (Hash_commit new_commit_node)
              (Value_commit (Commit new_commit_node)) blockstore
      in
      let tagstore =
          TagMap.add (Branch branch) (Hash_commit new_commit_node) tagstore
      in
      (blockstore, tagstore)
  
  else
    let () = log "both bp and ap stacks are not null" in
    let (treehash, blockstore) = create_fill_ap_bp_treenode ap_stack bp_stack value blockstore in

    let new_commit_node = ([commit_hash], treehash) in
    let blockstore =
        BlockMap.add (Hash_commit new_commit_node)
            (Value_commit (Commit new_commit_node)) blockstore
    in
    let tagstore =
        TagMap.add (Branch branch) (Hash_commit new_commit_node) tagstore
    in
    (blockstore, tagstore)

let rec insertKeys key blockstore prev_hash =
  match key with
  | [] -> (prev_hash, blockstore)
  | h::t -> 
     (let new_tree_node = [ (Node, h, prev_hash) ] in
        let blockstore =
            BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
            blockstore
        in
          insertKeys t blockstore (Hash_tree new_tree_node)
    )


let banyan_add_first branch key value blockstore tagstore =
  
  let hd_key = List.hd key in
  let key = List.tl key in

  let blob_hash = Hash_block value in
  let blockstore =
    BlockMap.add blob_hash (Value_block (Block value)) blockstore
  in
  let new_tree_node = [ (Content, hd_key, blob_hash) ] in
  let blockstore =
    BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
      blockstore
  in
    let (th, blockstore) = insertKeys key blockstore (Hash_tree new_tree_node) in
    let new_commit_node = ([], th) in
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
        let key = List.rev key in
        banyan_add_first branch key value blockstore tagstore
  in
  (blockstore, tagstore)


let banyan_op branch key value blockstore tagstore =
  let blockstore, tagstore = banyan_add branch key value blockstore tagstore in
  (blockstore, tagstore)