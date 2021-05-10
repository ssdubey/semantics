open Types
open Utils

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

let rec insertBottomToPivotKeys key pivotKeyTerm prev_treehash blockstore = 
  match key with 
  |[] -> blockstore, prev_treehash
  |h::t -> 
    (let new_tree_node = [ (Node, h, prev_treehash) ] in
      if (String.compare h pivotKeyTerm == 0) then
        (blockstore, prev_treehash)  (**returning tree node is the pivot tree node, 
                                                    includes pivot key term, but not inserted in the bs *)
      else
        let blockstore =
          BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node)) blockstore
        in
        insertBottomToPivotKeys t pivotKeyTerm (Hash_tree new_tree_node) blockstore
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

let rec searchTreeList key treelist =
match treelist with
|[] -> None
|(c, p, v)::t ->
    if (String.compare p key == 0) then
        Some v
    else
        searchTreeList key t 


let rec findPivot key tree_hash blockstore =
  match key with
  |h::[] -> (tree_hash, h)
  |h::t -> 
    let tree_node = BlockMap.find tree_hash blockstore in
      match tree_node with
      |Value_tree (Tree treelist) -> 
        (let valhash = searchTreeList h treelist in (*return some tree node or none, if key not found, or content is found*)
        match valhash with 
        |None -> (tree_hash, h) (*key not found in the current tree node, then return current tree node to update*)
        |Some hsh -> findPivot t hsh blockstore) (*key is found until this level, so serach next term of key in next level*)
      |_ -> failwith ("write_multikey: 54 -> this should never happen")


let rec searchKeyInTreelist k treelist =
    match treelist with
    |[] -> None
    |(c, p, v)::[] -> if (String.compare p k == 0) then (Some (c, p, v)) else None
    |(c, p, v)::t -> if (String.compare p k == 0) then (Some (c, p, v)) else searchKeyInTreelist k t 


let rec prevToPivot key pivotKeyTerm tree_hash blockstore prev_to_Pivot =
    let treenode = BlockMap.find tree_hash blockstore in
    match treenode with
    |Value_tree(Tree treelist) -> 
        let tuple = searchKeyInTreelist (List.hd key) treelist in(*return the tuple if the key is found*)
        match tuple with 
        |None -> None 
        |Some (c, p, v) -> 
            if (String.compare p pivotKeyTerm == 0) then 
                prev_to_Pivot 
            else 
                prevToPivot (List.tl key) pivotKeyTerm v  blockstore (Some (c, p, v))


let rec searchAndReplaceTuple pivotKeyTerm nextTo_pivot_treehash treelist treelist' =
    match treelist with
    |[] -> (Node, pivotKeyTerm, nextTo_pivot_treehash)::treelist'
    |(c, h, v)::t -> 
        if(String.compare h pivotKeyTerm == 0) then
            let treelist' = ((Node, h, nextTo_pivot_treehash)::t)@treelist' in
            treelist'
        else 
            let treelist' = (c, h, v)::treelist' in
            searchAndReplaceTuple pivotKeyTerm nextTo_pivot_treehash t treelist'


let rec insertTopToPivotKeys branch key pivotKeyTerm nextTo_pivot_treehash root_tree_hash blockstore =
    (**using pivot find prev_to_pivot. In [a;b;c;d;e] if d is pivot, we are looking for c *) 
    let prev_to_pivot = prevToPivot key pivotKeyTerm root_tree_hash blockstore None in (*return the entire tuple*)
    let blockstore, treehash = 
        match prev_to_pivot with
        |Some (_, p, vh) -> (
            let treenode = BlockMap.find vh blockstore in
            match treenode with
            |Value_tree (Tree treelist) -> 
                let treelist' = searchAndReplaceTuple pivotKeyTerm nextTo_pivot_treehash treelist [] in
                
                let blockstore =
                    BlockMap.add (Hash_tree treelist') (Value_tree (Tree treelist')) blockstore
                in
                    let pivotKeyTerm = p in 
                    insertTopToPivotKeys branch key pivotKeyTerm (Hash_tree treelist') root_tree_hash blockstore
        )
        |None -> (
            let treenode = BlockMap.find root_tree_hash blockstore in
            match treenode with
            |Value_tree (Tree treelist) -> 
                let treelist' = searchAndReplaceTuple pivotKeyTerm nextTo_pivot_treehash treelist [] in
                
                let blockstore =
                    BlockMap.add (Hash_tree treelist') (Value_tree (Tree treelist')) blockstore
                in
                (blockstore, (Hash_tree treelist'))
        ) in
        (blockstore, treehash)


(*key terms must not be repeated in a single key*)
let banyan_add_new commit_hash branch key value blockstore tagstore =
  (*pivot is the first node from bottom in which conflict arises *)
  let commit_node = BlockMap.find commit_hash blockstore in
  let root_tree_hash = 
    match commit_node with
    | Value_commit (Commit (_, th)) -> th 
    | _ -> failwith "write_multikey:50 -> commit node parsing error" 
  in
    let pivotTreeHash, pivotKeyTerm = findPivot key root_tree_hash blockstore in
    (*insert from bottom until pivotKeyTerm*)
    let rev_key = List.rev key in 

    let blob_hash = Hash_block value in
    let blockstore =
      BlockMap.add blob_hash (Value_block (Block value)) blockstore
    in
    let new_tree_node = [ (Content, (List.hd rev_key), blob_hash) ] in

    if (String.compare (List.hd rev_key) pivotKeyTerm == 0) then
      failwith "resolve conflict not defined"
    else
      let blockstore =
        BlockMap.add (Hash_tree new_tree_node) (Value_tree (Tree new_tree_node))
          blockstore
      in
        let blockstore, prevTo_pivot_treehash = (**In [a;b;c;d;e] if d is pivot, treehash is of e*)
                                insertBottomToPivotKeys (List.tl rev_key) pivotKeyTerm (Hash_tree new_tree_node) blockstore in
      
        (*Search from top and insert from bottom from pivot key term* prev and next will reverse from here due to key reversal *)  
        let blockstore, treehash = insertTopToPivotKeys branch key pivotKeyTerm prevTo_pivot_treehash root_tree_hash blockstore in
        let new_commit_node = ([commit_hash], treehash) in
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