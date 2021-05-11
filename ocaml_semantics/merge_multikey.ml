open Types
open Utils

let equal_objects o1 o2 =
  true (*compares any banyan objects and check if they are equal*)

let findInTreelist key treelist =
  match treelist with
  |[] -> None 
  |(c, p, v)::t ->
    if (String.compare p key == 0)then
      Some v
    else 
      findInTreelist key t 


let check_conflict treelist1 treelist2 reserve_treelist1 blockstore finalTreeList =
  match treelist1 with
  |[] -> 
    let treelist = includeUniqeElements reserve_treelist1 treelist2 finalTreeList in
    let treehash = Hash_tree (treelist) in 
    let blockstore = BlockMap.add treehash (Value_tree (Tree treelist)) blockstore in
    treehash, blockstore

  |(c, p, v)::t ->
    let res = findInTreelist p treelist2 in
    let finalTreeList = 
      (match res with 
        |None -> (c, p, v)::finalTreeList
        |Some hsh -> 
          if (equal_objects v hsh) then
            let finalTreeList = (c, p, v)::finalTreeList in
            finalTreeList
          else
            let node1 = BlockMap.find v blockstore in
            let node2 = BlockMap.find hsh blockstore in

            let valuehash, blockstore = 
              (match node1, node2 with
              |Value_tree (Tree lst1), Value_tree(Tree lst2) -> check_conflict lst1 lst2 reserve_treelist1 blockstore []
              |Value_block (Block bhash1), Value_block (Block bhash2) -> resolve_conflict bhash1 bhash2 p lca (*insert the resolved value in the blockstore and return its hash *)
              |_ -> hsh, blockstore (*if both are not tree/value then guest branch will dominate and its hash will be inserted*)
              )in

            let contType = checkContentType valuehash in
            let finalTreeList = (contType, p, valuehash)::finalTreeList in
              finalTreeList
      ) in
      let blockstore = BlockMap.add (Hash_tree finalTreeList) (Value_tree (Tree finalTreeList)) blockstore in
      check_conflict t treelist2 reserve_treelist1 blockstore finalTreeList
            


(*algorithm for above code
let check_conflict treelist1 treelist2  = 
  match treelist1 with
  |[] -> include all unique elemetns of treelis2 in finaltreelist; return treehash of finaltreelist 
  |(c, p, v)::t -> 
    let res = findInTreelist p treelist2 in
    let finalTreeList = 
      (match res with 
        |None -> keep cpv as it is in the treelist
        |Some hsh -> 
          if (equal_objects v hsh) then
            keep cpv as it is in the treelist
          else 
            let treehash = something in
              put p with updated treehash in the treelist)
      in 
      check_conflict t treelist2 *)



let three_way_merge treelist1 treelist2 lca =
  let finaltreehash, blockstore = check_conflict treelist1 treelist2 treelist1 in
  finaltreehash, blockstore


  

 
  return treehash and commit . Only treehash can be returned because in the check conflict function, it has to be computed in recursive manner.

let merge_branches hostBranch guestBranch blockstore tagstore =
  let c1 =
    match findtag hostBranch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch1"
  in
  let c2 =
    match findtag guestBranch tagstore with
    | Some x -> x
    | None -> failwith "illegal branch2"
  in

(*check these---not returning bs and ts*)
  (*if (equal_objects c1 c2) then
    c2
  else if (List.mem c1 (parents c2)) then 
    c2
  else if (List.mem c2 (parents c1)) then 
    c1
  else*)
    let treelist1 = find_treelist c1 blockstore in 
    let treelist2 = find_treelist c2 blockstore in  

    (*do lca stuff here*)
    let lca = LCA c1 c2 in
    let lca =
      (match lca with
      |h::[] -> three_way_merge treelist1 treelist2 lca 
      |h::t -> 
        let lca = recursive_merge lca in 
        lca) in

  let treehash, blockstore = three_way_merge treelist1 treelist2 lca in
    
  let new_commit_node = ([ c2;c1 ], treehash) in 

  let blockstore =
    BlockMap.add (Hash_commit new_commit_node)
      (Value_commit (Commit new_commit_node)) blockstore
  in

  let tagstore =
  	print_string ("merging: host branch " ^ hostBranch ^ "\n");
    TagMap.add (Branch hostBranch) (Hash_commit new_commit_node) tagstore
  in

 (blockstore, tagstore)