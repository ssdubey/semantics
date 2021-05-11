open Types
open Utils

let rec searchList k tree_node =
  match tree_node with
  |Value_tree (Tree ((node, p, vh)::[])) -> 
    if (String.compare k p == 0) then 
      (Tree [(node, k, vh)]) 
    else 
      failwith ("read_multikey:6: key not found in the list. Check if the tree node is correct)")
  |Value_tree (Tree ((node, p, vh)::t)) -> 
    if (String.compare k p == 0) then 
      (Tree [(node, k, vh)]) 
    else 
      searchList k (Value_tree(Tree t))

(*finds the tree node from [tree_hash]. Iterates over each term of the key and checks if it is present in one of the tuples of tree node.*)
let rec findKey key tree_hash blockstore =
  let tree_node = BlockMap.find tree_hash blockstore in 
  let vh = 
    match key with 
      |h::[] -> 
        (let tnode = searchList h tree_node in (*tuple*)
        match tnode with
        |Tree ([(Content, _, vhash)]) -> vhash
        |Tree ([(Node, _, _)]) -> failwith ("read_multikey:11: key not found (provided key is subset)"))
      |h::t -> 
        (let tnode = searchList h tree_node in (*tuple*)
        match tnode with
        |Tree ([(Content, _, _)]) -> failwith ("read_multikey:15: key not found (provided key is superset")
        |Tree ([(Node, h, vhash)]) -> findKey t vhash blockstore
        |_ -> failwith ("read_multikey:17: tnode error"))
    in
      vh

let banyan_read branch key blockstore tagstore =
  let commit_hash =
    match findtag branch tagstore with
    | Some x -> x
    | None -> failwith ("invalid branch "^branch)
  in
(* check why commit node after merge is having multiple same key entries *)
  let commit_node = BlockMap.find commit_hash blockstore in 
  (match commit_node with
  |Value_commit (Commit (_, tree_hash)) -> 
    let vhash = findKey key tree_hash blockstore in 
    let v = BlockMap.find vhash blockstore in
      (match v with
          | Value_block (Block (value)) -> log ("read -> value found: " ^ value ^ "\n")
          | _ -> log "read -> read error: string didnt match\n" )
  | _ -> log "read:49 -> this error should never come") 
  

  
  
  
  
  
  
  
  
  
  