open Types
open Utils




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
    let tree_node = BlockMap.find tree_hash blockstore in 
    match tree_node with
    |Value_tree (Tree (treelist)) -> 
      let val_hash = findKeyInTree key treelist in
      let v = BlockMap.find val_hash blockstore in
        (match v with
            | Value_block (Block (value)) -> log ("read -> value found: " ^ value ^ "\n")
            | _ -> log "read -> string didnt match\n" )
    
);
  ()
