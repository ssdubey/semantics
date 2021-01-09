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
            let v = findKeyInTree key treelist in
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
      let val_hash = findKeyInTree key treelist in
      let v = BlockMap.find val_hash blockstore in
        (match v with
            | Value_block (Block (valu)) -> 
              match (String.compare valu value) with 
              | 0 -> print_string ("\nread test passed: " ^ valu ^ "\n")
              | _ -> print_string ("\nread test failed: " ^ valu ^ "\n" ))
    
);
  

  ()
