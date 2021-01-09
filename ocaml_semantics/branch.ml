open Types
open Utils

let create_branch newBranch oldBranch tagstore =
  let latest_commit = findtag oldBranch tagstore in 
  let latest_commit = 
  match latest_commit with 
  |Some commit -> commit
  |None -> failwith "oldBranch not available" in
  
  let tagstore =
    TagMap.add (Branch newBranch) latest_commit tagstore
  in

  tagstore