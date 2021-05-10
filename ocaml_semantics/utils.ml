open Types

let log content = print_string ("log: " ^ content ^"\n")

let read_tagstore br tagstore =
  try Some (TagMap.find br tagstore) with _ -> None


let read_blockstore node_hash blockstore = 
    BlockMap.find node_hash blockstore


let get_tree_hash commit_node =
  let _, tree_hash = commit_node in
  tree_hash


let findtag branch tagstore =
  try Some (TagMap.find (Branch branch) tagstore) with _ -> None


let find_treelist commit_hash blockstore =
  (*let treelist =
    match commit with
    | Hash_commit (_, x) -> ( match x with Hash_tree treelist -> treelist )
  in
  treelist*)
  let commit = read_blockstore commit_hash blockstore in
  let tree_hash = match commit with 
                |Value_commit(Commit(_, th)) -> th in
  let tree_value = read_blockstore tree_hash blockstore in
  match tree_value with
  |Value_tree(Tree lst) -> lst 


let check_exist p redlist =
  List.exists (fun x -> String.compare x p == 0) redlist

let removeKeyFromTreeList key treelist =
  List.filter (fun (_, k, _) -> String.compare k key != 0) treelist


let rec findKeyInTree key treelist =
  match treelist with
  | [] -> Hash_block ""
  | [ (_, k, v) ] -> if String.compare k key == 0 then v else Hash_block ""
  | (_, k, v) :: t ->
      if String.compare k key == 0 then v else findKeyInTree key t


let rec find_commit_list current_commit_hash blockstore commit_list =
  let current_commit = read_blockstore current_commit_hash blockstore in
  match current_commit with 
  | Commit ([], c) -> c :: commit_list
  | Commit (h::t, c) ->         (*first commit in the parent list belongs to the branch in which the new commit node was created after merging*)
      (let commit_list = c :: commit_list in 
      find_commit_list h blockstore commit_list)
  (*| Commit (_, c) -> c :: commit_list *)  (*fix this to include multiple commits in the parent list*)

(*let match_commit commit_lst commit_arg_hash blockstore =
  let current_arg_commit = read_blockstore commit_arg_hash blockstore in
  match current_arg_commit with
  | Commit ([], c) -> check_list commit_lst current_arg_commit
  *)