let refresh branch replica blockstore tagstore =
  let latest_commit = (findtag replica tagstore) in
  (match latest_commit with 
  |Some _ -> let blockstore, tagstore = merge_branches replica branch blockstore tagstore in blockstore, tagstore
  |None -> print_string "\nno published items\n"; blockstore, tagstore)
