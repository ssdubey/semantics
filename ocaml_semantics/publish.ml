let publish_to_public private_branch public_branch blockstore tagstore =
	merge_branches private_branch public_branch blockstore tagstore

let publish branch replica blockstore tagstore =

	(* let public_branch = (branch ^ "_public") in *)
	let latest_commit =(findtag replica tagstore) in
	match latest_commit with
	|Some _ -> (
		let blockstore, tagstore = publish_to_public 
		branch replica blockstore tagstore in
		(blockstore, tagstore)
	)
	|None ->
		(let commit = 
			(match (findtag branch tagstore) with
			|None -> failwith "illegal branch to merge"
			|Some x -> x) in 
			let tagstore = TagMap.add (Branch replica) commit tagstore in 

      (* banyan_op "branch" "key3" "value3" blockstore tagstore;     *)
		(blockstore, tagstore)
	)