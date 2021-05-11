(* open Write_multikey *)
open Write_stack
open Read_multikey

let testcase blockstore tagstore =
    (* let blockstore, tagstore =
        banyan_op "b1" ["a";"b"] "1" blockstore tagstore
    in  *)
    let blockstore, tagstore =
        banyan_op "b1" ["a";"b";"c"] "1" blockstore tagstore
    in
    banyan_read "b1" ["a";"b";"c"] blockstore tagstore;

    let blockstore, tagstore =
        banyan_op "b1" ["a";"b";"c";"d"] "2" blockstore tagstore
    in 
    banyan_read "b1" ["a";"b";"c";"d"] blockstore tagstore;

    
    banyan_read "b1" ["a";"b";"c";"d"] blockstore tagstore;
    banyan_read "b1" ["a";"b";"c"] blockstore tagstore;
    