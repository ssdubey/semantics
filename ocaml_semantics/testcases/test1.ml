open Types
open Utils
open Write
open Read 
open Merge

let test blockstore tagstore = 
let blockstore, tagstore =
    banyan_op "b1" "key1" "value1" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b1" "key1" "value2" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" "key2" "value3" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" "key3" "value4" blockstore tagstore
  in
  
  let () =
    banyan_read "b1" "key1" blockstore tagstore;
    banyan_read "b2" "key2" blockstore tagstore;
    banyan_read "b2" "key3" blockstore tagstore;
  in

  let blockstore, tagstore = merge_branches "b1" "b2" blockstore tagstore in
  ()