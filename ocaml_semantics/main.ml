open Types
open Utils
(* open Write_multikey *)
open Write_stack
open Read_multikey
open Merge3
open Branch
open Write_read

let _ =
  let tagstore = TagMap.empty in
  let blockstore = BlockMap.empty in
  
  testcase blockstore tagstore

  (*let blockstore, tagstore =
    banyan_op "b1" ["a"] "1" blockstore tagstore
  in 

  let tagstore = create_branch "b2" "b1" tagstore in 

  let blockstore, tagstore =
    banyan_op "b1" ["b"] "2" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" ["b"] "3" blockstore tagstore
  in

  let blockstore, tagstore = merge_branches "b2" "b1" blockstore tagstore in 

  let blockstore, tagstore = merge_branches "b1" "b2" blockstore tagstore in 

  let blockstore, tagstore =
    banyan_op "b1" ["c"] "1" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" ["c"] "2" blockstore tagstore
  in

  let blockstore, tagstore = merge_branches "b1" "b2" blockstore tagstore in 
  
  let test1 () = 
    banyan_read "b1" ["a"] blockstore tagstore;
    banyan_read "b1" ["b"] blockstore tagstore;
    banyan_read "b1" ["c"] blockstore tagstore;
    banyan_read "b2" ["a"] blockstore tagstore;
    banyan_read "b2" ["b"] blockstore tagstore;
    banyan_read "b2" ["c"] blockstore tagstore;
  in

  test1 ()*)


  (*let blockstore, tagstore =
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
  ()*)




  (*let blockstore, tagstore =
    banyan_op "branch" "key1" "value5" blockstore tagstore
  in
  
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key1" "value5" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key1" "value5" blockstore tagstore in 
  
  let blockstore, tagstore =
    banyan_op "branch1" "key2" "value2" blockstore tagstore
  in
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch1" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch1" "key2" "value2" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key2" "value2" blockstore tagstore in 
  
  let blockstore, tagstore =
    banyan_op "branch" "key3" "value3" blockstore tagstore
  in
  print_string "\npublishing\n";
  let blockstore, tagstore = publish "branch" "replica1" blockstore tagstore in
  let _ = test_banyan_read "branch" "key3" "value3" blockstore tagstore in 
  let _ = test_banyan_read  "replica1" "key3" "value3" blockstore tagstore in 

  print_string "\ntesting refresh\n";
  let blockstore, tagstore = refresh "branch" "replica1" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key1" "value5" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key2" "value2" blockstore tagstore in 
  let _ = test_banyan_read "branch" "key3" "value3" blockstore tagstore in 

  ()*)