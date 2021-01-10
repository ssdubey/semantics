open Types
open Utils
open Write
open Read 
open Merge
open Branch

let _ =
  let tagstore = TagMap.empty in
  let blockstore = BlockMap.empty in
  
  let blockstore, tagstore =
    banyan_op "b1" "a" "1" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b1" "b" "2" blockstore tagstore
  in

  let tagstore = create_branch "b2" "b1" tagstore in 

  let blockstore, tagstore =
    banyan_op "b1" "b" "3" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b1" "c" "4" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b1" "d" "5" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" "a" "2" blockstore tagstore
  in

  let tagstore = create_branch "b3" "b2" tagstore in 

  let blockstore, tagstore =
    banyan_op "b2" "c" "3" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b2" "e" "4" blockstore tagstore
  in

  let blockstore, tagstore =
    banyan_op "b3" "c" "5" blockstore tagstore
  in

  let blockstore, tagstore = merge_branches "b1" "b2" blockstore tagstore in 

  let test1 () = 
    banyan_read "b1" "a" blockstore tagstore;
    banyan_read "b1" "b" blockstore tagstore;
    banyan_read "b1" "c" blockstore tagstore;
    banyan_read "b1" "d" blockstore tagstore;
    banyan_read "b2" "a" blockstore tagstore;
    banyan_read "b2" "b" blockstore tagstore;
    banyan_read "b2" "c" blockstore tagstore;
    banyan_read "b2" "d" blockstore tagstore;
    banyan_read "b2" "e" blockstore tagstore;
  in

  let blockstore, tagstore = merge_branches "b2" "b3" blockstore tagstore in 

  let test2 () = 
    banyan_read "b3" "a" blockstore tagstore;
    banyan_read "b3" "b" blockstore tagstore;
    banyan_read "b3" "c" blockstore tagstore;
    banyan_read "b3" "d" blockstore tagstore;
    banyan_read "b3" "e" blockstore tagstore;
  in

  test1 (); 
  test2 ()
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