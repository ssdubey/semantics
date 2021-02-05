Require Import Frap.

Set Implicit Arguments.

(*Basic skeleton of the semantics is ready. It was done with commit type as hash instead of list hash * hash, due to type related issues
It is fixed now, as shown below but semantics are not modified accordingly. Start from modifying the hash type below. One small 
theorem is designed to test it. It works fine, but it has to enhanced to check the content of the blockstore and tagstore after addition.
*)

Inductive content := 
|Node
|Content.

Inductive branch := 
|Branch (n : string).

Inductive hash :=
|Hash_block (b : string)
|Hash_tree (t: list(content * string * hash))
|Hash_commit (c: (list hash * hash))
|Dummy_hash.

Definition commit :Set := (list hash) * hash.
Definition tree := list(content * string * hash).
Definition block := string.

Definition compare_block x y :=
match (x =? y) with
|true => True
|false => False
end.

Fixpoint compare_tree_list (t1 t2 : tree) := 
match (t1, t2) with
|([],[]) => True
|((c1, key1, value1)::lst1, (c2, key2, value2)::lst2) => (
        let v1 := if (key1 =? key2) then 
                    (match (value1, value2) with
                    |(Hash_block v1, Hash_block v2) => compare_block v1 v2
                    |_ => False
                    end)
                  else
                    False
        in
        v1 /\ compare_tree_list lst1 lst2)
|_ => False     (*fix this: add condition for (node, key, value) also*)
end.

Inductive value :=
|Value_commit (c: commit) (*commit is hash, so hash to be defined first*)
|Value_tree (t: tree)
|Value_block (b: block)
|Dummy_value.

Definition dummy_commit:commit := ([Dummy_hash], Dummy_hash).
Definition dummy_tree:tree := [(Content, "dummy", Dummy_hash)].

Definition tagstore := fmap branch hash.  (*branch : string -> hash_block (c: commit)*)

Definition blockstore := fmap hash value.   (*hash_block (data:string) -> Value_block(data:string)*)

Definition create_block_hash (b: block) : hash := Hash_block b.
Definition create_tree_hash (t: tree) : hash := Hash_tree t.
Definition create_commit_hash (c: (list hash * hash)) : hash := Hash_commit c.
(*Definition create_commit_hash (c: hash) : hash := Hash_commit c.*)

Inductive cmd :=
|Seq : cmd -> cmd -> cmd
|add_block : value -> cmd
|Assign : var -> value -> cmd
|Assign_bs : hash -> value -> cmd
|Assign_ts : branch -> hash -> cmd
|Read_ts : branch -> tagstore -> cmd
|Skip: cmd.

Definition returnvalue : Type := (blockstore * tagstore).

Delimit Scope cmd_scope with cmd.
Infix ";;" := Seq (at level 80) : cmd_scope.

Definition banyan_add (br: branch) (k: string) (v: string) :=
(*Seq (Assign_bs (create_block_hash v) (Value_block v)) (Assign_bs (create_block_hash v) (Value_block v)).
*)
  (let h := create_block_hash v in
  Assign_bs h (Value_block v) ;;

  let t := (Content, k, h)::[] in
  let treehash := create_tree_hash t in
  Assign_bs treehash (Value_tree t);;

  let c := ([], treehash) in 
  let commithash := create_commit_hash c in 
  Assign_bs commithash (Value_commit c);;
  
  Assign_ts br commithash
  (*Assign_ts br h*)

  )%cmd.


(*as of now it is doing main operations*)
Inductive cmd_step : cmd * blockstore * tagstore -> cmd * blockstore * tagstore -> Prop :=
|Assign_bs_Step : forall blockhash blockvalue bs ts,
  cmd_step (Assign_bs blockhash blockvalue, bs, ts) (Skip, (bs $+ (blockhash, blockvalue)), ts)
|Assign_ts_Step : forall br h bs ts,
  cmd_step ((Assign_ts br h), bs, ts) (Skip, bs, (ts $+ (br, h))).
(*|Cmd_Skip : forall bs ts,
  cmd_step (Skip, bs, ts) (Skip, bs, ts).*)
(*|Read_ts_Step: 
  cmd_step (Read_ts *)

(*as of now it is resolving the operations to perform main operations in cmd_step*)
Inductive basic_step : (cmd * blockstore * tagstore * cmd) -> (cmd * blockstore * tagstore * cmd) -> Prop :=
|SeqStep : forall c1 c2 k bs ts,
  basic_step (Seq c1 c2, bs, ts, k) (c1, bs, ts, (Seq c2 k))
|SeqSolve : forall c1 bs ts c1' bs' ts' k,
  cmd_step (c1, bs, ts) (c1', bs', ts') ->
  basic_step (c1, bs, ts, k) (c1', bs', ts', k)
|SeqStep2 : forall bs ts c k,
  basic_step (Skip, bs, ts, (Seq c k)) (c, bs, ts, k).
(*|FinalStep : forall bs ts,
  basic_step (Skip, bs, ts, Skip) (Skip, bs, ts, Skip).*)


(*writing basic_step (...) means it will take one step and whatever is the output, it will be assigned to st.
*)
(*adding first item to db*)
Example ex1: exists st, basic_step^* ((banyan_add (Branch "branch") "key" "value"), $0, $0, Skip) st.
Proof.
eexists.
propositional.
unfold banyan_add.

eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

econstructor.

Qed.


Definition searchKey (k: string) value_tree :=  
match value_tree with
| Value_tree t => 
  match t with
  | [] => create_block_hash ""
  | [(_, key, h)] => if (k =? key) then h else create_block_hash ""
  | _ => create_block_hash ""
  end
| _ => create_block_hash ""
end.
  

Definition getSecondInCommit vc :=
match vc with
|Value_commit x => 
  match x with
  |(_, c) => c
  end
|_ => Dummy_hash
end.

Definition resolve_opt_hash opt_hash :=
match opt_hash with 
| Some x => x
| None => Dummy_hash
end.

Definition resolve_opt_commit opt_val :=
match opt_val with
|Some x => x
|None => Value_commit dummy_commit
end.

Definition resolve_opt_tree opt_val :=
match opt_val with
|Some x => x
|None => Value_tree dummy_tree
end.

Definition read_ts (br: branch) (ts: tagstore) :=
match (ts $? br) with
|Some x => x
|None => Dummy_hash
end.

Definition read_bs (hashArg: hash) (bs: blockstore) :=
match (bs $? hashArg) with
|Some x => x
|None => Dummy_value
end.

Definition read_bs_tree (hashArg : hash) (bs: blockstore) :=   (*this is redundant and created only for debugging
                                                              read_bs should serve its purpose*)
match (bs $? hashArg) with
|Some (Value_tree x) => (Value_tree x)
|Some _ => Dummy_value
|None => Dummy_value
end.

Definition read_store_helper (st: cmd * blockstore * tagstore * cmd)  br (key: string) (v:block) :=
match st with
|(_, bs, ts, _) =>
  let latestCommitHash := resolve_opt_hash (ts $? br) in
  let value_commit :=  resolve_opt_commit (bs $? latestCommitHash) in
  let treeHash := getSecondInCommit value_commit in
  let value_tree := resolve_opt_tree (bs $? treeHash) in
  let blockHash := searchKey key value_tree in  
  let value_block := (bs $? blockHash) in
  
  match value_block with
  | Some x => 
    match x with
    | Value_block v => true
    | _ => false
    end
  | _ => false
  end

end.

(*adding and reading the first item in the database*)
Example ex2: exists st, (basic_step^* ((banyan_add (Branch "branch") "key" "value"), $0, $0, Skip) st) /\ 
                                                          ((read_store_helper st (Branch "branch") "key" "value") = true).
Proof.
eexists.
propositional.
unfold banyan_add.

eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_block_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_tree_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_tree_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_tree_hash.
eapply Assign_ts_Step.

econstructor.

unfold read_store_helper.
unfold read_ts.
simplify.
unfold create_block_hash.
simplify.
equality.
Qed.

(*adding second consecutive item in the database*)
Definition banyan_add2 (br1: branch) (k1: string) (v1: string) (br2: branch) (k2: string) (v2: string):=
(let h := create_block_hash v1 in
  Assign_bs h (Value_block v1) ;;

  let t := (Content, k1, h)::[] in
  let treehash := create_tree_hash t in
  Assign_bs treehash (Value_tree t);;

  let c := ([], treehash) in 
  let commithash := create_commit_hash c in 
  Assign_bs commithash (Value_commit c);;
  
  Assign_ts br1 commithash;;
  


  let h2 := create_block_hash v2 in
  Assign_bs h2 (Value_block v2) ;;

  let t2 := (Content, k2, h2)::t in
  let treehash2 := create_tree_hash t2 in
  Assign_bs treehash2 (Value_tree t2);;

  let c2 := ([commithash], treehash2) in      (*commithash ensures that branch2 is branched from branch1*)
  let commithash2 := create_commit_hash c2 in 
  Assign_bs commithash2 (Value_commit c2);;
  
  Assign_ts br2 commithash2

  )%cmd.



Example ex3: exists st, basic_step^* ((banyan_add2 (Branch "branch1") "key1" "value1" (Branch "branch1") "key2" "value2"), 
            $0, $0, Skip) st.
Proof.
eexists.
propositional.
unfold banyan_add2.

eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_block_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_tree_hash.
unfold create_block_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_tree_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_tree_hash.
eapply Assign_ts_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_block_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_tree_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_block_hash.
unfold create_tree_hash.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
unfold create_commit_hash.
unfold create_tree_hash.
unfold create_block_hash.
eapply Assign_ts_Step.

debug eauto.
Qed.

 
Definition merge_branches (store: cmd * blockstore * tagstore * cmd) (br1 : branch) (br2 : branch) :=
match store with
|(_, bs, ts, _) => 
  (let c1 := read_ts br1 ts in
  let c2 := read_ts br2 ts in

  let val_t1 := read_bs_tree c1 bs in
  let val_t2 := read_bs_tree c2 bs in

  let t1 := (match val_t1 with 
  |Value_tree t1 => t1             (*(let treehash3 := create_tree_hash t1 in Assign_bs treehash3 (Value_tree t1))*)
  |_=> []                          (*Assign_bs Dummy_hash Dummy_value*)
  end) in
  
  let t2 := (match val_t2 with
  | Value_tree t2 => t2
  | _ => []
  end) in

  let mergedTree := t1 ++ t2 in (*(Content, "mergeKey", Dummy_hash) :: t1 in merge the lists t1 and t2 here*)
  let treehash3 := create_tree_hash mergedTree in
  Assign_bs treehash3 (Value_tree mergedTree);;

  let c3 := ([], treehash3) in 
  let commithash3 := create_commit_hash c3 in 
  Assign_bs commithash3 (Value_commit c3);;
  
  Assign_ts br1 commithash3
)%cmd
end.


Example ex4: exists st, basic_step^* ((banyan_add2 (Branch "branch1") "key1" "value1" (Branch "branch2") "key2" "value2"), 
            $0, $0, Skip) st /\ 
            (exists st2, basic_step^* (merge_branches st (Branch "branch1") (Branch "branch2"), $0, $0, Skip) st2).
Proof.
eexists.
propositional.
unfold banyan_add2.

eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

econstructor.

unfold merge_branches.

econstructor.
econstructor.

Qed.

(*-----------lca------------*)

Definition queue_commit := list hash.

Definition empty_queue_commit : queue_commit := nil.

Fixpoint reverse_aux (lst:list hash) acc :=
match lst with
|[] => acc
|(x::xs) => reverse_aux xs (x::acc)
end.

Definition reverse lst := reverse_aux lst [].

Definition push (q: queue_commit) x :=
reverse (x :: (reverse q)).

Definition pop (q: queue_commit) :=
match q with 
|[] => None
|x::xs => Some (x, xs)
end.

Definition queue_pair := list (nat * hash).
Definition empty_queue_pair : queue_pair := nil.
Fixpoint reverse_aux2 (lst:list (nat *hash)) acc :=
match lst with
|[] => acc
|(x::xs) => reverse_aux2 xs (x::acc)
end.

Definition reverse_pair_list lst := reverse_aux2 lst [].

Definition push_pair (q: queue_pair) d x :=
reverse_pair_list ((d, x) :: (reverse_pair_list q)).

Definition pop_pair (q: queue_pair) :=
match q with 
|[] => None
|x::xs => Some (x, xs)
end.

Inductive seen :=
|Seen1
|Seen2
|LCA
|SeenBoth.

Definition set := list hash.
Definition empty_set : set := nil.
Definition set_add (a:hash) (x:set) : set := a::x.

(*Definition marks := fmap hash var.   (*commit -> seen (String)*)
Definition parents := fmap hash hash.  (*commit -> parent commit*)
Definition layers := fmap nat hash. (*depth -> commit*)
Definition complet:bool := false.
*)

Record state := create_empty_state {marks:fmap hash seen; c1: hash; c2: hash; parents: fmap hash (list hash); 
layers: fmap nat hash; complete: bool; depth: nat; lca_mark: list hash}.

Definition add_parents t c p := 
let p := parents t $+ (c, p) in 
create_empty_state (marks t) (c1 t) (c2 t) p (layers t) (complete t) (depth t) (lca_mark t).

Definition get_parent t c := parents t $? c.

Definition add_to_layer t d c:= 
let l := layers t $+ (d, c) in 
create_empty_state (marks t) (c1 t) (c2 t) (parents t) l (complete t) (depth t) (lca_mark t).

Definition get_layer t d := 
match (layers t $? d) with
| Some h => set_add h empty_set
| None => empty_set
end.

Definition get_mark t elt := marks t $? elt.

Definition set_mark t mark elt := 
let m := marks t $+ (elt, mark) in 
let cond := 
match mark with
|LCA => true
|_ => false
end in
if cond then 
let lca_m := elt :: (lca_mark t) in
create_empty_state m (c1 t) (c2 t) (parents t) (layers t) (complete t) (depth t) lca_m
else
create_empty_state m (c1 t) (c2 t) (parents t) (layers t) (complete t) (depth t) (lca_mark t).

Definition check_complete (s:state) := complete s = true.

Definition set_complete t b :=
create_empty_state (marks t) (c1 t) (c2 t) (parents t) (layers t) b (depth t) (lca_mark t).

Definition set_depth t d := 
create_empty_state (marks t) (c1 t) (c2 t) (parents t) (layers t) (complete t) (d+1) (lca_mark t).

Definition both_seen t c := 
match get_mark t c with
|None |Some Seen1 |Some Seen2 => false
|_ => true
end.

Definition check_all_both_seen (layer: set) := (*include t in the argument*)
match layer with
|[] => false
|x :: xs => true (*modify this to check if all items are true*)
end.

Definition check_not_eq (d:nat) (e: nat) := 
if (Nat.eqb d e) then false else true.

Fixpoint push_in_queue todo commits :=
match commits with
|[] => todo
|h::t => (
        let todo := push todo h in 
        push_in_queue todo t)
end.

Fixpoint compare_hash_list n (a: list hash) (b: list hash) ans :=
match n with
|S n =>(
  let ans := (
    match (a, b) with
    |([], []) => True
    |((Hash_block x)::lst1, (Hash_block y)::lst2) => (compare_block x y) /\ compare_hash_list n lst1 lst2 ans
    |((Hash_tree t1)::lst1, (Hash_tree t2)::lst2) => (compare_tree_list t1 t2) /\ compare_hash_list n lst1 lst2 ans
    |((Hash_commit c1)::lst1, (Hash_commit c2):: lst2) => (
         let compare_commit := (fix compare_commit (c1 c2:commit) :=
            let (parentsList1, treehash1) := c1 in
            let (parentsList2, treehash2) := c2 in
            let res1 := compare_hash_list n parentsList1 parentsList2 ans in
            let res2 := compare_hash_list n (treehash1::[]) (treehash2::[]) ans in
            res1 /\ res2 ) in  

          (compare_commit c1 c2) /\ compare_hash_list n lst1 lst2 ans)
    
    |_ => False
  end) in ans)
| 0 => ans
end.

(*
Definition compare_list (a: list hash) (b: list hash) :=
match (a=b) with
|True => true
end.

Definition compare_tree (t1:hash) (t2:hash) :=
match (t1 = t2) with
|True => true
end.
*)

(*Definition equal_keys (commit1:hash) (commit2:hash) := 
match (commit1, commit2) with
|(Hash_commit (xlst, x), Hash_commit (ylst, y)) => 
  let lst_comp := match (xlst, ylst) with
  |([],[]) => true
  |(a,b) => compare_list a b
  end
  in
  let tree_comp := compare_tree x y in
  match (lst_comp, tree_comp) with
  |(true, true) => true
  |_ => false
  end  (*fix this: verify the comparision to hashes here*)
|_ => false
end.*)

Definition equal_keys (commit1:hash) (commit2:hash) :=
let ans := compare_hash_list 100 (commit1::[]) (commit2::[]) False in
match ans with 
|True => true
end.

Definition check_shared mark :=
match mark with 
|SeenBoth => true
|LCA => true
|_ => false
end.

Definition update_mark t mark commit :=
let mark1 := get_mark t commit in
let new_mark :=
match (mark, mark1) with 
|(Seen1, Some Seen1) | (Seen1, None) => Seen1
|(Seen2, Some Seen2) | (Seen2, None) => Seen2
|(SeenBoth, Some LCA) => SeenBoth
|(SeenBoth, _) => SeenBoth
|(Seen1, Some Seen2) | (Seen2, Some Seen1) => LCA 
|(_, Some LCA) => LCA
|_ => SeenBoth
end 
in 
let is_init := equal_keys commit (c1 t) || equal_keys commit (c2 t) in
let is_shared := check_shared new_mark in 
let t := (if (is_shared && is_init) then set_complete t true else t) in
let t := set_mark t new_mark commit in
(t, new_mark).

(*Definition aux1 (_:empty_state) (_:hash) (todo:list hash) := todo.*)

Definition aux1 t a todo :=
match (get_parent t a) with
|Some x => (push_in_queue todo x)
|None => todo
end.

Definition aux2 mark :=
match mark with 
|LCA => SeenBoth
|_ => mark
end.

Fixpoint loop todo t mark (next:list hash) {struct todo}:=
match todo with
|[] => (t, next, mark)
|a::xs =>(
  let old_mark := get_mark t a in 
  let (t, mark) := update_mark t mark a in 
  let next :=
    match old_mark with
    |Some (SeenBoth | LCA) => next
    |Some m => (match m with |mark => next end)
    |_ => let nextround := aux1 t a next in nextround
    end
  in
  let m := aux2 mark in
  loop xs t m next
)
end.

Check loop.

Fixpoint loophelper n todo t mark {struct n}:=
match n with
|S n =>(
  let '(t, next, mark') := loop todo t mark [] in 
  match next with
  |[] => t (*(t, next, mark')*)
  |h::hx => (
      let '(t, next, mark) := loop next t mark' [] in
      match next with 
      |[] => loophelper n next t mark
      |_ => loophelper n next t mark
      end)
  end
)
|0 => t
end.

Definition update_ancestor_marks t mark commit :=
let todo := empty_queue_commit in 
let todo := push todo commit in
let (*'(t, _, _)*) t := loophelper 10 todo t mark in
t.



Fixpoint update_ancestor t mark parents := 
match parents with
|[] => t
|h::[] => let t := update_ancestor_marks t mark h in t
|h::tl => let t := update_ancestor_marks t mark h in update_ancestor t mark tl
end.



Definition update_parents t d commit parents := 
let t := add_parents t commit parents in
let t := add_to_layer t d commit in 

let t := 
  if (check_not_eq d (depth t)) then
  (
    let layer := get_layer t (depth t) in 
    let comp := check_all_both_seen layer in (*include t in the argument*)
    let t := if (comp) then (set_complete t true) else (set_depth t d) in 
    t  
  )else(
    t
  ) in 

let mark := get_mark t commit in 
let t := 
  match mark with
  |Some m => update_ancestor t m parents
  |None => t
  end
in
t.

Fixpoint insert_init init todo :=
match init with
|[] => todo
|h::t => let todo := push_pair todo 0 h in 
          insert_init t todo
end.

Inductive status :=
|Stop
|Continue.

Definition check state :=
if (complete state) then Stop else Continue.

Fixpoint check_mem commit seen :=
match seen with
|[] => false
|h::t => if (equal_keys commit h) then true else check_mem commit t 
(*equal_keys check if two commits are equal. Named in different context*)
end.

(*Fixpoint unqueue todo seen {struct todo} :=
match todo with
|[] => (None, todo)
|x::xs => (
  let (_, commit) := (x: (nat * hash)) in
  if (check_mem commit seen) then unqueue xs seen else (Some x, xs)
  )
end.*)

Definition read_parents (commit: hash) bs :=
let parents := bs $? commit in
match parents with
|Some (Value_commit(parents, _)) => parents
|_ => [Dummy_hash]
end.

Definition checkmap (m: fmap nat nat) := 
match (m $? 2) = (Some 3) with
|True => true
end.

Definition ret state :=
lca_mark state.

Fixpoint diff_helper h seen res :=
match seen with
|[] => h::res
|x::xs => (
  let cond := equal_keys h x in 
  match cond with 
  |true => res
  |false => diff_helper h xs res
  end)
end.

Fixpoint find_diff parents seen res :=
match parents with
|[] => res
|h::t => (
  let res := diff_helper h seen res in
  find_diff t seen res)
end.

Fixpoint add_todo todo d parents :=
match parents with
|[] => todo
|h::t => let todo := push_pair todo d h in 
          add_todo todo d t
end. 

(*Fixpoint unqueue todo seen := 
match todo with
|[] => (None, todo)
|x::xs => (let (d, c) := (x:nat*hash) in 
          if (check_mem c seen) then unqueue xs seen else (Some x, xs))
end.*)

(*Definition traverse_bfs init bs state :=
let todo := empty_queue_pair in
let todo := insert_init init todo in
let next := [] in
let aux := 
  (fix aux seen next :=
     let ch := check state in 
      match ch with
      |Stop => state
      |Continue => (
            let (item, todo) := (unqueue todo seen) in
            match item with
            |None => state
            |Some (depth, commit) => (
                   let seen := set_add commit seen in 
                   let parents := read_parents commit bs in
                   let state := update_parents state depth commit parents in 
                   let parents := find_diff parents seen [] in
                   let next := add_todo next (depth+1) parents in
                   aux seen next
            )
            end
      )
      end
  )in aux empty_set.
*)



Fixpoint bfs_aux seen state todo bs next {struct todo}:=
let ch := check state in 
match ch with
|Stop => (state, next, seen)
|Continue => (
      match todo with
      |[] => (state, next, seen)
      |x::xs => (
          let (depth, commit) := (x: (nat * hash)) in
          if (check_mem commit seen) then bfs_aux seen state xs bs next
          else(
            let seen := set_add commit seen in 
            let parents := read_parents commit bs in
            let state := update_parents state depth commit parents in 
            let parents := find_diff parents seen [] in
            let next := add_todo next (depth+1) parents in
            bfs_aux seen state xs bs next
          )
        )
      end
)
end.

Fixpoint bfs_aux_helper n seen state todo bs next {struct n}:=
match n with
|S n => 
  match next with 
  |[] => state
  |(1, Dummy_hash)::[] => (let '(state, next, seen) := bfs_aux seen state todo bs [] in
                          bfs_aux_helper n seen state next bs [])
  |_ => let '(state, next, seen) := bfs_aux seen state todo bs [] in
        bfs_aux_helper n seen state next bs []
  end
|0 => state
end.


Definition traverse_bfs init bs state :=
let todo := empty_queue_pair in
let todo := insert_init init todo in
let seen := [] in 
let state := bfs_aux_helper 10 seen state todo bs [(1, Dummy_hash)] in (*fix this: 10 is hard coded to make the loop run*)
state.


Definition find_lca (c1:hash) (c2:hash) (bs: blockstore) :=
if (equal_keys c1 c2) then ([c1]) 
else  (*considering it is always false for now*)
let init := empty_set in 
let init := set_add c1 init in 
let init := set_add c2 init in 
let s := create_empty_state $0 c1 c2 $0 $0 false 0 [] in 
let state := traverse_bfs init bs s in 
let lcas := ret state in
lcas.
(* 
Fixpoint facto n :=
match n with
|0 => 2
|S n => (let v := fac 3 in
        S n * facto n)
end.
 
Fixpoint fac (n:nat) :=
match n with 
|0 => 1
|S n => (*S n * fact n*)
  (let v := facto n in
  S v * fac n)
end. 

Compute fact 3.*)

(*
Fixpoint old_aux acc lst bs :=
match lst with 
|[] => Some acc
|old ::olds => (
    let acc := three_way_merge acc old bs in
    old_aux acc olds
    )
end.

Definition old lcas :=
match lcas with 
|[] => None
|(old :: olds) => old_aux
*)

Fixpoint three_way_merge n (c1:hash) (c2:hash) bs ans :=
match n with
|0 => ans
|S n =>
(
  match ans with 
  |Dummy_hash => 
      ( (**)
      match (equal_keys c1 c2) with
      |true => c1 
      |false => 
        (
          let lcas := find_lca c1 c2 bs in 
          let old := 
            match lcas with
            |[] => None
            |(old :: olds) => 
                    (let aux := (fix aux acc lst :=
                        match lst with
                        |[] => Some acc
                        |(old' :: olds') => (
                              let acc := three_way_merge n acc old bs ans in 
                              aux acc olds')
                        end
                    ) in
                    aux old olds)
            end
          in 
          let lca := old in
          let ans := 
            match lca with
            |Some x => x
            |None => Dummy_hash
            end
          in 
          ans
       )
      end
     ) (**)
  | _ => ans
end
)
end.

Fixpoint check_exists p redlist :=
match redlist with
|[] => false
|x::xs => if (x =? p) then true else check_exists p xs
end.

Fixpoint add_redlist newtreelist redlist (treelist: tree) := 
let newtreelist := 
  match treelist with
  |[] => newtreelist
  |x::t => (
      let '(c, p, v) := x in
      if (check_exists p redlist) then add_redlist newtreelist redlist t
      else
        let newtreelist := x::newtreelist in
        add_redlist newtreelist redlist t
      )
  end
in 
newtreelist.

Fixpoint findKeyInTree key (treelist:tree) :=
match treelist with
|[] => Hash_block ""
|[(c, k, v)] => if (k =? key) then v else Hash_block ""
|(c, k, v)::t => if (k =? key) then v else findKeyInTree key t
end.

Definition resolve_conflict lca v1 v2 key bs :=
let lca_tree := read_bs_tree lca bs in
let lca_treelist := 
  (match lca_tree with
  |Value_tree t => t
  |_ => []
  end) in
let v := findKeyInTree key lca_treelist in
match v with
|Hash_block "" => (append (append v1 "_") v2)
|Hash_block x => (append(append x v1) v2)
|_ => "error"
end. 

Fixpoint merge_trees treelist1 treelist2 new_tree_list red_list lca bs :=
(match treelist1 with 
| [] => (
      let lst := add_redlist new_tree_list red_list treelist2 in
      (bs, lst))
| (x::xs) => (
      let '(c, p, hash_block_v1) := x in
      let v1 := (match hash_block_v1 with 
                |Hash_block v1 => v1 
                |_ => "" end) in
      let v2 := findKeyInTree p treelist2 in

      let '(new_tree_list, red_list, bs) := 
            (match v2 with 
            |Hash_block "" => ((c, p, Hash_block v1) :: new_tree_list, red_list, bs)
            |Hash_block x => (
                    if (v1 =? x) then(
                      let red_list := p::red_list in
                      ((c, p, Hash_block v1)::new_tree_list, red_list, bs))
                    else (
                      let conflict_string := resolve_conflict lca v1 x p bs in
                      let h := create_block_hash conflict_string in
                      let q := Assign_bs h (Value_block conflict_string) in
                      let red_list := p::red_list in 
                      ((c, p, Hash_block conflict_string) :: new_tree_list, red_list, bs)
                    )
                )
            |_ => ([], [], bs)
            end) in
      merge_trees xs treelist2 new_tree_list red_list lca bs)
end). 
      

Definition merge_branches_with_lca (store: cmd * blockstore * tagstore * cmd) (br1 : branch) (br2 : branch) :=
match store with
|(_, bs, ts, _) => 
  (let c1 := read_ts br1 ts in
  let c2 := read_ts br2 ts in

  let lca := three_way_merge 10 c1 c2 bs Dummy_hash in 

  let val_t1 := read_bs_tree c1 bs in
  let val_t2 := read_bs_tree c2 bs in

  let t1 := (match val_t1 with 
  |Value_tree t1 => t1             (*(let treehash3 := create_tree_hash t1 in Assign_bs treehash3 (Value_tree t1))*)
  |_=> []                          (*Assign_bs Dummy_hash Dummy_value*)
  end) in
  
  let t2 := (match val_t2 with
  | Value_tree t2 => t2
  | _ => []
  end) in

  let (bs, mergedTree) := merge_trees t1 t2 [] [] lca bs in
    (*t1 ++ t2 in*) (*(Content, "mergeKey", Dummy_hash) :: t1 in merge the lists t1 and t2 here*)
  let treehash3 := create_tree_hash mergedTree in
  Assign_bs treehash3 (Value_tree mergedTree);;

  let c3 := ([c1;c2], treehash3) in 
  let commithash3 := create_commit_hash c3 in 
  Assign_bs commithash3 (Value_commit c3);;
  
  Assign_ts br1 commithash3
)%cmd
end.

Example ex5: exists st, basic_step^* ((banyan_add2 (Branch "branch1") "key1" "value1" (Branch "branch2") "key2" "value2"), 
            $0, $0, Skip) st /\ 
            (exists st2, basic_step^* (merge_branches_with_lca st (Branch "branch1") (Branch "branch2"), $0, $0, Skip) st2).
Proof.
eexists.
propositional.
eapply TrcFront.
unfold banyan_add2.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.







eexists.
propositional.
unfold banyan_add2.

eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.
eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqStep.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_bs_Step.

eapply TrcFront.
eapply SeqStep2.
eapply TrcFront.
eapply SeqSolve.
eapply Assign_ts_Step.

econstructor.

unfold merge_branches.

econstructor.
econstructor.



(*Definition publish (st: cmd * blockstore * tagstore * cmd) (br: branch) (rep: branch) :=*)
(*publish and refresh are basically merges only. If I am not checking the valid branches, which I dont thinkk is needed
for semantics, there is nothing else to do more than merge. So not doing publish/refresh for now*)

Definition dummyMap := fmap (nat nat.

Definition isTrue (b:bool) :=
match b with
|true => True
|false => False
end.

Example ex5: isTrue(true)=False.
Proof.
simplify.
equality.


