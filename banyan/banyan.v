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
(*|Hash_commit (c: hash).*)

Definition commit :Set := (list hash) * hash.
Definition tree := list(content * string * hash).
Definition block := string.

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

  let c2 := ([commithash], treehash2) in 
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
(*econstructor.*)  (*not sure how its solving everything. state is (Skip, bs, ts, Skip) for 
                whcih i dont have any semantics*)
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

Record empty_state := create_empty_state {marks:fmap hash seen; c1: hash; c2: hash; parents: fmap hash (list hash); 
layers: fmap nat hash; complete: bool; depth: nat}.

Definition add_parents t c p := 
let p := parents t $+ (c, p) in 
create_empty_state (marks t) (c1 t) (c2 t) p (layers t) (complete t) (depth t).

Definition get_parent t c := parents t $? c.

Definition add_to_layer t d c:= 
let l := layers t $+ (d, c) in 
create_empty_state (marks t) (c1 t) (c2 t) (parents t) l (complete t) (depth t).

Definition get_layer t d := 
match (layers t $? d) with
| Some h => set_add h empty_set
| None => empty_set
end.

Definition get_mark t elt := marks t $? elt.

Definition set_mark t mark elt := 
let m := marks t $+ (elt, mark) in 
create_empty_state m (c1 t) (c2 t) (parents t) (layers t) (complete t) (depth t).

Definition check_complete (s:empty_state) := complete s = true.

Definition set_complete t b :=
create_empty_state (marks t) (c1 t) (c2 t) (parents t) (layers t) b (depth t).

Definition set_depth t d := 
create_empty_state (marks t) (c1 t) (c2 t) (parents t) (layers t) (complete t) (d+1).

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

Fixpoint loop t mark todo :=
match (pop todo) with
|Some (a, todo) => (
  let old_mark := get_mark t a in 
  let t := set_mark t mark a in 
  let todo :=
    match old_mark with
    |Some (SeenBoth | LCA) => todo
    |Some mark => todo
    |_ => aux1 t a todo
    end
  in
  let m := aux2 mark in
  loop t m todo
)
|None => t
end.


Definition update_ancestor_marks t mark commit :=
let todo := empty_queue in 
let todo := push todo commit in
loop t mark todo



Definition update_ancestor t mark parents := 
match parents with
|[] =>
|h::[] => update_ancestor_marks t mark h
|h::t => update_ancestor_marks t mark h; update_ancestor t mark t

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
update_ancestor t mark parents.

Definition find_lca (c1:hash) (c2:hash) :=
(*if (c1 = c2) then c1 
else*)  (*considering it is always false for now*)
let init := empty_set in 
let init := set_add c1 init in 
let init := set_add c2 init in 
let s := create_empty_state $0 c1 c2 $0 $0 false in 



Definition three_way_merge (c1:hash) (c2:hash) bs ts :=
(*if (c1 = c2) then c1 
else*)  (*considering it is always false for now*)
let lca := find_lca c1 c2  in 
lca.

Definition merge_branches_with_lca (store: cmd * blockstore * tagstore * cmd) (br1 : branch) (br2 : branch) :=
match store with
|(_, bs, ts, _) => 
  (let c1 := read_ts br1 ts in
  let c2 := read_ts br2 ts in

  let lca := three_way_merge c1 c2 bs ts in 

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


