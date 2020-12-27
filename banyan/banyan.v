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


Definition searchKey value_tree :=  (*accomodate key k in search*)
match value_tree with
| Value_tree t => 
  match t with
  | [] => true (*create_block_hash ""*)
  | [(_, _, h)] => true (*h*)
  | _ => true (*create_block_hash ""*)
  end
| _ => true (*create_block_hash ""*)
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

(*Inductive read_semantics : (cmd * option hash) -> (cmd * option hash) -> Prop :=
|Read_ts_step : forall br ts,
  read_semantics (Read_ts br ts, None) (Skip, ts $? br).*)

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

Definition read_bs_tree (hashArg : hash) (bs: blockstore) :=
match (bs $? hashArg) with
|Some x => x
|None => Dummy_value
end.

Definition verify_store_helper (st: cmd * blockstore * tagstore * cmd)  br (v:block) :=
match st with
|(_, bs, ts, _) =>
  let commitHash := read_ts br ts in
  let value_commit :=  read_bs commitHash bs in
  let treeHash := getSecondInCommit value_commit in
  let value_tree := read_bs_tree treeHash bs in 
  let blockHash := searchKey value_tree in
blockHash
  (*let latestCommitHash := resolve_opt_hash (ts $? br) in
  let value_commit :=  resolve_opt_commit (bs $? latestCommitHash) in
  let treeHash := getSecondInCommit value_commit in
  let value_tree := resolve_opt_tree (bs $? treeHash) in
  let blockHash := searchKey value_tree in  (*accomodate key k in search*)
  let value_block := (bs $? blockHash) in
  
  match value_block with
  | Some x => 
    match x with
    | Value_block v => true
    | _ => false
    end
  | _ => false
  end
*)
end.


Definition verify_store (st: cmd * blockstore * tagstore * cmd) br v := 
match st with
|(_,bs,ts,_) => verify_store_helper st br v
end.



(*adding and checkinng the first item in the database*)
Example ex2: exists st, (basic_step^* ((banyan_add (Branch "branch") "key" "value"), $0, $0, Skip) st) /\ 
                                                          ((verify_store_helper st (Branch "branch") "value") = true).
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

unfold verify_store.
unfold verify_store_helper.
unfold read_ts.
simplify.
unfold read_bs.
simplify.

simplify.
simplify.

unfold read_bs_tree.
simplify.

unfold searchKey.

simplify.
Admitted.
(*econstructor.

Qed.*)


Definition banyan_add2 (br: branch) (k1: string) (v1: string) (k2: string) (v2: string):=
(let h := create_block_hash v1 in
  Assign_bs h (Value_block v1) ;;

  let t := (Content, k1, h)::[] in
  let treehash := create_tree_hash t in
  Assign_bs treehash (Value_tree t);;

  let c := ([], treehash) in 
  let commithash := create_commit_hash c in 
  Assign_bs commithash (Value_commit c);;
  
  Assign_ts br commithash;;
  


  let h2 := create_block_hash v2 in
  Assign_bs h2 (Value_block v2) ;;

  let t2 := (Content, k2, h2)::t in
  let treehash2 := create_tree_hash t2 in
  Assign_bs treehash2 (Value_tree t2);;

  let c2 := ([commithash], treehash2) in 
  let commithash2 := create_commit_hash c2 in 
  Assign_bs commithash2 (Value_commit c2);;
  
  Assign_ts br commithash2

  )%cmd.



Example ex3: exists st, basic_step^* ((banyan_add2 (Branch "branch") "key1" "value1" "key2" "value2"), 
            $0, $0, Skip) st.
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


econstructor.  (*not sure how its solving everything*)
Qed.


Definition read_store_helper (st: cmd * blockstore * tagstore * cmd)  br (v:block) :=
match st with
|(_, bs, ts, _) =>
  let latestCommitHash := resolve_opt_hash (ts $? br) in
  let value_commit :=  resolve_opt_commit (bs $? latestCommitHash) in
  let treeHash := getSecondInCommit value_commit in
  let value_tree := resolve_opt_tree (bs $? treeHash) in
  let blockHash := searchKey value_tree in  (*accomodate key k in search*)
  let value_block := (bs $? blockHash) in

  match value_block with  (*value_block is of type option value*)
  | Some x => 
    match x with
    | Value_block v => True
    | _ => False
    end
  | _ => False
  end

end.


Definition read_store (st: cmd * blockstore * tagstore * cmd) br v := 
match st with
|(_,bs,ts,_) => read_store_helper st br v
end.

Example ex4: exists st, (basic_step^* ((banyan_add (Branch "branch") "key" "value"), $0, $0, Skip) st) /\ 
                                                          ((read_store_helper st (Branch "branch") "value")).
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
simplify.

(*
unfold read_store.
unfold read_store_helper.
simplify.*)
econstructor.

unfold verify_store.
unfold verify_store_helper.

econstructor.
simplify.
equality.

Admitted.

Definition isTrue (b:bool) :=
match b with
|true => True
|false => False
end.

Example ex5: isTrue(true)=False.
Proof.
simplify.
equality.



(*Inductive commit (*(p: parent) (h: hash)*) := 
|Commit (c: (list hash * hash)).
*)

(*Definition hashlist := list hash.

Definition commit := pair hashlist hash.
*)


(*Inductive step : cmd_state -> cmd_state -> Prop := 
|StepAssign: forall v x e k,
  step (v, Assign x e, k) (v $+ (x, e), Skip, k)
|StepSeq : forall v c1 c2 k,
  step (v, (Seq c1 c2), k) (v, c1, Seq c2 k).
*)

(*Definition cmd_state:Type := blockstore * cmd * cmd.

Definition cred : Type := branch * string(*key*) * value.

Definition state :Type := cred * blockstore * tagstore.

Inductive banyan_cmd : state -> state -> Prop :=
|Add_block : forall v blockhash br branc valu bs ts bs' key,
  blockhash = create_block_hash v ->
  br = Branch branc -> 
  valu = Value_block v ->
  bs' = bs $+ (blockhash, valu) ->
  banyan_cmd (br, key, valu, bs, ts) (br, key, valu, bs', ts).

Definition state' : Type := string * string * string * blockstore * tagstore. (*b,t,c are not same types, convert them to value and then change the state*)

Inductive banyan_cmd : state' -> state' -> Prop :=
|Add_block : forall v blockhash val bs ts bs' k br,
  blockhash = create_block_hash v ->
  (*val = Value_block v ->*)
  bs' = bs $+ (blockhash, v) ->
  banyan_cmd (br, k, v, bs, ts) (br, k, v, bs', ts)
|Add_tree : forall treehash t val bs' bs ts br k,
  treehash = create_tree_hash t ->
  (*val = Value_tree t ->*)
  bs' = bs $+ (treehash, t) ->
  banyan_cmd (br, k, t, bs, ts) (br, k, t, bs', ts).
|Add_commit : forall commithash c val bs' bs ts br brnch ts',
  commithash = create_commit_hash c ->
  val = Value_commit c ->
  bs' = bs $+ (commithash, val) ->
  br = Branch brnch -> 
  ts' = ts $+ (br, commithash) ->
  banyan_cmd (bs, ts) (bs', ts'). *)

(*
Inductive banyan_cmd : state' -> state' -> Prop :=
|Add_block : forall v blockhash val bs ts bs',
  blockhash = create_block_hash v ->
  val = Value_block v ->
  bs' = bs $+ (blockhash, val) ->
  banyan_cmd (bs, ts) (bs', ts)
|Add_tree : forall treehash t val bs' bs ts,
  treehash = create_tree_hash t ->
  val = Value_tree t ->
  bs' = bs $+ (treehash, val) ->
  banyan_cmd (bs, ts) (bs', ts)
|Add_commit : forall commithash c val bs' bs ts br brnch ts',
  commithash = create_commit_hash c ->
  val = Value_commit c ->
  bs' = bs $+ (commithash, val) ->
  br = Branch brnch -> 
  ts' = ts $+ (br, commithash) ->
  banyan_cmd (bs, ts) (bs', ts'). 
*)




(*Definition valuation := fmap var value.
*)

(*|StepAddBlock : forall v,
*)
(*|StepSkip : forall v,
step (Skip, k) (k, Skip).
*)
Definition banyan_add (b: branch) (k: string) (v: string) (bs: blockstore) (ts: tagstore) :=
  Assign "val" (Value_block v).
  

  (*blockstore = add_block value
  blockstore = add_tree tree;;
  blockstore, tagstore = add_commit commit.
*)
Example eg1:
  step banyan_add "br" "key" "val" $0 $0.
