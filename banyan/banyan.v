Require Import Frap.

Set Implicit Arguments.


Inductive content := 
|Node
|Content.

Inductive branch := 
|Branch (n : string).

Inductive hash :=
|Hash_block (b : string)
|Hash_tree (t: list(content * string * hash))
(*|Hash_commit (c: (list hash * hash)).*)
|Hash_commit (c: hash).

Definition commit := hash.
Definition tree := list(content * string * hash).
Definition block := string.

Inductive value :=
|Value_commit (c: commit) (*commit is hash, so hash to be defined first*)
|Value_tree (t: tree)
|Value_block (b: block).

Definition tagstore := fmap branch commit.  (*branch : string -> hash_block (c: commit)*)

Definition blockstore := fmap hash value.   (*hash_block (data:string) -> Value_block(data:string)*)

Definition create_block_hash (b: block) : hash := Hash_block b.
Definition create_tree_hash (t: tree) : hash := Hash_tree t.
(*Definition create_commit_hash (c: (list hash * hash)) : hash := Hash_commit c.*)
Definition create_commit_hash (c: hash) : hash := Hash_commit c.

Inductive cmd :=
|Seq : cmd -> cmd -> cmd
|add_block : value -> cmd
|Assign : var -> value -> cmd
|Assign_bs : hash -> value -> cmd
|Skip: cmd.


(*Inductive banyan_cmd :=
|returnvalue : blockstore -> banyan_cmd
|Assign_bs : hash -> value -> blockstore -> banyan_cmd.*)

Definition returnvalue : Type := (blockstore * tagstore).

Delimit Scope cmd_scope with cmd.
Infix ";;" := Seq (at level 80) : cmd_scope.

(*Inductive dummy_cmd_step : (blockstore * hash * value) -> (blockstore * hash * value) -> Prop :=
|cmd_step_Assignbs : forall bs h v,
  dummy_cmd_step (bs, h, v) (bs $+ (h, v), h, v).

Definition dummy_banyan_add (br: branch) (k: string) (v: string) (bs: blockstore) :=
  Assign_bs bs (create_block_hash v) (Value_block v).

Example ex: exists st, dummy_cmd_step ($0, (create_block_hash "val"), (Value_block "val")) st.
Proof.
eexists.
econstructor.
Qed.
*)

Definition banyan_add (br: branch) (k: string) (v: string) :=
(*Seq (Assign_bs (create_block_hash v) (Value_block v)) (Assign_bs (create_block_hash v) (Value_block v)).
*)
  (let h := create_block_hash v in
  Assign_bs h (Value_block v) ;; 

  let t := (Content, k, h)::[] in
  let treehash := create_tree_hash t in
  Assign_bs treehash (Value_tree t);;

  let c := treehash in (*change*)
  let commithash := treehash in (*change*)
  Assign_bs commithash (Value_commit c) 
  
  )%cmd.



(*Definition banyan_add (br: branch) (k: string) (v: string) (bs: blockstore) (ts: tagstore): returnvalue := 
  let bs := Assign_bs (create_block_hash v) (Value_block v) bs in
  let t := (Content, k, (create_block_hash v))::[] in
  let bs := Assign_bs (create_tree_hash t) (Value_tree t) bs in (bs, ts).*)


Inductive cmd_step : cmd * blockstore * tagstore -> cmd * blockstore * tagstore -> Prop :=
|AssignbsStep : forall blockhash blockvalue bs ts,
  cmd_step ((Assign_bs blockhash blockvalue), bs, ts) (Skip, (bs $+ (blockhash, blockvalue)), ts).

Inductive basic_step : (cmd * blockstore * tagstore * cmd) -> (cmd * blockstore * tagstore * cmd) -> Prop :=
|SeqStep : forall c1 c2 k bs ts c1' bs' ts',
  cmd_step (c1, bs, ts) (c1', bs', ts') ->
  basic_step (Seq c1 c2, bs, ts, k) (c1', bs', ts', (Seq c2 k))
|SeqStep2 : forall bs ts c k,
  basic_step (Skip, bs, ts, (Seq c k)) (c, bs, ts, k).

(*Definition checkblock (st: cmd * blockstore * tagstore) :=
match st with
|(_, bs, ts) => (bs $? (create_block_hash "value")) = Some (Value_block "value")
end.*)

Example ex2: exists st, basic_step ((banyan_add (Branch "branch") "key" "value"), $0, $0, Skip) st.
Proof.
eexists.
propositional.
unfold banyan_add.

econstructor.

eapply AssignbsStep.
econstructor.
Qed.





















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
