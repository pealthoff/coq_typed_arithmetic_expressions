Inductive term : Type :=
  | true : term
  | false : term
  | ifThenElse : term -> term -> term -> term
  | zero: term
  | succ: term -> term
  | pred: term -> term
  | iszero: term -> term.

Inductive bvalue : term -> Prop :=
  | vtrue: bvalue true
  | vfalse: bvalue false.

Inductive nv : term -> Prop :=
  | vzero : nv zero
  | vsucc : forall t, nv t -> nv (succ t).

Definition value (t:term) := bvalue t \/ nv t.

Reserved Notation "t1 '>>' t2" (at level 40).

Inductive eval : term -> term -> Prop :=
  | E_IfTrue : forall t2 t3,
    (ifThenElse true t2 t3) >> t2
  | E_IfFalse : forall t2 t3,
    (ifThenElse false t2 t3) >> t3
  | E_If : forall t1 t1' t2 t3,
    t1 >> t1' ->
    (ifThenElse t1 t2 t3) >> (ifThenElse t1' t2 t3)
  | E_IsZero : forall t1 t1',
    t1 >> t1' ->
    (iszero t1) >> (iszero t1')
  | E_IsZeroZero :
    (iszero zero) >> true
  | E_IsZeroSucc : forall t1,
    nv t1 ->
    (iszero (succ t1)) >> false
  | E_Succ : forall t1 t1',
    t1 >> t1' ->
    (succ t1) >> succ t1'
  | E_PredZero :
    (pred zero) >> zero
  | E_PredSucc : forall t1,
    nv t1 ->
    (pred (succ t1)) >> t1
  | E_Pred : forall t1 t1',
    t1 >> t1' ->
    (pred t1) >> (pred t1')
  where " t1 >> t2 " := (eval t1 t2).

Inductive type : Type :=
  | Bool : type
  | Nat : type.

Reserved Notation " t ':' T" (at level 40).

Inductive tc : term -> type -> Prop :=
  | T_True :
    true : Bool
  | T_False:
    false : Bool
  | T_If : forall t1 t2 t3 T,
    t1 : Bool ->
    t2 : T ->
    t3 : T ->
    (ifThenElse t1 t2 t3) : T
  | T_Zero :
    zero : Nat
  | T_Succ : forall t1,
    t1 : Nat ->
    (succ t1) : Nat
  | T_Pred : forall t1,
    t1: Nat ->
    (pred t1) : Nat
  | T_IsZero : forall t1,
    t1 : Nat ->
    (iszero t1) : Bool
where "t ':' T" := (tc t T).

(* Canonical Forms *)

Lemma canonical_bool : forall v,
  (value v) /\ v : Bool -> (v = true) \/ (v = false).
Proof.
  intros. destruct H.
  inversion H. inversion H1.
  - left. reflexivity.
  - right. reflexivity.
  - inversion H1.
    + rewrite <- H2 in H0. inversion H0.
    + rewrite <- H3 in H0. inversion H0.
  Qed.

Lemma canonical_nat : forall v,
  (value v) /\ v : Nat -> nv v.
Proof.
  intros. destruct H.
  inversion H. destruct H1.
    inversion H0.
    inversion H0.
    apply H1.
  Qed.

Theorem progress : forall t T,
  t : T -> (value t) \/ (exists t', t >> t').
Proof.
  intros. induction H.
  - (*T_True*) left. unfold value. left. apply vtrue.
  - (*T_False*) left. unfold value. left. apply vfalse.
  - (*T_If*) right. destruct IHtc1. 
    + assert(CB: (t1 = true) \/ (t1 = false)).
    {
      apply canonical_bool. split. apply H2. apply H.
    }
      destruct CB as [CBT | CBF].
      * exists t2. rewrite -> CBT. apply E_IfTrue.
      * exists t3. rewrite -> CBF. apply E_IfFalse.
    + destruct H2.
      exists (ifThenElse x t2 t3).
      apply E_If. apply H2.
  - (*T_Zero*) left. unfold value. right. apply vzero.
  - (*T_Succ*) destruct IHtc.
    + left. unfold value. right. apply vsucc.
      apply canonical_nat. split. apply H0. apply H.
    + right. destruct H0. exists (succ x). apply E_Succ. apply H0.
  - (*T_Pred*) right. destruct IHtc.
    + assert(CV: nv t1).
      {
        apply canonical_nat. split. apply H0. apply H.
      }
      inversion CV.
      * exists zero. apply E_PredZero.
      * exists t. apply E_PredSucc. apply H1.
    + destruct H0. exists (pred x). apply E_Pred. apply H0.
  - (*T_IsZero*) right. destruct IHtc.
    + assert(CV: nv t1).
      {
        apply canonical_nat. split. apply H0. apply H.
      }
      inversion CV.
      * exists true. apply E_IsZeroZero.
      * exists false. apply E_IsZeroSucc. apply H1.
    + destruct H0. exists (iszero x). apply E_IsZero. apply H0.
  Qed.
