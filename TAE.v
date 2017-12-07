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

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive eval : term -> term -> Prop :=
  | E_IfTrue : forall t2 t3,
    (ifThenElse true t2 t3) --> t2
  | E_IfFalse : forall t2 t3,
    (ifThenElse false t2 t3) --> t3
  | E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    (ifThenElse t1 t2 t3) --> (ifThenElse t1' t2 t3)
  | E_IsZero : forall t1 t1',
    t1 --> t1' ->
    (iszero t1) --> (iszero t1')
  | E_IsZeroZero :
    (iszero zero) --> true
  | E_IsZeroSucc : forall t1,
    nv t1 ->
    (iszero (succ t1)) --> false
  | E_Succ : forall t1 t1',
    t1 --> t1' ->
    (succ t1) --> succ t1'
  | E_PredZero :
    (pred zero) --> zero
  | E_PredSucc : forall t1,
    nv t1 ->
    (pred (succ t1)) --> t1
  | E_Pred : forall t1 t1',
    t1 --> t1' ->
    (pred t1) --> (pred t1')
  where " t1 --> t2 " := (eval t1 t2).

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

