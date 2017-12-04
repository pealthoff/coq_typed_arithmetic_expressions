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

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive eval : term -> term -> Prop :=
  | E_IfTrue : forall t2 t3,
    (ifThenElse true t2 t3) ==> t2
  | E_IfFalse : forall t2 t3,
    (ifThenElse false t2 t3) ==> t3
  | E_If : forall t1 t1' t2 t3,
    t1 ==> t1' ->
    (ifThenElse t1 t2 t3) ==> (ifThenElse t1' t2 t3)
  | E_IsZero : forall t1 t1',
    t1 ==> t1' ->
    (iszero t1) ==> (iszero t1')
  | E_IsZeroZero :
    (iszero zero) ==> true
  | E_IsZeroSucc : forall t1,
    nv t1 ->
    (iszero (succ t1)) ==> false
  where " t1 ==> t2 " := (eval t1 t2).













Inductive type : Type :=
  | Bool : type
  | Nat : type.

Fixpoint eval (t:term) : term :=
  match t with
  | true => true
  | false => false
  | ifThenElse c t1 t2 =>
    match c with
    | true => t1
    | false => t2
    | otherwise => ifThenElse (eval c) t1 t2
    end
  | zero => zero
  | succ n => succ n
  | pred n =>
    match n with
    | zero => zero
    | succ n2 => n2
    | otherwise => pred (eval n)
    end
  | iszero n =>
    match n with
    | zero => true
    | succ n2 => false
    | otherwise => iszero (eval n)
    end
  end.

Fixpoint tc (t:term) : type :=
  match t with
  | true => Bool
  | false => Bool
  | ifThenElse c t1 t2 => tc t1
  | zero => Nat
  | succ n => Nat
  | pred n => Nat
  | iszero n => Bool
  end.

Fixpoint tcv (v:value) : type :=
  match v with
  | vtrue => Bool
  | vfalse => Bool
  | vzero => Nat
  | vsucc n => Nat
  end.

Lemma IoT1: forall R:type, (tc true = R) -> R = Bool.
Proof. intros. rewrite <- H. reflexivity. Qed.

Lemma IoT2: forall R:type, (tc false = R) -> R = Bool.
Proof. intros. rewrite <- H. reflexivity. Qed.

Lemma CF1: forall v:value, 
  (tcv v = Bool) -> (v = vtrue)\/(v = vfalse).
Proof.
Admitted.

Theorem Progress: forall (t:term),





Fixpoint bigStep (t: term) : value :=
  match t with
  | true => vtrue
  | false => vfalse
  | zero => vzero
  | succ t1 => vsucc (bigStep t1)
  | ifTheElse c t1 t2 =>
    match c with
    | vtrue => (bigStep t1)
    | vfalse => (bigStep t2)
    | otherwise => bigStep (ifThenElse (bigStep c) t1 t2)
  
  end.
