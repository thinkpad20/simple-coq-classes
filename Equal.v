(* Equal: a type class for types with decidable equality. This is slightly 
   less general than the [EqDec] class defined in the [EquivDec] module, 
   because it is specific to the [eq] relation. *)

Require Import Coq.Arith.Peano_dec.
Require Import Relation_Definitions EquivDec.
Require Import Ascii String.

Class Eq (T:Type) := {
  decide_eq: forall a b: T, {a = b} + {a <> b}
}.

(* The Eq class is just EqDec with the relation specialized to [eq]. *)
Theorem Eq_EqDec : forall T, Eq T -> EqDec T eq.
Proof.
  intros.
  unfold EqDec.
  intros.
  destruct (decide_eq x y).
  left. apply e.
  right. apply n.
Defined.

Instance eq_nat: Eq nat := {
  decide_eq := eq_nat_dec
}.

Instance eq_ascii: Eq ascii := {
  decide_eq := ascii_dec
}.

Instance eq_string: Eq string := {
  decide_eq := string_dec
}.

Open Scope list_scope.

Section EqList.
  Context {T: Type}.
  Context {eqT: Eq T}.
  
  Theorem list_eq_dec: forall l l': list T, {l = l'} + {l <> l'}.
    intros l.
    induction l.
      intros l'. destruct l'. left. reflexivity.
      right. intuition. inversion H.
      intros l'. destruct l'. right. intuition. inversion H.
      assert ({l = l'} + {l <> l'}). apply IHl.
      assert ({a = t} + {a <> t}). apply decide_eq.
      destruct H. 
        destruct H0. 
          left. rewrite e. rewrite e0. reflexivity.
          right. rewrite e. intuition. inversion H. contradiction.
        right. intuition. inversion H. contradiction. 
        inversion H. contradiction.
  Defined.

  Instance eq_list: Eq (list T) := {
    decide_eq := list_eq_dec
  }.
End EqList.
