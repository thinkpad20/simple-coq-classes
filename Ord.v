(* Ord: type class for ordered types. *)

Require Import EquivDec Compare_dec Relation_Definitions Le.
Require Import Coq.Classes.RelationClasses.
Require Import Equal Relations.

Open Scope list_scope.

Check transitive.

Class Ord (T: Type) {eq_: Eq T} := {
  lessthan: relation T;
  lt_trans: transitive lessthan;
  lt_asym: asymmetric lessthan;
  lt_dec: forall a b: T, {lessthan a b} + {a = b} + {lessthan b a}
}.

Instance ord_nat : Ord nat := {
  lessthan := lt;
  lt_dec := lt_eq_lt_dec
}.
Proof.
  unfold transitive. 
  apply Lt.lt_trans.
  unfold asymmetric.
  apply NPeano.Nat.lt_asymm.
Defined.

Section ListLt.
  Context {T: Type}.
  Context {eq_elem: Eq T}.
  Context {ord_elem: Ord T}.
  
  Inductive list_lt: list T -> list T -> Prop :=
    | lt_nil  : forall x l, list_lt nil (x::l)
    | lt_cons : forall x xs y ys,
        lessthan x y -> list_lt (x::xs) (y::ys).
  
  Lemma list_lt_trans: transitive list_lt.
  Proof.
    unfold transitive. intros xs ys zs H1 H2.
    generalize dependent ys.
    generalize dependent zs.
    induction xs.
      intros.
      destruct zs. inversion H1. inversion H2. constructor.
      intros.
      inversion H1.
      destruct zs. subst. inversion H2.
      subst. inversion H2. subst.
      constructor. apply (lt_trans a y t H4 H0).
  Qed.

  Lemma list_lt_asym: asymmetric list_lt.
  Proof.
    unfold asymmetric. unfold not. intros.
    inversion H. subst. inversion H0. subst.
    inversion H0. subst. apply (lt_asym x y H1 H3).
  Qed.

  (* Theorem list_lt_asym_dec: forall l l', {list_lt l l'} + {~list_lt l l'}. *)
  (* Proof. *)
  (*   intros l. induction l. *)
  (*   destruct l'. right. intuition. inversion H. *)
  (*   left. constructor. *)
  (*   intros l'. *)
  (*   destruct l'. right. intuition. inversion H. *)
  (*   destruct (lt_dec a t). *)
  (*   destruct s. *)
  (*   destruct (IHl l'). *)
  (*   left. constructor. apply l0. apply l1. *)
  (*   right. intuition. inversion H. subst. contradiction. *)
  (*   right. intuition. inversion H. subst.  *)
  (*   apply (lt_asym t t). apply H3. apply H3. *)
  (*   right. intuition. inversion H. subst. apply (lt_asym a t). *)
  (*   apply H3. apply l0. *)
  (* Defined. *)

  Theorem list_lt_dec: forall l l', {list_lt l l'} + {l = l'} + {list_lt l' l}.
  Proof.
    intros l. 
    induction l.
      intros l'.
      destruct l'. auto. left. left. constructor.
      intros l'.
      destruct l'.
        right. constructor.
        destruct (lt_dec a t).
        inversion s.
        left. left. constructor. apply H.
        destruct (IHl l').
        inversion s0. left. left.
        
        destruct (list_lt_asym_dec l l').
    auto. induction l. destruct l'. left. auto.
    elimtype False. apply b. constructor.
    destruct l'. right. constructor.
    

  Instance list_ord
    {eqlist: Eq (list T)}: Ord (list T) := {
    lessthan := list_lt;
    lt_trans := list_lt_trans;
    lt_asym := list_lt_asym
  }.
  (* decision procedure *)
  
Theorem list_leq_partialorder:
  forall T {eq_elem: Eq T} {ord_elem: Ord T}, partial_order list_leq.
Proof.
  intros.
  unfold partial_order.
  split. unfold preorder.
  split. unfold reflexive. intros l.
  induction l. constructor. constructor. apply eq_implies_leq. reflexivity.
  apply IHl.
  unfold transitive.
    intros xs ys zs H.
    
    
  


(* Instance list_leq_partial_order  *)
(*    {T: Type} {eq_elem: Eq T} {ord_elem: Ord T}:  *)
(*    PartialOrder eq (@list_leq T eq_elem ord_elem). *)
(* Proof. *)
(*   split. *)
(*   (* Prove reflexivity *) *)
(*     unfold Reflexive. *)
(*     intros l. *)
(*     induction l. constructor. *)
(*     constructor. apply eq_implies_leq. reflexivity. apply IHl. *)
(*   (* Prove symmetry *) *)
(*     unfold Symmetric. *)
(*     intros xs ys H. *)
(*     induction xs. *)

Instance ord_list 
  {T: Type} 
  {eq_elem: Eq T}
  {ord_elem: Ord T} 
  {eq_list: Eq (list T)}: 
  Ord (list T) := {
  leq := list_leq
}.

