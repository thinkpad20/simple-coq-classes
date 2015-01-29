Require Import Relation_Definitions.

Section Relations.
  Context {T: Type}.
  Variable R: relation T.
  Definition reflexive: Prop := forall a, R a a.
  Definition transitive: Prop := forall a b c, R a b -> R b c -> R a c.
  Definition symmetric: Prop := forall a b, R a b -> R b a.
  Definition equivalence: Prop := reflexive /\ transitive /\ symmetric.
  Definition antisymmetric: Prop := forall a b, R a b -> R b a -> a = b.
  Definition asymmetric: Prop := forall a b, R a b -> ~R b a.
  Definition preorder: Prop := reflexive /\ transitive.
  Definition partial_order: Prop := preorder /\ antisymmetric.
  
  (* Asymmetry is stronger than antisymmetry. *)
  Theorem asym_implies_antisym: asymmetric -> antisymmetric.
  Proof.
    unfold asymmetric. unfold antisymmetric. unfold not.
    intros asym a b Rab Rba. 
    apply asym in Rab. destruct Rab. apply Rba.
  Qed.
End Relations.
