Require Import
  Ring abstract_algebra subsetsig theory.rings.

Section contents.

  Context `{CommutativeRing (R:=R)}.

  Global Instance : SubsetSig_Closed R 0 := _ : 0 ∊ R.
  Global Instance : SubsetSig_Closed R 1 := _ : 1 ∊ R.
  Global Instance : SubsetSig_Closed (R==>R==>R) (+)   := _ : Closed (R==>R==>R) (+).
  Global Instance : SubsetSig_Closed (R==>R==>R) (.*.) := _ : Closed (R==>R==>R) (.*.).
  Global Instance : SubsetSig_Closed (R==>R) (-) := _ : Closed (R==>R) (-).

  Local Notation R' := (Every (SubsetSig R)).

  Instance: CommutativeRing R' := subsetsig_comring R.

  Lemma stdlib_ring_theory :
    Ring_theory.ring_theory 0 1 (+) (.*.) (λ x y : SubsetSig R, x - y) (-) (=).
  Proof.
   constructor; intros.
   exact (plus_0_l (R:=R') x).
   exact (commutativity (S:=R') x y).
   exact (associativity (S:=R') x y z).
   exact (mult_1_l (R:=R') x).
   exact (commutativity (S:=R') x y).
   exact (associativity (S:=R') x y z).
   exact (distribute_r (S:=R') x y z).
   reflexivity.
   exact (plus_negate_r (R:=R') x).
  Qed.

End contents.

Arguments stdlib_ring_theory {_ _ _ _ _ _ _} R {_}.

Ltac subring R := subsetsig_quote_equiv R; ring.

(*
Section test.

  Context `{CommutativeRing (R:=R)}.


  Add Ring R : (stdlib_ring_theory R).


  Goal forall x `{!x ∊ R} y `{!y ∊ R}, x*y=y*x.
  Proof. intros. subsetsig_quote_equiv R. ring. Qed.

End test.
*)
