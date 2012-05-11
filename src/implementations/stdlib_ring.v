Require Import
  Ring abstract_algebra subsetsig theory.rings.

Section semiring.
  Context `{CommutativeSemiRing (R:=R)}.

  Global Instance : SubsetSig_Closed R 0 := _ : 0 ∊ R.
  Global Instance : SubsetSig_Closed R 1 := _ : 1 ∊ R.
  Global Instance : SubsetSig_Closed (R==>R==>R) (+)   := _ : Closed (R==>R==>R) (+).
  Global Instance : SubsetSig_Closed (R==>R==>R) (.*.) := _ : Closed (R==>R==>R) (.*.).

  Notation R' := (every (SubsetSig R)).

  Instance: CommutativeSemiRing R' := subsetsig_comsemiring R.

  Lemma stdlib_semiring_theory : Ring_theory.semi_ring_theory (0:SubsetSig R) 1 (+) (.*.) (=).
  Proof.
   constructor; intros.
   exact (plus_0_l _).
   exact (commutativity (+) _ _).
   exact (associativity (+) _ _ _).
   exact (mult_1_l _).
   exact (mult_0_l _).
   exact (commutativity (.*.) _ _).
   exact (associativity (.*.) _ _ _).
   exact (plus_mult_distr_r _ _ _).
  Qed.

End semiring.

Arguments stdlib_semiring_theory {_ _ _ _ _ _} R {_}.

Section ring.

  Context `{CommutativeRing (R:=R)}.

  Global Instance : SubsetSig_Closed (R==>R) (-) := _ : Closed (R==>R) (-).

  Notation R' := (every (SubsetSig R)).

  Instance: CommutativeRing R' := subsetsig_comring R.

  Lemma stdlib_ring_theory :
    Ring_theory.ring_theory 0 1 (+) (.*.) (λ x y : SubsetSig R, x - y) (-) (=).
  Proof.
   constructor; intros.
   exact (plus_0_l _).
   exact (commutativity (+) _ _).
   exact (associativity (+) _ _ _).
   exact (mult_1_l x).
   exact (commutativity (.*.) _ _).
   exact (associativity (.*.) _ _ _).
   exact (plus_mult_distr_r _ _ _).
   reflexivity.
   exact (plus_negate_r _).
  Qed.

End ring.

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
