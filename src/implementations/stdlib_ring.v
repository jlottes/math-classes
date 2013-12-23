Require Import
  Ring abstract_algebra setsig theory.rings.

Section semiring_ops.
  Context `(R:set) `{H:CommutativeSemiRing _ (R:=R)}.

  Instance stdlib_ring_zero_closed : 0 ∊ R := _.
  Instance stdlib_ring_one_closed  : 1 ∊ R := _.
  Instance stdlib_ring_plus_closed : Closed (R⇀R⇀R) (+) := _.
  Instance stdlib_ring_mult_closed : Closed (R⇀R⇀R) (.*.) := _.
End semiring_ops.

Hint Extern 2 (Zero (setsig ?R)) => eapply (setsig_zero R (pf:=stdlib_ring_zero_closed R)) : typeclass_instances.
Hint Extern 2 (One  (setsig ?R)) => eapply (setsig_one  R (pf:=stdlib_ring_one_closed  R)) : typeclass_instances.
Hint Extern 2 (Plus (setsig ?R)) => eapply (setsig_plus R (pf:=stdlib_ring_plus_closed R)) : typeclass_instances.
Hint Extern 2 (Mult (setsig ?R)) => eapply (setsig_mult R (pf:=stdlib_ring_mult_closed R)) : typeclass_instances.

Section semiring.
  Context `(R:set) `{CommutativeSemiRing _ (R:=R)}.

  Notation R' := (every (setsig R)).

  Instance: CommutativeSemiRing R' := setsig_comsemiring R.

  Lemma stdlib_semiring_theory : Ring_theory.semi_ring_theory (R:=setsig R) 0 1 (+) (.*.) (=).
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

Section ring_ops.
  Context `(R:set) `{H:CommutativeRing _ (R:=R)}.

  Instance stdlib_ring_negate_closed : Closed (R⇀R) (-) := _.
End ring_ops.

Hint Extern 2 (Negate (setsig ?R)) => eapply (setsig_negate R (pf:=stdlib_ring_negate_closed R)) : typeclass_instances.

Section ring.
  Context `(R:set) `{CommutativeRing _ (R:=R)}.

  Notation R' := (every (setsig R)).

  Instance: CommutativeRing R' := setsig_comring R.

  Lemma stdlib_ring_theory :
    Ring_theory.ring_theory (R:=setsig R) 0 1 (+) (.*.) (λ x y, x - y) (-) (=).
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

Ltac stdlib_semiring_quote R := 
  let H1 := constr:(_ : CommutativeSemiRing R) in
  let zc := constr:(stdlib_ring_zero_closed R (H:=H1)) in
  let oc := constr:(stdlib_ring_one_closed R (H:=H1)) in
  let pc := constr:(stdlib_ring_plus_closed R (H:=H1)) in
  let mc := constr:(stdlib_ring_mult_closed R (H:=H1)) in
  setsig_quote R zc oc pc mc zc zc.

Ltac stdlib_ring_quote R := 
  let H1 := constr:(_ : CommutativeSemiRing R) in
  let H2 := constr:(_ : CommutativeRing R) in
  let zc := constr:(stdlib_ring_zero_closed R (H:=H1)) in
  let oc := constr:(stdlib_ring_one_closed R (H:=H1)) in
  let pc := constr:(stdlib_ring_plus_closed R (H:=H1)) in
  let mc := constr:(stdlib_ring_mult_closed R (H:=H1)) in
  let nc := constr:(stdlib_ring_negate_closed R (H:=H2)) in
  setsig_quote R zc oc pc mc nc zc.

Ltac setring R := first [
    let q := stdlib_ring_quote R in setsig_quote_equiv R q
  | let q := stdlib_semiring_quote R in setsig_quote_equiv R q
  ]; ring.

(*
Section test.

  Context `{CommutativeSemiRing (R:=R)}.

  Add Ring R : (stdlib_semiring_theory R).

  Goal forall x `{x ∊ R} y `{y ∊ R}, x*y=y*x.
  Proof. intros. setring R. Qed.

End test.
*)

(*
Section test.

  Context `{CommutativeRing (R:=R)}.

  Add Ring R : (stdlib_ring_theory R).

  Goal forall x `{x ∊ R} y `{y ∊ R}, x*y=y*x.
  Proof. intros. setsig_quote_equiv R ltac:(stdlib_ring_quote R). ring. Qed.

End test.
*)
