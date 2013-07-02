Require Import
  abstract_algebra interfaces.rationals interfaces.orders interfaces.affine_extension
  theory.subset theory.rationals orders.rationals orders.abs orders.minmax
  the_rationals implementations.affinely_extended_ring
  stdlib_field.

Module Type TheAERationalsSig.
  Parameter A : Type.
  Parameter Q : @Subset A.
  Parameter Qinf : AffExt Q.
  Parameter Qfull : AffExtFull Q.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter infty: Infty A.
  Parameter negate : Negate A.
  Parameter inv  : Inv A.
  Parameter equiv: Equiv A.
  Parameter uneq : UnEq A.
  Parameter U    : RationalsToField Q.
  Parameter rationals : @Rationals A Q plus mult zero one negate inv equiv uneq U.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter ae_field : AffinelyExtendedField Q.
  Parameter eq_dec : StrongSubDecision Qfull Qfull (=).
  Parameter le_dec : StrongSubDecision Qfull Qfull (≤).
  Parameter abs : Abs A.
  Parameter dec_abs : DecAbs Q.
End TheAERationalsSig.

Local Notation Q' := the_rationals.
Local Notation T := (AffineExtendT TheRationals.A).
Local Notation X := (AffineExtendImage Q').

Module TheAERationals : TheAERationalsSig.
  Definition A : Type := T.
  Definition Q : @Subset A := X.
  Definition Qinf := _ : AffExt X.
  Definition Qfull := _ : AffExtFull X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition infty := _ : Infty T.
  Definition negate:= _ : Negate T.
  Definition inv   := _ : Inv T.
  Definition equiv := _ : Equiv T.
  Definition uneq  := _ : UnEq T.
  Instance: AffinelyExtendedField X := _.
  Definition U     := rationals.iso_to_field (cast Q' X).
  Definition rationals := rationals.iso_is_rationals (cast Q' X).
  Definition le := _ : Le T.
  Definition lt := _ : Lt T.
  Definition ae_field := _ : AffinelyExtendedField X.
  Definition eq_dec := _ : StrongSubDecision (AffineExtendFull Q') (AffineExtendFull Q') (=).
  Definition le_dec := _ : StrongSubDecision (AffineExtendFull Q') (AffineExtendFull Q') (≤).
  Definition abs : Abs T := default_abs (R:=X).
  Instance: AffinelyExtendedRing X := _.
  Definition dec_abs := default_abs_spec (R:=X).
End TheAERationals.

Notation the_ae_rationals := TheAERationals.Q.
Hint Extern 10 (@Subset TheAERationals.A) => eexact (aff_ext_full the_ae_rationals) : typeclass_instances.
Hint Extern 12 (@Subset TheAERationals.A) => eexact (aff_ext the_ae_rationals) : typeclass_instances.

Local Notation QA := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).
Add Field Q : (stdlib_field_theory Q).

Ltac ae_rat_set_min δ a b Ea Eb :=
  set (δ := @meet _ (min (X:=Q∞)) a b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
  assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _));
  assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _)).

