Require Import
  abstract_algebra interfaces.orders interfaces.affine_extension theory.strong_setoids theory.fields.
Require Export
  orders.affinely_extended_ring orders.fields.

Local Notation T  := (aff_ext_full _).
Local Notation "F∞" := (aff_ext _).
Local Notation U := (ae_undef _).
Local Notation notR := (ae_inf_undef _).

Section closed.
  Context `{AffinelyExtendedField A (F:=F)}.
  Hint Extern 10 (@set A) => eexact T : typeclass_instances.

  Lemma ae_inv_closed : Closed (T ⇀ T) (inv). Proof morphism_closed (inv).

  Lemma ae_inv_proper : Proper ((T,=) ==> (T,=)) (inv). Proof morphism_proper _.

End closed.

Hint Extern 4 (inv _ ∊ T) => eapply @ae_inv_closed : typeclass_instances.

Hint Extern 2 (Proper ((T,=) ==> _) (-)) => eapply @ae_inv_proper : typeclass_instances.

Section misc.
  Context `{AffinelyExtendedField A (F:=F)}.
  Hint Extern 10 (@set A) => eexact T : typeclass_instances.

  Lemma ae_in_halves x `{x ∊ F∞} : x/2 + x/2 = x.
  Proof.
    destruct (ae_decompose_ext x) as [?|[?[E|E]]].
    rewrite <-(_ $ mult_2_plus_r (x/2)), <-(_ $ associativity (.*.) _ _ _).
    rewrite (_ $ field_inv_l _). exact (mult_1_r _).
    rewrite (_ $ E), (_ $ ae_pos_mult_inf_l _). exact ae_inf_plus_inf.
    rewrite (_ $ E), (_ $ ae_pos_mult_minf_l _). exact ae_minf_minus_inf.
  Qed.

End misc.
