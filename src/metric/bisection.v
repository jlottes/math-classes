Require Import
  abstract_algebra interfaces.orders theory.setoids
  interfaces.rationals theory.rationals theory.fields
  interfaces.affine_extension affinely_extended_field the_ae_rationals
  interfaces.naturals theory.naturals orders.naturals the_naturals
  interfaces.integers theory.integers orders.integers the_integers
  interfaces.archimedean_fields orders.archimedean_fields
  misc.quote stdlib_ring stdlib_field_dec.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Section bisection.
  Context `(F:@set AF) `{ArchimedeanField _ (F:=F)}.
  Add Ring F : (stdlib_ring_theory F).

  Context `(X:@set A).
  Context (P : A → AF → Prop).
  Context (bisect : ∀ x `{x ∊ X} δ `{δ ∊ F₊}, P x δ → ∃ `{x' ∊ X}, P x' (2*δ/3) ) .

  Notation Z := the_integers.
  Notation "#" := (integers_to_ring Z F).

  Let aux n `{n ∊ Z} : 2 < n → 2*n ≤ 3*(n-1).
  Proof. intro. rewrite (le_iff_lt_plus_1 _ _).
    apply (flip_pos_minus _ _). split. apply _. red.
    mc_replace (3*(n-1)+1-2*n) with (n-2) on Z by setring Z.
    apply (flip_lt_minus_r _ _ _). now rewrite (_ $ plus_0_l _).
  Qed.

  Context ε `{ε ∊ F₊}.

  Let P' x δ n := P x δ ∧ δ < #n * ε .

  Let iter x `{x ∊ X} δ `{δ ∊ F₊} n `{n ∊ Z₊}
    : P' x δ (2+n) → ∃ `{x' ∊ X} `{δ' ∊ F₊} `{m ∊ Z⁺}, P' x' δ' (2+m) ∧ m < n.
  Proof. intros [IH ?].
    assert (n-1 ∊ Z⁺). split. apply _. red.
      apply (flip_le_minus_r _ _ _). rewrite (_ $ plus_0_l _).
      apply (nat_ne_0_ge_1 (N:=Z⁺)). split. apply _. now destruct (_ : n ∊ Z ₀).
    destruct (bisect x _ δ _ IH) as [x'[??]].
    exists_sub x' (2*δ/3) (n-1). split. split; trivial.
    + apply (lt_le_trans _ (2*#(2+n)/3 * ε) _).
      * mc_replace (2*#(2+n)/3*ε) with (2*(#(2+n)*ε)/3) on F by setring F.
        apply (strictly_order_preserving (.* inv (3:F))); try apply _.
        now apply (strictly_order_preserving ((2:F) *.) _ _).
      * apply (order_preserving (.* ε) _ _).
        apply (mult_inv_le_cancel_l _ _ _).
        rewrite <-(_ $ preserves_3 (f:=#)).
        rewrite <-(_ $ preserves_2 (f:=#)).
        rewrite <-2!(_ $ preserves_mult _ _).
        apply (order_preserving # _ _).
        mc_replace ((2+(n-1))*3) with (3*(2+n-1)) on Z by setring Z.
        apply (aux _). apply (flip_pos_minus _ _).
        mc_replace (2+n-2) with n on Z by setring Z. apply _.
   + apply (flip_pos_minus _ _).
     mc_replace (n-(n-1)) with (1:Z) on Z by setring Z. apply _.
  Qed.

  Let loop : ∀ n `{n ∊ Z⁺} x `{x ∊ X} δ `{δ ∊ F₊}, P' x δ (2+n) 
      → ∃ `{x' ∊ X} `{δ' ∊ F₊}, P' x' δ' 2.
  Proof.
    set (Pn := λ n, ∀ x `{x ∊ X} δ `{δ ∊ F₊}, P' x δ (2+n) 
         → ∃ `{x' ∊ X} `{δ' ∊ F₊}, P' x' δ' 2).
    assert (Proper ((Z⁺,=)==>iff) Pn).
      intros m n E'. unfold_sigs. unfold Pn, P'.
      split; intros P'' x ? d ? E2;
        [ rewrite <-(Z $ E') in E2 | rewrite ->(Z $ E') in E2 ];
        destruct (P'' x _ d _ E2) as [x'[?[d'[? ?]]]]; now exists_sub x' d'.
    apply (naturals.strong_induction (N:=Z⁺) Pn). intros n ? IH x ? d ? iv.
    destruct (nat_0_or_pos (N:=Z⁺) n) as [En|[_ ?]].
      exists_sub x d. destruct iv as [? iv]. split; trivial.
      now rewrite (Z $ En), (Z $ plus_0_r _) in iv.
    assert (n ∊ Z₊) by (split; trivial; apply _).
    assert (1*ε < #2 * ε) as E'. preserves_simplify #.
      apply (strictly_order_preserving (.* ε) _ _). apply lt_1_2.
    destruct (cotransitivity E' d) as [Ed|Ed].
      destruct (iter x d n iv) as [x'[?[d'[?[m[?[iv' Em]]]]]]].
      exact (IH m _ Em x' _ d' _ iv').
    exists_sub x d. destruct iv as [? iv]. split; trivial.
  Qed.

  Lemma bisection_pos x `{x ∊ X} δ `{δ ∊ F₊} : P x δ → ∃ `{x' ∊ X} `{δ' ∊ F₊}, P x' δ' ∧ δ' < 2*ε .
  Proof. destruct (archimedean_int_bounds ( δ/ε )) as [_ [_ [N [? [_ EN]]]]].
    assert (N ∊ Z₊). apply (reflects_pos #). apply _.
      split. apply _. red. subtransitivity (δ/ε). apply (_ : δ/ε ∊ F₊ ).
    intro. assert (P' x δ (2+N)) as HP'.
      split. trivial.
      apply (mult_inv_lt_cancel_l _ _ _).
      subtransitivity (#N).
      apply (strictly_order_preserving # _ _).
      apply (flip_pos_minus _ _).
      mc_replace (2+N-N) with (2:Z) on Z by setring Z. apply _.
    destruct (loop N x δ HP') as [x'[?[δ'[?[? E]]]]].
    rewrite (_ $ preserves_2 (f:=#)) in E.
    exists_sub x' δ'. intuition.
  Qed.

  Lemma bisection x `{x ∊ X} δ `{δ ∊ F⁺} : P x δ → ∃ `{x' ∊ X} `{δ' ∊ F⁺}, P x' δ' ∧ δ' < 2*ε .
  Proof. intro P0. destruct (_ : 2*ε ∊ F₊) as [_ E]; red in E.
    destruct (cotransitivity E δ).
      assert (δ ∊ F₊). split; trivial; apply _.
      destruct (bisection_pos x δ P0) as [x'[?[δ'[??]]]]. now exists_sub x' δ'.
    exists_sub x δ. intuition.
  Qed.
End bisection.

