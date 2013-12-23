Require Import
  stdlib_binary_integers
  abstract_algebra interfaces.additional_operations interfaces.orders
  interfaces.modules interfaces.polynomial_rings
  interfaces.integers theory.integers orders.integers
  interfaces.naturals theory.naturals orders.naturals nonneg_integers_naturals peano_naturals
  theory.setoids theory.jections theory.rings orders.rings theory.modules
  orders.lattices orders.minmax lattice_ordered_rings
  stdlib_ring misc.quote
  bigops_int kronecker_delta
  theory.nonneg_int_pow
  seq_polynomials.

(*
Local Notation ZA := BinNums.Z.
Local Notation Z  := (every BinNums.Z).
*)
Local Notation δ := kronecker_delta.

Local Notation "#" := (to_polynomial_ring _).
Local Notation x := polynomial_var.
Local Notation ℰ := polynomial_eval.

Hint Extern 2 (SemiRng_Morphism _ _ #) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ #) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ #) => eapply @monmor_sgmor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ #) => eapply @srngmor_mult_mor : typeclass_instances.

Hint Extern 2 (SemiRng_Morphism _ _ (ℰ _ _)) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ (ℰ _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (ℰ _ _)) => eapply @monmor_sgmor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (ℰ _ _)) => eapply @srngmor_mult_mor : typeclass_instances.

Instance evaluable_in_comring `{Setoid (S:=R)} `{S:set} `{CommutativeSemiRing _ (R:=S)}
  (φ: R ⇀ S) `{!Morphism (R ⇒ S) φ} a `{a ∊ S}
  : Polynomial_Evaluable φ a.
Proof. intros. intros r ?. exact (commutativity (.*.) _ _). Qed.

Instance: ∀ `{Setoid (S:=R)} `{S:set} `{SemiRing _ (R:=S)} (φ: R ⇀ S) `{!Morphism (R ⇒ S) φ},
  Polynomial_Evaluable φ 0.
Proof. intros. intros r ?. now rewrite (_ $ mult_0_l _), (_ $ mult_0_r _). Qed.

Instance: ∀ `{Setoid (S:=R)} `{S:set} `{SemiRing _ (R:=S)} (φ: R ⇀ S) `{!Morphism (R ⇒ S) φ},
  Polynomial_Evaluable φ 1.
Proof. intros. intros r ?. now rewrite (_ $ mult_1_l _), (_ $ mult_1_r _). Qed.

Section hints.
  Context `{Polynomial_Ring A (R:=R) (P:=P)}.

  Instance poly_ring_inject_mor_plain: Morphism (R ⇒ P) # := sgmor_subsetmor.

  Context `{S:set} `{SemiRing _ (R:=S)} (φ:R ⇀ S) `{!SemiRing_Morphism R S φ}
                       a `{a ∊ S} `{!Polynomial_Evaluable φ a} .

  Instance polynomial_eval_mor_plain : Morphism (P ⇒ S) (ℰ  φ a) := sgmor_subsetmor.
End hints.

Hint Extern 2 (Morphism _ #) => eapply @poly_ring_inject_mor_plain : typeclass_instances.
Hint Extern 2 (Morphism _ (ℰ _ _)) => eapply @polynomial_eval_mor_plain : typeclass_instances.

Lemma poly_eval_self `{Polynomial_Ring (R:=R) (P:=P)} : ℰ # x = (id:P⇀P) .
Proof. subsymmetry. apply (polynomial_eval_unique # x _); subreflexivity. Qed.

Section between_poly_rings_surjective.
  Context `{Polynomial_Ring (R:=R) (P:=P₁)}.
  Context `{Polynomial_Ring (B:=_) (Bplus:=_) (Bmult:=_) (Bzero:=_) (Bone:=_) (Bnegate:=_) (Be:=_)
                            (R:=R) (P:=P₂)} .

  Section another_ring.
    Context `{S:set} `{SemiRing _ (R:=S)} (φ:R ⇀ S) `{!SemiRing_Morphism R S φ} .

    Lemma another_poly_ring_eval a `{a ∊ S} `{!Polynomial_Evaluable φ a}
      : ℰ (P:=P₁) φ a = ℰ (P:=P₂) φ a ∘ ℰ (P:=P₁) # x.
    Proof. subsymmetry. apply (polynomial_eval_unique _ _). apply _.
    + match goal with |- ?f ∘ ?g ∘ ?h = ?k  => change (f ∘ (g ∘ h) = k) end.
      pose proof (polynomial_eval_const (P:=P₁) # (x:P₂)) as E. rewrite E.
      exact (polynomial_eval_const _ _).
    + unfold compose.
      pose proof (polynomial_eval_var (P:=P₁) # (x:P₂)) as E. rewrite (_ $ E).
      exact (polynomial_eval_var _ _).
    Qed.
  End another_ring.

  Instance poly_ring_to_poly_ring_inv : Inverse (ℰ (P:=P₂) # (x:P₁)) := (ℰ (P:=P₁) # (x:P₂)) .

  Instance poly_ring_to_poly_ring_surj : Surjective P₂ P₁ (ℰ (P:=P₂) # x).
  Proof. split; unfold inverse, poly_ring_to_poly_ring_inv; try apply _.
    rewrite <-poly_eval_self. subsymmetry.
    apply (another_poly_ring_eval _ _).
  Qed.

  Instance poly_ring_to_poly_ring_modmor : Module_Morphism R P₁ P₂ (ℰ (P:=P₁) # x) .
  Proof. split; try apply _. intros r ? p ?.
    rewrite 2!(_ $ poly_ring_dot_def _ _).
    rewrite (_ $ preserves_mult _ _).
    pose proof (polynomial_eval_const (P:=P₁) # (x:P₂) _ _ (_:Proper (R,=) r)) as E.
    now setoid_rewrite E.
  Qed.
End between_poly_rings_surjective.
Arguments another_poly_ring_eval {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R} P₁ {_ _ _ _ _ _ _ _ _ _ _ _} P₂ {_ _ _ _} {_ S _ _ _ _ _ _} φ {_} a {_ _} _ _ _.

Hint Extern 2 (Inverse (ℰ # x)) => eapply @poly_ring_to_poly_ring_inv : typeclass_instances.
Hint Extern 2 (Module_Morphism _ _ _ (ℰ # x)) => eapply @poly_ring_to_poly_ring_modmor : typeclass_instances.

Section poly_rings_bijective.
  Context `{Polynomial_Ring (R:=R) (P:=P₁)}.
  Context `{Polynomial_Ring (B:=_) (Bplus:=_) (Bmult:=_) (Bzero:=_) (Bone:=_) (Bnegate:=_) (Be:=_)
                            (R:=R) (P:=P₂)} .

  Existing Instance poly_ring_to_poly_ring_surj.

  Instance poly_rings_bijective: Bijective P₁ P₂ (ℰ (P:=P₁) # x).
  Proof. apply (alt_Build_Bijective _);
    unfold inverse, poly_ring_to_poly_ring_inv; try apply _;
    apply surjective; apply _.
  Qed.
End poly_rings_bijective.

Hint Extern 2 (Bijective ?P₁ ?P₂ (ℰ # x)) => class_apply (poly_rings_bijective (P₁:=P₁) (P₂:=P₂)) : typeclass_instances.

Section eval.
  Context `{Polynomial_Ring (R:=R) (P:=P)}.

  Instance poly_ring_inject_injective: Injective R P #.
  Proof. split; try apply _. intros a ? b ? E.
    setoid_rewrite <-( polynomial_eval_const (id:R⇀R) 0 _ _ (_ : Proper (R,=) a) ).
    setoid_rewrite <-( polynomial_eval_const (id:R⇀R) 0 _ _ (_ : Proper (R,=) b) ).
    unfold compose. now rewrite (_ $ E).
  Qed.

  Section another_ring.
    Context `{S:set} `{SemiRing _ (R:=S)} (φ:R ⇀ S) `{!SemiRing_Morphism R S φ} .

    Lemma polynomial_eval_proper a `{a ∊ S} `{!Polynomial_Evaluable φ a} b `{b ∊ S}
      : a = b → ℰ (P:=P) φ a = ℰ (P:=P) φ b .
    Proof. intro E.
      assert (Polynomial_Evaluable φ b). intros r ?. rewrite <-(_ $ E).
        exact (polynomial_evaluable φ r).
      rewrite 2!(_ $ another_poly_ring_eval P (Poly R) _ _).
      cut (ℰ (P:=Poly R) φ a = ℰ φ b).
        intro E2. rewrite E2. subreflexivity.
      unfold polynomial_eval, poly_polynomial_ring_eval.
      rewrite (_ $ E). subreflexivity.
    Qed.
  End another_ring.

End eval.
Hint Extern 2 (Injective _ _ #) => eapply @poly_ring_inject_injective : typeclass_instances.

Notation ZA := BinNums.Z.
Notation Z := (every ZA).

Class PolynomialCoefficient `(R:set) `(P:set) := polynomial_coef : ZA → P ⇀ R .
Local Notation "[ p ]_ i" := (polynomial_coef i p) (at level 1, format "[ p ]_ i").

Section coef_spec.
  Context `{Polynomial_Ring (R:=R) (P:=P)}.
  Context {coef:PolynomialCoefficient R P}.

  Class PolynomialCoefficientSpec : Prop :=
  { polynomial_coef_modmor i : Module_Morphism R P R (polynomial_coef i)
  ; polynomial_coef_one j : [1]_j = δ j 0
  ; polynomial_coef_shift i p `{p ∊ P} : [x*p]_(1+i) = [p]_i
  }.
End coef_spec.
Arguments PolynomialCoefficientSpec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} R P {_ _}.

Hint Extern 2 (Module_Morphism _ _ _ (polynomial_coef _)) => eapply @polynomial_coef_modmor : typeclass_instances.

Section default_coefficient.
  Context `{Polynomial_Ring A (R:=R) (P:=P)}.

  Instance coefficient_default : PolynomialCoefficient R P
    := λ i, (λ p, coef p i) ∘ (ℰ # (x:Poly R)).

  Instance coefficient_default_spec:
    PolynomialCoefficientSpec R P (coef:=coefficient_default).
  Proof. unfold coefficient_default. split; unfold polynomial_coef.
  + intros i. apply _.
  + intros j. unfold compose. now rewrite (_ $ preserves_1).
  + intros i p ?. unfold compose.
    rewrite (_ $ preserves_mult _ _).
    set (q:=ℰ # x p). assert (q ∊ Poly R) by (subst q; apply _).
    pose proof (polynomial_eval_var (P:=P) (to_polynomial_ring (Poly R)) x) as E.
    rewrite (Poly R $ E). simpl.
    destruct (nonneg_or_neg i).
    * assert (1 < 1 + (1 + i)) as Ei by apply (pos_plus_lt_compat_r _ _).
      rewrite (_ $ sum_delta_l_0 (λ k, coef q (1 + i - k)) _ _ Ei).
      now eq_replace (1+i-1) with i by setring (Z).
    * rewrite (_ $ poly_coef_neg _ _).
      apply (sum_delta_l_zero_r (λ k, coef q (1 + i - k))).
      apply (lt_iff_S_le _ _). apply (flip_neg_minus _ _).
      now eq_replace (1+i-1) with i by setring (Z).
  Qed.

  Definition deg_le p n := ∀ i, n<i → [p]_i = 0 .
  Definition deg_eq `{UnEq A} p n := deg_le p n ∧ [p]_n ≠ 0 .
  Definition monic_of_deg p n := deg_le p n ∧ [p]_n = 1 .
  Definition monic p := ∃ `{n ∊ Z⁺}, monic_of_deg p n .

  Instance: ∀ i `{i ∊ Z}, Module_Morphism R P R (polynomial_coef i) := λ i _, _.

  Lemma deg_le_proper p `{p ∊ P} q `{q ∊ P} n : p = q → deg_le p n ↔ deg_le q n.
  Proof. intros E. split; intros P' i Ei; [ rewrite <-(P $ E) | rewrite (P $ E) ]; exact (P' i Ei). Qed.

  Lemma deg_le_weaken p `{p ∊ P} n m : deg_le p n → n ≤ m → deg_le p m .
  Proof. intros Ep Enm i Ei. apply (Ep i). now apply (le_lt_trans _ m _). Qed.

  Lemma deg_le_plus p `{p ∊ P} q `{q ∊ P} n : deg_le p n → deg_le q n → deg_le (p+q) n .
  Proof. intros Ep Eq i Ei. rewrite (_ $ preserves_plus _ _).
    rewrite (_ $ Ep i Ei), (_ $ plus_0_l _). exact (Eq i Ei).
  Qed.

  Lemma deg_le_negate p `{p ∊ P} n : deg_le p n → deg_le (-p) n .
  Proof. intros Ep i Ei. rewrite (_ $ preserves_negate _).
    rewrite (_ $ Ep i Ei). exact negate_0.
  Qed.

  Lemma deg_le_mult p `{p ∊ P} n q `{q ∊ P} m : deg_le p n → deg_le q m → deg_le (p*q) (n+m).
  Proof. intros Ep Eq i Ei. unfold polynomial_coef, coefficient_default, compose.
    rewrite (_ $ preserves_mult _ _).
    change (∑_(k < 1 + i) [p]_k * [q]_(i-k) = 0).
    apply (sum_of_zero_alt _ _). intros k ? Ek.
    destruct (le_or_lt k n) as [Ekn|Ekn].
      cut (m<i-k). intro Em. rewrite (_ $ Eq (i-k) Em). exact (mult_0_r _).
      eq_replace m with (-n+(n+m)) by setring (Z).
      eq_replace (i-k) with (-k+i) by setring (Z).
      apply (plus_le_lt_compat _ _ _ _); trivial.
      now apply (flip_le_negate _ _).
    rewrite (_ $ Ep _ Ekn). exact (mult_0_l _).
  Qed.

  Lemma deg_le_dot p `{p ∊ P} n a `{a ∊ R} : deg_le p n → deg_le (a · p) n .
  Proof. intros Ep i Ei. rewrite (_ $ preserves_dot _ _).
    rewrite (_ $ Ep i Ei). exact (dot_0_r _).
  Qed.

End default_coefficient.
Hint Extern 2 (PolynomialCoefficientSpec _ _ (coef:=coefficient_default)) =>
  eapply @coefficient_default_spec : typeclass_instances.

Section coefficient.
  Context `{Polynomial_Ring A (R:=R) (P:=P)}.
  Context {cf:PolynomialCoefficient R P} `{!PolynomialCoefficientSpec R P}.

  Instance: ∀ i `{i ∊ Z}, Module_Morphism R P R (polynomial_coef i) := λ i _, _.

  Lemma monomial_coefficient `{!NonnegIntPowSpec P Z pw} n {eln:n ∊ Z⁺} i : [x^n]_i = δ i n .
  Proof. revert i. ZPlus_induction n.
  + intros i. rewrite (_ $ nonneg_int_pow_0 _). apply polynomial_coef_one.
  + intros i. rewrite (_ $ nonneg_int_pow_S _ _).
    pose proof (plus_negate_r_split_alt 1 i) as Ei. rewrite <-(to_eq Ei) at 1. clear Ei.
    rewrite (_ $ polynomial_coef_shift _ _).
    rewrite (_ $ IH (i-1)).
    apply (kronecker_delta_shift _ _ _ _).
    split; intro E; [rewrite <-(_ $ E) | rewrite (_ $ E) ]; setring (Z).
  Qed.

  Lemma polynomial_coef_1_0 : [1]_0 = 1.
  Proof. rewrite (_ $ polynomial_coef_one 0). exact (kronecker_delta_diag _). Qed.

  Lemma polynomial_coef_1_nz n `{n ∊ Z ₀} : [1]_n = 0.
  Proof. rewrite (_ $ polynomial_coef_one n).
    apply (kronecker_delta_uneq _ _). now destruct (_ : n ∊ Z ₀).
  Qed.

  Lemma polynomial_coef_1_pos n `{n ∊ Z₊} : [1]_n = 0.
  Proof polynomial_coef_1_nz n. 

  Lemma polynomial_coef_const_0 c `{c ∊ R} : [#c]_0 = c.
  Proof. rewrite <-(_ $ mult_1_r (#c)), <-(_ $ poly_ring_dot_def _ _).
     rewrite (_ $ preserves_dot _ _), (_ $ polynomial_coef_1_0). unfold dot.
     exact (mult_1_r _).
  Qed.

  Lemma polynomial_coef_const_nz c `{c ∊ R} n `{n ∊ Z ₀} : [#c]_n = 0.
  Proof. rewrite <-(_ $ mult_1_r (#c)), <-(_ $ poly_ring_dot_def _ _).
     rewrite (_ $ preserves_dot _ _), (_ $ polynomial_coef_1_nz _). unfold dot.
     exact (mult_0_r _).
  Qed.

  Lemma polynomial_coef_const_pos c `{c ∊ R} n `{n ∊ Z₊} : [#c]_n = 0.
  Proof polynomial_coef_const_nz c n.

  Lemma polynomial_coef_x_0 : [x]_0 = 0.
  Proof. rewrite <-(_ $ mult_1_r x).
    eq_replace (0:ZA) with (1+(-1):ZA) by setring (Z).
    rewrite (_ $ polynomial_coef_shift _ _).
    pose proof _ : -1 ∊ Z₋ .
    exact (polynomial_coef_1_nz (-1)).
  Qed.

  Lemma polynomial_coef_x_1 : [x]_1 = 1.
  Proof. rewrite <-(_ $ mult_1_r x).
    eq_replace (1:ZA) with (1+0:ZA) by setring (Z).
    rewrite (_ $ polynomial_coef_shift _ _).
    exact (polynomial_coef_1_0).
  Qed.

  Section unique.
    Hint Extern 2 (Pow T ZA) => eapply (nonneg_int_pow_default Z) : typeclass_instances.
    Instance: NonnegIntPowSpec P Z _ := _.

    Lemma coefficient_unique i : (polynomial_coef i : P ⇀ R) = coefficient_default i.
    Proof. unfold coefficient_default.
      intros p q Ep. unfold_sigs. red_sig. unfold compose.
      rewrite <-(_ $ Ep). clear dependent q.
      pose proof  bijective_applied (ℰ (P:=P) # (x:Poly R)) p as E.
        rewrite <-(_ $ E) at 1. clear E.
      set (q := ℰ (P:=P) # (x:Poly R) p). assert (q ∊ Poly R). subst q. apply _.
      unfold inverse, poly_ring_to_poly_ring_inv.
      rewrite (_ $ poly_expand q) at 1.
      rewrite 2!(_ $ preserves_sum_range _ _ _ _).
      subtransitivity (∑_(k < len q) coef q k * δ k i).
        apply (sum_range_proper_0 _ _ _). intros k ??.
        rewrite 2!(_ $ preserves_dot _ _). unfold dot.
        pose proof (preserves_nat_pow (N:=Z⁺) (f:=ℰ (P:=Poly R) # (x:P)) x k) as E. rewrite (_ $ E). clear E.
        pose proof (polynomial_eval_var (P:=Poly R) (to_polynomial_ring P) x) as E. rewrite (P $ E). clear E.
        rewrite (_ $ monomial_coefficient k i).
        now rewrite (_ $ kronecker_delta_sym _ _).
      destruct (nonneg_or_neg i).
        destruct (le_or_lt (len q) i) as [E|E].
          now rewrite (_ $ sum_delta_r_zero_r (coef q) 0 _ _ E), (_ $ poly_coef_after _ _ E).
        now apply (sum_delta_r_0 (coef q) (len q) _).
      rewrite (_ $ poly_coef_neg _ _).
      apply (sum_delta_r_zero_l (coef q)). apply (_ : i ∊ Z₋).
    Qed.
  End unique.

  Lemma deg_le_coef p `{p ∊ P} n : deg_le p n → ∀ i, n<i → [p]_i = 0 .
  Proof. intros P' i E. rewrite (coefficient_unique i p p (_ : Proper (P,=) p)). exact (P' i E). Qed.

  Lemma deg_le_coef_iff p `{p ∊ P} n : deg_le p n ↔ ∀ i, n<i → [p]_i = 0 .
  Proof. split. exact (deg_le_coef _ _). intros P' i E.
    rewrite <-(coefficient_unique i p p (_ : Proper (P,=) p)). exact (P' i E).
  Qed.

  Lemma monic_of_deg_alt p `{p ∊ P} n : monic_of_deg p n → deg_le p n ∧ [p]_n = 1 .
  Proof. intros [??]. intuition. now rewrite (coefficient_unique n p p (_ : Proper (P,=) p)). Qed.

  Lemma monic_alt p `{p ∊ P} : monic p → ∃ `{n ∊ Z⁺}, deg_le p n ∧ [p]_n = 1 .
  Proof. intros [n[??]]. exists_sub n. now apply monic_of_deg_alt. Qed.

  Context {pw:Pow T ZA} `{!NonnegIntPowSpec P Z pw}.

  Lemma polynomial_expand p `{p ∊ P}
    : ∃ `{n ∊ Z⁺}, p = ∑_(i < n) [p]_i · x^i .
  Proof. exists_sub (len (ℰ (P:=P) # (x:Poly R) p)).
    pose proof  bijective_applied (ℰ (P:=P) # (x:Poly R)) p as E.
    unfold inverse, poly_ring_to_poly_ring_inv in E.
    rewrite <-(_ $ E) at 1.
    set (q:=ℰ (P:=P) # (x:Poly R) p). assert (q ∊ Poly R). subst q. apply _.
    rewrite (_ $ poly_expand q) at 1.
    rewrite (_ $ preserves_sum_range _ _ _ _).
    apply (sum_range_proper_0 _ _ _). intros i ??.
    rewrite (_ $ preserves_dot _ _).
    rewrite (_ $ preserves_nat_pow (N:=Z⁺) _ _).
    pose proof (polynomial_eval_var (P:=Poly R) # (x:P)) as E2. rewrite (_ $ E2). clear E2.
    cut (coef q i = [p]_i). intro E2. now rewrite (_ $ E2).
    rewrite (coefficient_unique i _ _ (_:Proper (P,=) p)).
    unfold coefficient_default, compose. now fold q.
  Qed.

  Lemma coef_neg p `{p ∊ P} i `{i ∊ Z₋} : [p]_i = 0.
  Proof. destruct (polynomial_expand p) as [m[mel E]]. rewrite (_ $ E).
    rewrite (_ $ preserves_sum_range _ _ _ _).
    apply (sum_of_zero_alt _). intros j ? _.
    rewrite (_ $ preserves_dot _ _).
    rewrite (_ $  monomial_coefficient j i).
    assert (i<j) as Eij. apply (lt_le_trans _ 0 _).
      now destruct (_ : i ∊ Z₋). now destruct (_ : j ∊ Z⁺).
    rewrite (_ $ kronecker_delta_lt _ _ Eij).
    exact (dot_0_r _).
  Qed.

  Lemma deg_le_expand p `{p ∊ P} n : deg_le p n ↔ p = ∑_(i < 1+n) [p]_i · x^i .
  Proof. revert n. cut (∀ n, p = ∑_(i < 1 + n) [p]_i · x ^ i → deg_le p n). intros Pdeg n. split. 2:apply Pdeg.
  + intros Ec. destruct (polynomial_expand p) as [m[mel E]]. rewrite (_ $ E).
    destruct (total le m (1+n)) as [Em|Em].
    * destruct (decompose_le Em) as [a[ael Ea]]. rewrite (to_eq Ea).
      subsymmetry. subtransitivity (∑_(i < m) [p]_i · x ^ i + ∑_(m ≤ i < m + a) [p]_i · x ^ i).
        apply (sum_split_0 _ _ _).
      cut (∑_(m ≤ i < m + a) [p]_i · x ^ i = 0).
        intro E'. now rewrite (_ $ E'), (_ $ plus_0_r _).
      apply (sum_of_zero _ _). intros i [Ei _].
      rewrite (le_iff_lt_plus_1 _ _) in Ei. rewrite <-(flip_lt_minus_l _ _ _) in Ei.
      cut ([p]_i = 0). intro E'. rewrite (_ $ E'). exact (dot_0_l _).
      apply (deg_le_coef p (m-1)); trivial. clear dependent i.
      apply Pdeg. now eq_replace (1+(m-1)) with m by setring (Z).
    * destruct (nonneg_or_neg n).
        destruct (decompose_le Em) as [a[ael Ea]]. rewrite (to_eq Ea).
        subtransitivity (∑_(i < 1+n) [p]_i · x ^ i + ∑_(1+n ≤ i < 1+n + a) [p]_i · x ^ i).
          apply (sum_split_0 _ _ _).
        cut (∑_(1+n ≤ i < 1+n + a) [p]_i · x ^ i = 0).
        intro E'. now rewrite (_ $ E'), (_ $ plus_0_r _).
        apply (sum_of_zero _ _). intros i [Ei _].
        rewrite <-(lt_iff_S_le _ _) in Ei.
        rewrite (_ $ deg_le_coef _ _ Ec _ Ei). exact (dot_0_l _).
      assert (∀ i, 0 ≤ i → n < i) as Pi. intros i ?.
        apply (lt_le_trans _ 0 _); trivial. now destruct (_ :  n ∊ Z₋).
      subtransitivity 0; [| subsymmetry]; apply (sum_of_zero _ _); intros i [Ei _];
        rewrite (_ $ deg_le_coef p n Ec i (Pi i Ei));
        exact (dot_0_l _).
  + intros n E. apply (deg_le_coef_iff _ _). intros i Ei.
    rewrite (_ $ E).
    rewrite (_ $ preserves_sum_range _ _ _ _).
    apply (sum_of_zero_alt _). intros j ? Ej.
    rewrite (_ $ preserves_dot _ _).
    rewrite (_ $  monomial_coefficient j i).
    rewrite <-(le_iff_lt_S _ _) in Ej.
    assert (j<i) as Eij. now apply (le_lt_trans _ n _).
    rewrite (_ $ kronecker_delta_gt _ _ Eij).
    exact (dot_0_r _).
  Qed.

  Lemma poly_split p `{p ∊ P} n `{n ∊ Z⁺} : deg_le p n →
    ∃ `{q ∊ P}, p = [p]_n · x^n + q ∧ deg_le q (n-1).
  Proof. intro Ep. rewrite (deg_le_expand p n) in Ep.
    exists_sub (∑_(i < n) [p]_i · x ^ i). split.
    + rewrite (_ $ commutativity (+) _ _), (_ $ Ep) at 1.
      exact (sum_split_r_0 (fun i => [p]_i · x ^ i) n).
    + apply (deg_le_coef_iff _). intros j Ej.
      rewrite (_ $ preserves_sum_range _ _ _ _).
      apply (sum_of_zero_alt _). intros i ? Ei.
      rewrite (_ $ preserves_dot _ _).
      rewrite (_ $  monomial_coefficient i j).
      assert (i<j) as Eij. apply (lt_le_trans _ n _); trivial.
        apply (le_iff_lt_plus_1 _ _). now apply (flip_lt_minus_l _ _ _).
      rewrite (_ $ kronecker_delta_gt j i Eij). exact (dot_0_r _).
  Qed.

End coefficient.

Section more_deg_le.
  Context `{Polynomial_Ring A (R:=R) (P:=P)}.

  (* Add Ring P : (stdlib_ring_theory P) *)

  Hint Extern 2 (PolynomialCoefficient _ _) => eapply coefficient_default : typeclass_instances.
  Instance: PolynomialCoefficientSpec R P := _.

  Instance: ∀ i `{i ∊ Z}, Module_Morphism R P R (polynomial_coef i) := λ i _, _.

  Lemma deg_le_monomial `{!NonnegIntPowSpec P Z pw} n {eln:n ∊ Z⁺} : deg_le (x^n) n .
  Proof. intros i Ei.
    rewrite (_ $ monomial_coefficient (R:=R) (P:=P) n i).
    now apply (kronecker_delta_gt _ _).
  Qed.

  Hint Extern 2 (Pow T ZA) => eapply (nonneg_int_pow_default Z) : typeclass_instances.
  Instance: NonnegIntPowSpec P Z _ := _.

  Lemma deg_le_bound p `{p ∊ P} : ∃ n, deg_le p n.
  Proof. destruct (polynomial_expand p) as [n[eln E]].
    exists (n-1). apply (deg_le_expand p).
    now eq_replace (1+(n-1)) with n by setring (Z).
  Qed.

  Lemma deg_le_x : deg_le x 1 .
  Proof. pose proof (nonneg_int_pow_1 (R:=P) (Z:=Z) x) as E.
    apply (deg_le_proper (R:=R) (P:=P) _ _ 1 E).
    apply (deg_le_monomial _).
  Qed.

  Lemma deg_le_1 : deg_le 1 0 .
  Proof. pose proof (nonneg_int_pow_0 (R:=P) (Z:=Z) x) as E.
    apply (deg_le_proper (R:=R) (P:=P) _ _ 0 E).
    apply (deg_le_monomial _).
  Qed.

  Lemma deg_le_const p `{p ∊ P} : deg_le p 0 ↔ ∃ `{c ∊ R}, p = # c .
  Proof. rewrite (deg_le_expand _ _).
    rewrite (_ $ sum_split_l_0 _ _), (_ $ sum_empty_plus_0 _ _), (_ $ plus_0_r _).
    rewrite (_ $ nonneg_int_pow_0 _), (_ $ poly_ring_dot_def _ _), (_ $ mult_1_r _).
    split. now exists_sub [p]_0. intros [c[? E]].
    cut ([p]_0 = c). intro E2. now rewrite (_ $ E2).
    rewrite (_ $ E). exact (polynomial_coef_const_0 _).
  Qed.

  Lemma deg_le_linear p `{p ∊ P} : deg_le p 1 ↔ ∃ `{a ∊ R} `{b ∊ R}, p = a · x + # b .
  Proof. rewrite (deg_le_expand _ _).
    rewrite (_ $ sum_split_r_0 _ _), (_ $ sum_split_l_0 _ _).
    assert (1 ≤ 1) as E by easy.
    rewrite (_ $ sum_empty_le _ 1 1 E), (_ $ plus_0_r _). clear E.
    rewrite (_ $ nonneg_int_pow_0 _), (_ $ poly_ring_dot_def _ 1), (_ $ mult_1_r _).
    rewrite (_ $ nonneg_int_pow_1 _).
    rewrite (_ $ commutativity (+) (#[p]_0) _).
    split. now exists_sub [p]_1 [p]_0. intros [a[ela[b[elb E]]]].
    cut ([p]_1 = a ∧ [p]_0 = b). intros [E1 E2]. now rewrite (_ $ E1), (_ $ E2).
    split; rewrite (_ $ E), (_ $ preserves_plus _ _), (_ $ preserves_dot _ _); unfold dot.
      rewrite (_ $ polynomial_coef_const_nz _ _).
      rewrite (_ $ polynomial_coef_x_1 (R:=R) (P:=P)).
      rewrite (_ $ plus_0_r _).
      exact (mult_1_r _).
    rewrite (_ $ polynomial_coef_x_0 (R:=R) (P:=P)), (_ $ mult_0_r _), (_ $ plus_0_l _).
    exact (polynomial_coef_const_0 _).
  Qed.

  Lemma x_sqr_plus_1_monic : monic_of_deg (x*x+1) 2.
  Proof. split.
  + apply (deg_le_plus _ _). 
      apply (deg_le_mult _ _ _ _); apply deg_le_x.
    apply (deg_le_weaken _) with 0. apply deg_le_1. exact (le_0_2).
  + rewrite (_ $ preserves_plus _ _).
    pose proof (nonneg_int_pow_2 (R:=P) (Z:=Z) x) as E.
    rewrite <-(_ $ E), (_ $ monomial_coefficient (R:=R) (P:=P) 2 2).
    rewrite (_ $ polynomial_coef_one _).
    rewrite (_ $ kronecker_delta_diag _).
    rewrite (_ $ kronecker_delta_gt 2 0 (lt_0_2)).
    exact (plus_0_r _).
  Qed.

End more_deg_le.

Section division.
  Context `{Polynomial_Ring B (R:=R) (P:=P)}.

  Add Ring P : (stdlib_ring_theory P).

  Hint Extern 2 (PolynomialCoefficient _ _) => eapply coefficient_default : typeclass_instances.
  Instance: PolynomialCoefficientSpec R P := _.

  Hint Extern 2 (Pow _ ZA) => eapply (nonneg_int_pow_default Z) : typeclass_instances.
  Instance: NonnegIntPowSpec P Z _ := _.

  Instance: ∀ i `{i ∊ Z}, Module_Morphism R P R (polynomial_coef i) := λ i _, _.

  Lemma poly_div_monic f {elf: f ∊ P} g `{g ∊ P} n `{n ∊ Z⁺} : monic_of_deg g n
    → ∃ `{q ∊ P} `{r ∊ P}, f = q * g + r ∧ deg_le r (n-1) .
  Proof. intros Pm. apply (monic_of_deg_alt _) in Pm. destruct Pm as [Edg Egn].
    destruct (poly_split g n Edg) as [g'[elg' [Eg' Edg']]].
    rewrite (_ $ Egn), (_ $ lm_identity _) in Eg'.
    destruct (deg_le_bound f) as [m Edf].
    destruct (le_or_lt (n-1) m) as [Enm|Enm].
    + destruct (decompose_le Enm) as [a[ela Ea]].
      rewrite (to_eq Ea) in Edf. clear dependent m.
      revert f elf Edf. ZPlus_induction a; intros f ? Edf.
      * exists_sub 0 f. split. setring P.
        now eq_replace (n-1+0) with (n-1) in Edf by setring (Z).
      * eq_replace (n-1+(1+a)) with (n+a) in Edf by setring (Z).
        destruct (poly_split f _ Edf) as [f'[elf' [Ef' Edf']]].
        destruct (IH (f' - ([f]_(n+a) · x^a) * g') _) as [q'[elq'[r'[elr' [E Edr']]]]].
          apply (deg_le_plus _ _ _).
            now eq_replace (n-1+a) with (n+a-1) by setring (Z).
          apply (deg_le_negate _ _).
          eq_replace (n-1+a) with (a+(n-1)) by setring (Z).
          apply (deg_le_mult _ _ _ _); trivial.
          apply (deg_le_dot _ _ _). apply (deg_le_monomial _).
        exists_sub ([f]_(n+a) · x^a + q') r'. intuition.
        subtransitivity ([f]_(n+a) · x^a * g + (q' * g + r')). 2: setring P.
        rewrite <-(_ $ E), (_ $ Eg').
        subtransitivity ([f]_(n + a) · x ^ (n + a) + f'). trivial.
        rewrite (P $ nonneg_int_pow_exp_plus x n a).
        rewrite (_ $ commutativity (.*.) (x^n) (x^a)).
        rewrite (_ $ aa_linear_l _ _ _).
        set (q := [f]_(n + a) · x ^ a ). assert (q ∊ P). unfold q. apply _.
        set (xn := x^n). assert (xn ∊ P). unfold xn. apply _.
        setring P.
    + exists_sub 0 f. split. setring P.
      apply deg_le_weaken with m; trivial. now apply (lt_le _ _).
  Qed.
End division.
