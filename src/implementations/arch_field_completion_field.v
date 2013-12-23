Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_fields interfaces.metric_spaces
  interfaces.rationals the_ae_rationals
  theory.setoids theory.products theory.fields
  metric.metric_spaces metric.totally_bounded metric.maps_continuous
  metric.prelength metric.products
  cauchy_completion metric.complete metric.continuity
  metric.archimedean_fields.
Require Export
  arch_field_completion_ops.

Local Open Scope grp_scope.

Section contents.
  Context `{ArchimedeanField A1 (F:=F)} `{Ball F} `{!ArchimedeanField_Metric F}.
  Context `{R:@set A2} {Re:Equiv R} {Rue:UnEq R} {Rball:Ball R} {Rlimit:Limit R}.
  Context `{!ToCompletion F R} `{!Completion F R} `{!MetricInequality R}.

  Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.

  Notation "#" := (to_completion F R).

  Instance: FinitePoints R := finite_points_completion.
  Instance: LocatedPoints R := located_points_completion.
  Instance: StrongSetoid R := metric_inequality_strong_setoid.
  Instance: LocallyTotallyBounded R := locally_totally_bounded_completion.

  Instance: StrongInjective F R #. Proof isometry_str_injective _.
  Instance: Strong_Morphism F R #. Proof strong_injective_mor _.

  Hint Extern 0 (Zero   A2) => eexact (Creals_zero   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (One    A2) => eexact (Creals_one    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Negate A2) => eexact (Creals_negate (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Plus   A2) => eexact (Creals_plus   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Mult   A2) => eexact (Creals_mult   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Inv    A2) => eexact (Creals_inv    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Zero   (elt_type R)) => eexact (Creals_zero   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (One    (elt_type R)) => eexact (Creals_one    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Negate (elt_type R)) => eexact (Creals_negate (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Plus   (elt_type R)) => eexact (Creals_plus   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Mult   (elt_type R)) => eexact (Creals_mult   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Inv    (elt_type R)) => eexact (Creals_inv    (F:=F) (R:=R)) : typeclass_instances.

  Instance: 0 ∊ R := _ : # 0 ∊ R.
  Instance: 1 ∊ R := _ : # 1 ∊ R.

  Instance: Morphism (R ⇒ R) (-) := _ : Morphism (R ⇒ R) (ufm_completion_map (-)).
  Instance Creals_negate_iso: Isometry R R (-) := _ : Isometry R R (ufm_completion_map (-)).
  Instance: ClosedFun (R ⇀ R) (-) := morphism_closed _.
  Hint Extern 5 (- _ ∊ R) => eapply (_ : ClosedFun (R ⇀ R) (-)) : typeclass_instances.

  Instance Creals_plus_cont: UniformlyContinuous (R*R) R (uncurry (+) : R*R ⇀ R).
  Proof. pose proof _ : UniformlyContinuous (R*R) R (ufm_completion_map (uncurry (+) : F*F ⇀ F)).
    cut (@equiv _ (ext_equiv (X:=R*R) (Y:=R)) (ufm_completion_map (uncurry (+) : F*F ⇀ F)) (uncurry (+))).
      intro E. now rewrite <-E.
    intros ?? E. unfold plus at 2. unfold Creals_plus.
    unfold_sigs. red_sig. rewrite (R*R $ E).
    destruct y as [??]. now unfold uncurry, curry.
  Qed.

  Instance: Morphism (R ⇒ R ⇒ R) (+). Proof. unfold plus, Creals_plus. apply _. Qed.
  Instance: ClosedFun (R ⇀ R ⇀ R) (+) := binary_morphism_closed _.
  Hint Extern 5 (_ + _ ∊ R) => eapply (_ : ClosedFun (R ⇀ R ⇀ R) (+)) : typeclass_instances.

  Notation mult_ext := (continuous_extension (to_completion (F*F) (R*R)) # (F*F) F (uncurry (.*.)): R*R ⇀ R).
  Instance Creals_mult_cont: Continuous (R*R) R (uncurry (.*.) : R*R ⇀ R).
  Proof. cut (Continuous (R*R) R mult_ext).
      intro.
      assert (@equiv _ (ext_equiv (X:=R*R) (Y:=R)) mult_ext (uncurry mult)) as E.
       intros ?? E. unfold mult at 2. unfold Creals_mult.
       unfold_sigs. red_sig. rewrite (R*R $ E).
       destruct y as [??]. now unfold uncurry, curry.
      rewrite <-E. apply _.
    apply (continuous_dom_ran_proper).
    apply (cont_ext_cont _ _ _ _ _).
    exact (ext_domain_ambient _).
    exact (ext_domain_ambient _).
  Qed.

  Instance: Morphism (R ⇒ R ⇒ R) (.*.).
  Proof. replace (mult: R ⇀ R ⇀ R) with (curry (uncurry (mult: R ⇀ R ⇀ R))) by reflexivity. apply _. Qed.
  Instance: ClosedFun (R ⇀ R ⇀ R) (.*.) := binary_morphism_closed _.
  Hint Extern 5 (_ * _ ∊ R) => eapply (_ : ClosedFun (R ⇀ R ⇀ R) (.*.)) : typeclass_instances.

  Lemma nonzero_ext : -closure #⁺¹(∼ F ₀) = R ₀ .
  Proof. rewrite <-zero_is_complement.
    cut (#⁺¹({{0}}) = {{0}}). intro E.
      now rewrite E, (closure_singleton _), nonzero_is_metric_complement.
    split.
      intros [?[? [[? E1] E2]]]. split. apply _. rewrite (_ $ E1) in E2. subsymmetry.
      intros [? E]. split. apply _. exists (0:F). exists (_ : (0:F) ∊ {{0}}) . subsymmetry.
  Qed.

  Instance Creals_inv_cont: Continuous (R ₀) (R ₀) (⁻¹).
  Proof.
    apply (continuous_dom_ran_proper (-closure #⁺¹(∼ F ₀)) (-closure #⁺¹(∼ F ₀)));
      try exact nonzero_ext.
     unfold inv, Creals_inv. apply (cont_ext_cont _ _ _ _ _).
  Qed.
  Instance: ClosedFun (R ₀ ⇀ R ₀) (⁻¹) := morphism_closed _.
  Hint Extern 5 (_ ⁻¹ ∊ R ₀) => eapply (_ : ClosedFun (R ₀ ⇀ R ₀) (⁻¹)) : typeclass_instances.
  Hint Extern 5 (_ ⁻¹ ∊ R) => eapply (_ : R ₀ ⊆ R) : typeclass_instances.

  Let preserves_negate x `{x ∊ F} : # (-x) = - # x.
  Proof.
    now destruct ( ufm_completion_map_extends (CX:=R) (-) _ _ (_:Proper (F,=) x) ).
  Qed.

  Let preserves_plus x `{x ∊ F} y `{y ∊ F} : # (x+y) = # x + # y.
  Proof.
    now destruct ( ufm_completion_map_extends (CX:=R*R) (uncurry (+) : F*F ⇀ F ) (x,y) (x,y)
      (_:Proper (F*F,=) (x,y)) ).
  Qed.

  Let preserves_mult x `{x ∊ F} y `{y ∊ F} : # (x*y) = # x * # y.
  Proof.
    now destruct ( cont_ext_extends (to_completion (F*F) (R*R)) # (F*F) F (uncurry (.*.))
      (x,y) (x,y) (_:Proper (F*F,=) (x,y)) ) .
  Qed.

  Instance: ∀ x, x ∊ F ₀ → #x ∊ R ₀.
  Proof. intros x [??]. split. apply _. change (# x ≠ # 0). now apply (strong_injective _ _ _). Qed.

  Let preserves_inv x `{x ∊ F ₀} : # (x⁻¹) = (#x)⁻¹.
  Proof.
    destruct ( cont_ext_extends # # (F ₀) (F ₀) (⁻¹) x x (_:Proper (F ₀,=) x) ) .
    pose proof _ :  (inv (#x)) ∊ R ₀.
    subsymmetry.
  Qed.

  Instance: Commutative (+) R.
  Proof.
    cut (uncurry (+) = uncurry (+) ∘ (prod_swap:R*R ⇀ R*R)).
      intros E x ? y ?. now destruct (E (x,y) (x,y) (_:Proper (R*R,=) (x,y)) ).
    apply (ufm_cont_equal_on_dense_image_applied (to_completion (F*F) (R*R)) _ _).
    intros [x y][??]. change (#x + #y = #y + #x).
    now rewrite <-2!(_ $ preserves_plus _ _), (_ $ commutativity (+) _ _).
  Qed.

  Instance: Associative (+) R.
  Proof.
    cut (   uncurry (+) ∘ (prod_map (uncurry (+)) (id:R⇀R))
          = uncurry (+) ∘ (prod_map (id:R⇀R) (uncurry (+))) ∘ prod_assoc_r ).
      intros E x ? y ? z ?. now destruct (E (x,y,z) (x,y,z) (_:Proper (R*R*R,=) (x,y,z)) ).
    apply (ufm_cont_equal_on_dense_image_applied (to_completion (F*F*F) (R*R*R)) _ _).
    intros [[x y] z][[??]?]. change (#x + #y + #z = #x + (#y + #z)).
    now rewrite <-!(_ $ preserves_plus _ _), (_ $ associativity (+) _ _ _).
  Qed.

  Instance: LeftIdentity (+) 0 R.
  Proof.
    cut ( uncurry (+) ∘ (prod_map (λ _, 0) (id:R⇀R)) ∘ prod_diag = (id:R⇀R) ).
      intros E x ?. now destruct (E x x (_:Proper (R,=) x) ).
    apply (ufm_cont_equal_on_dense_image_applied # _ _).
    intros x ?. change (#0 + #x = #x).
    now rewrite <-(_ $ preserves_plus _ _), (_ $ plus_0_l _).
  Qed.

  Instance: LeftInverse (+) (-) 0 R.
  Proof.
    cut (    uncurry (+) ∘ (prod_map (-) (id:R⇀R)) ∘ prod_diag = ((λ _, 0):R⇀R) ).
      intros E x ?. now destruct (E x x (_:Proper (R,=) x) ).
    apply (ufm_cont_equal_on_dense_image_applied # _ _).
    intros x ?. change (-#x + #x = #0).
    now rewrite <-(_ $ preserves_negate _), <-(_ $ preserves_plus _ _), (_ $ plus_negate_l _).
  Qed.

  Instance: Commutative (.*.) R.
  Proof.
    cut (uncurry (.*.) = uncurry (.*.) ∘ (prod_swap:R*R ⇀ R*R)).
      intros E x ? y ?. now destruct (E (x,y) (x,y) (_:Proper (R*R,=) (x,y)) ).
    apply (cont_equal_on_dense_image_applied _ _ (to_completion (F*F) (R*R))).
    intros [x y][??]. change (#x * #y = #y * #x).
    now rewrite <-2!(_ $ preserves_mult _ _), (_ $ commutativity (.*.) _ _).
  Qed.

  Instance: Associative (.*.) R.
  Proof.
    cut (   uncurry (.*.) ∘ (prod_map (uncurry (.*.)) (id:R⇀R))
          = uncurry (.*.) ∘ (prod_map (id:R⇀R) (uncurry (.*.))) ∘ (prod_assoc_r:R*R*R⇀R*(R*R)) ).
      intros E x ? y ? z ?. now destruct (E (x,y,z) (x,y,z) (_:Proper (R*R*R,=) (x,y,z)) ).
    apply (cont_equal_on_dense_image_applied _ _ (to_completion (F*F*F) (R*R*R))).
    intros [[x y] z][[??]?]. change (#x * #y * #z = #x * (#y * #z)).
    now rewrite <-!(_ $ preserves_mult _ _), (_ $ associativity (.*.) _ _ _).
  Qed.

  Instance: LeftIdentity (.*.) 1 R.
  Proof.
    cut (    uncurry (.*.) ∘ (prod_map (λ _, 1) (id:R⇀R)) ∘ prod_diag = (id:R⇀R) ).
      intros E x ?. now destruct (E x x (_:Proper (R,=) x) ).
    apply (cont_equal_on_dense_image_applied _ _ #).
    intros x ?. change (#1 * #x = #x).
    now rewrite <-(_ $ preserves_mult _ _), (_ $ mult_1_l _).
  Qed.

  Instance: LeftDistribute (.*.) (+) R.
  Proof.
    cut ( uncurry (.*.) ∘ (prod_map (id:R⇀R) (uncurry (+)))
         = uncurry (+) ∘ (prod_map
             (uncurry (.*.) ∘ (prod_map (id:R⇀R) (fst:R*R⇀R)) )
             (uncurry (.*.) ∘ (prod_map (id:R⇀R) (snd:R*R⇀R)) )
           ) ∘ (prod_diag:R*(R*R) ⇀ (R*(R*R))*(R*(R*R))) ).
      intros E x ? y ? z ?. now destruct (E (x,(y,z)) (x,(y,z)) (_:Proper (R*(R*R),=) (x,(y,z))) ).
    apply (cont_equal_on_dense_image_applied _ _ (to_completion (F*(F*F)) (R*(R*R)))).
    intros [x [y z]][?[??]]. change (#x * (#y + #z) = #x * #y + #x * #z).
    rewrite <-(_ $ preserves_plus _ _), <-3!(_ $ preserves_mult _ _), <-(_ $ preserves_plus _ _).
    now rewrite (_ $ plus_mult_distr_l _ _ _).
  Qed.

  Instance: CommutativeRing R.
  Proof. repeat (split; try apply _). Qed.

  Instance Creals_inject_ring_mor: SemiRing_Morphism F R #.
  Proof. apply (ring_morphism_alt _ _).
    exact preserves_plus.
    exact preserves_mult.
    easy.
  Qed.

  Instance: StrongRngOps R.
  Proof. split; [ apply _ |..]; (split; [ apply _ |]).
    now destruct (uniformly_cont_strong_mor (uncurry (+):R*R ⇀ R)).
    now destruct (cont_strong_mor (uncurry (.*.):R*R ⇀ R)).
  Qed.

  Instance: 1 ∊ R ₀ := _ : # 1 ∊ R ₀.

  Instance: Dense (X:=R ₀) #⁺¹(F ₀).
  Proof. apply (dense_ambient_proper _ nonzero_ext).
    exact (ext_domain_dense_image # (F ₀)).
  Qed.

  Instance: LeftInverse (.*.) (⁻¹) 1 (R ₀).
  Proof.
    cut (    (uncurry (.*.):R ₀ * R ₀ ⇀ R)
                ∘ (prod_map (inv:R ₀ ⇀ R ₀) (id:R ₀ ⇀ R ₀)) ∘ prod_diag = ((λ _, 1):R ₀ ⇀ R) ).
      intros E x ?. now destruct (E x x (_:Proper (R ₀,=) x) ).
    assert (Continuous (R ₀ * R ₀) R (uncurry mult)).
      apply (restrict_continuous (D:=R*R)); apply _.
    assert (MetricSpace (R ₀)). exact sub_metric_space.
    apply (cont_equal_on_dense (D:=R ₀) (R:=R) _ _ (#⁺¹(F ₀))).
    intros x' ? [[[?[x[? E]]] _ ] _].
    assert (x' ∊ R ₀). rewrite <-(R $ E). apply _.
    red_sig. rewrite <-(R ₀ $ E).
    change ( (# x)⁻¹ * (# x) = # 1 ).
    assert (∀x, x ∊ R ₀ → x ∊ R). apply _.
    rewrite <-( R $ preserves_inv x ), <-(R $ preserves_mult _ _).
    now rewrite (F $ field_inv_l x).
  Qed.

  Instance Creals_field: Field R := {}.

End contents.
