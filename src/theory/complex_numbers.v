Require Import
  abstract_algebra 
  interfaces.orders interfaces.archimedean_fields
  interfaces.reals interfaces.complex_numbers
  interfaces.modules interfaces.polynomial_rings
  theory.strong_setoids theory.jections
  theory.groups theory.fields theory.reals
  theory.modules theory.associative_algebras
  realpair_complexes
  stdlib_ring misc.quote.

Local Open Scope grp_scope.


Lemma complex_ring_proper: Find_Proper_Signature (@ComplexRing) 0
  (∀ A Aplus Amult Azero Aone Anegate Aunit Ae, Proper ((=)==>impl) (@ComplexRing A Aplus Amult Azero Aone Anegate Aunit Ae)).
Proof. structure_proper; trivial. Qed.
Hint Extern 0 (Find_Proper_Signature (@ComplexRing) 0 _) => eexact complex_ring_proper : typeclass_instances.

Section complex_ring.
  Context `{ComplexRing (C:=C)}.

  Lemma i_sqr_neg_1 : i*i = -1.
  Proof. apply (equal_by_zero_sum _ _). rewrite (_ $ negate_involutive _).
    exact imaginary_unit_def.
  Qed.

  Context `{Inv _} `{UnEq _} `{!Field C}.

  Instance i_nonzero : i ∊ C ₀ .
  Proof. apply (mult_apart_zero_l i i). rewrite (_ $ i_sqr_neg_1). apply _. Qed.

  Lemma inverse_i : i⁻¹ = -i.
  Proof. apply (left_cancellation (.*.) i C _ _).
    rewrite (_ $ field_inv_r _). subsymmetry.
    rewrite <-(_ $ negate_mult_distr_r _ _), (_ $ i_sqr_neg_1).
    exact (negate_involutive _).
  Qed.
End complex_ring.

Hint Extern 2 (i ∊ _ ₀) => eapply @i_nonzero : typeclass_instances.

Lemma complex_ring_morphism_alt `{R:set} `{S:set}
  (f:R ⇀ S) `{ComplexRing _ (C:=R)} `{ComplexRing _ (C:=S)} :
  Morphism (R ⇒ S) f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 1 = 1
  → f i = i
  → ComplexRing_Morphism R S f.
Proof. intros ? fplus fmult f1 fi.
  assert (SemiRing_Morphism R S f) by now apply (ring_morphism_alt f).
  repeat (split; try apply _); trivial.
Qed.

Lemma complexring_morphism_proper: Find_Proper_Signature (@ComplexRing_Morphism) 0
  (∀ A B Ae Be Aplus Bplus Amult Bmult Azero Bzero Aone Bone Anegate Bnegate Aunit Bunit R S,
    Proper ((@equiv (R ⇀ S) _) ==> impl)
   (@ComplexRing_Morphism A B Ae Be Aplus Bplus Amult Bmult Azero Bzero Aone Bone Anegate Bnegate Aunit Bunit R S)).
Proof. red; intros. intros f g E ?.
  destruct (_ : ComplexRing_Morphism R S f) as [?? _ _].
  split; try apply _. rewrite <- E; apply _.
  rewrite <- (E i i); try now red_sig. exact preserves_i.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ComplexRing_Morphism) 0 _) => eexact complexring_morphism_proper : typeclass_instances.

Lemma complexring_morphism_proper2: Find_Proper_Signature (@ComplexRing_Morphism) 1
  (∀ A B Ae Be Aplus Bplus Amult Bmult Azero Bzero Aone Bone Anegate Bnegate Aunit Bunit,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@ComplexRing_Morphism A B Ae Be Aplus Bplus Amult Bmult Azero Bzero Aone Bone Anegate Bnegate Aunit Bunit)).
Proof. structure_mor_proper. trivial. Qed.
Hint Extern 0 (Find_Proper_Signature (@ComplexRing_Morphism) 1 _) => eexact complexring_morphism_proper2 : typeclass_instances.

Lemma id_complexring_mor `(R:set) S `{!Subset R S} `{ComplexRing _ (C:=R)} `{!ComplexRing S} : ComplexRing_Morphism R S id.
Proof. split; try apply _. subreflexivity. Qed.
Hint Extern 4 (ComplexRing_Morphism _ _ id) => eapply @id_complexring_mor : typeclass_instances.

Lemma compose_complexring_morphism `{ComplexRing (C:=R)} `{S:set} `{ComplexRing _ (C:=S)} `{ComplexRing (C:=T)}
  (f:R ⇀ S) (g:S ⇀ T) `{!ComplexRing_Morphism R S f} `{!ComplexRing_Morphism S T g}: ComplexRing_Morphism R T (g ∘ f).
Proof. split; try apply _.
  unfold compose. rewrite (S $ preserves_i). exact preserves_i.
Qed.
Hint Extern 4 (ComplexRing_Morphism _ _ (_ ∘ _)) => class_apply @compose_complexring_morphism : typeclass_instances.

Lemma invert_complexring_morphism `{R:set} `{S:set}
 (f:R ⇀ S) `{ComplexRing_Morphism _ _ (C₁:=R) (C₂:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  ComplexRing_Morphism S R (inverse f).
Proof. destruct (_ : ComplexRing_Morphism R S f) as [?? _ _].
  split; try apply _.
  apply (injective f _ _).
  now rewrite (S $ preserves_i), (S $ surjective_applied _ _).
Qed.
Hint Extern 4 (ComplexRing_Morphism _ _ (inverse _)) => eapply @invert_complexring_morphism : typeclass_instances.


Hint Extern 2 (SemiRing_Morphism _ _ (complex_to_ring _ _)) => class_apply @cringmor_sring_mor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism _ _ (complex_to_ring _ _)) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ (complex_to_ring _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (complex_to_ring _ _)) => eapply @monmor_sgmor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (complex_to_ring _ _)) => eapply @srngmor_mult_mor : typeclass_instances.

Local Notation R := (complex_reals _).

Lemma complex_to_ring_plain_mor {A} (C:@set A) `{ComplexNumbers A (C:=C)} 
  `{S:set} `{ComplexRing _ (C:=S)} (f:R ⇀ S) `{!SemiRing_Morphism R S f}
  : Morphism (C ⇒ S) (complex_to_ring C f).
Proof. pose proof _ : SemiRing_Morphism C S (complex_to_ring C f). apply _. Qed.

Hint Extern 2 (Morphism _ (complex_to_ring ?C ?f)) => eapply (complex_to_ring_plain_mor C f) : typeclass_instances.


Lemma complex_to_self `{ComplexNumbers (C:=C)} : complex_to_ring C (id : R ⇀ C) = (id : C ⇀ C).
Proof. symmetry. apply (complex_to_ring_unique C id id) . subreflexivity. Qed.

Section complex_to_complex.
  Context `{ComplexNumbers (C:=C₁)}.  Notation R₁ := (complex_reals C₁).
  Context `{ComplexNumbers (C:=C₂)}.  Notation R₂ := (complex_reals C₂).

  Notation f := ((id:R₂ ⇀ C₂) ∘ to_reals R₂ R₁) .
  Instance: SemiRing_Morphism R₁ C₂ f := _.

  Definition complex_to_complex := complex_to_ring C₁ f.
  Notation g := complex_to_complex.

  Hint Unfold complex_to_complex : typeclass_instances.
  
  Instance complex_to_complex_plain_mor : Morphism (C₁ ⇒ C₂) g := _.
  Instance complex_to_complex_mor : ComplexRing_Morphism C₁ C₂ g := _.

  Lemma complex_to_complex_of_real x `{x ∊ R₁} : g x = to_reals R₂ R₁ x.
  Proof.
    assert (x ∊ C₁). apply (_ : R ⊆ C₁). apply _.
    assert (to_reals R₂ R₁ x ∊ C₂). apply (_ : R ⊆ C₂). apply _.
    subsymmetry.
    now destruct (complex_to_ring_extends C₁ ((id:R ⇀ C₂) ∘ to_reals R R) _ _ (_:Proper (R,=) x)).
  Qed.
End complex_to_complex.

Arguments complex_to_complex {_} C₁ {_ _ _ _ _ _ _ _ _ _ _} C₂ {_ _ _ _ _} _.

Hint Extern 2 (ComplexRing_Morphism _ _ (complex_to_complex _ _)) => class_apply @complex_to_complex_mor : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (complex_to_complex _ _)) => class_apply @cringmor_sring_mor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism _ _ (complex_to_complex _ _)) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ (complex_to_complex _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (complex_to_complex _ _)) => eapply @monmor_sgmor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (complex_to_complex _ _)) => eapply @srngmor_mult_mor : typeclass_instances.
Hint Extern 2 (Morphism _ (complex_to_complex _ _)) => class_apply @complex_to_complex_plain_mor : typeclass_instances.

Hint Extern 2 (Inverse (complex_to_complex ?C₁ ?C₂))
  => eexact (complex_to_complex C₂ C₁) : typeclass_instances.

Hint Extern 2 (to_reals (complex_reals ?C) _ _ ∊ ?C) => apply (_ : complex_reals C ⊆ C) : typeclass_instances.

Section complex_to_complex_bijective.
  Let bij_aux
    `{ComplexNumbers (C:=C₁)}
    `{ComplexNumbers (C:=C₂)} :
    (complex_to_complex C₂ C₁) ∘ (complex_to_complex C₁ C₂) = id.
  Proof. pose proof (_ : R ⊆ C₁). rewrite <-(complex_to_self).
    apply (complex_to_ring_unique C₁ id _).
    unfold compose. intros y x E. unfold_sigs. red_sig. subtransitivity x. clear dependent y.
    rewrite (_ $ complex_to_complex_of_real x).
    rewrite (_ $ complex_to_complex_of_real _).
    subsymmetry.
    match goal with |- ?f (?g x) = x =>
      now destruct (to_reals_self (f ∘ g) _ _ (_:Proper (R,=) x))
    end.
  Qed.

  Instance complex_to_complex_bijective
    `{ComplexNumbers (C:=C₁)}
    `{ComplexNumbers (C:=C₂)} :
    Bijective C₁ C₂ (complex_to_complex C₁ C₂) .
  Proof. apply alt_Build_Bijective; unfold inverse; try apply _; apply bij_aux. Qed.
End complex_to_complex_bijective.

Hint Extern 2 (Bijective _ _ (complex_to_complex _ _)) => class_apply @complex_to_complex_bijective : typeclass_instances.

Lemma complex_numbers_algebra `{ComplexNumbers (C:=C)}
  : UnitalCommutativeAlgebra R C.
Proof. apply (unital_comm_alg_from_ring (id:R ⇀ C)).
+ unfold dot. rewrite <-(_ : Subset (C ⇒ C ⇒ C) (R ⇒ C ⇒ C)). apply _.
+ intros r ? z ?. pose proof (_ : R ⊆ C). subreflexivity.
Qed.

Class RealPart `(C:set) `{!ComplexReals C} := re : C ⇀ R .
Class ImagPart `(C:set) `{!ComplexReals C} := im : C ⇀ R .

Section re_im_spec.
  Context `{ComplexNumbers (C:=C)}.

  Class RealPartSpec (f:RealPart C) : Prop :=
  { real_part_closed : Closed (C ⇀ R) re
  ; real_part_spec z `{z ∊ C} a `{a ∊ R} b `{b ∊ R} : z = a + b * i → re z = a
  }.

  Class ImagPartSpec (f:ImagPart C) : Prop :=
  { imag_part_closed : Closed (C ⇀ R) im
  ; imag_part_spec z `{z ∊ C} a `{a ∊ R} b `{b ∊ R} : z = a + b * i → im z = b
  }.

End re_im_spec.
Arguments RealPartSpec {_} C {_ _ _ _ _ f}.
Arguments ImagPartSpec {_} C {_ _ _ _ _ f}.

Section re.
  Context `{ComplexNumbers (C:=C)}.
  Add Ring C : (stdlib_ring_theory C).

  Instance: ComplexNumbers (ComplexPair R) := _.

  Instance: ∀ a `{a ∊ R} b `{b ∊ R}, cp a b ∊ ComplexPair R.
  Proof. split; simpl; apply _. Qed.

  Notation g := (complex_to_complex C (ComplexPair (complex_reals C))).
 
  Lemma complex_to_complex_pair_real x `{x ∊ R} : g x = cp x 0.
  Proof.
    assert (cp x 0 = cp (to_reals R R x) 0) as E.
      split; simpl; [| easy]. apply (symmetry (S:=R) _ _).
      now destruct (to_reals_self (to_reals R R) _ _ (_:Proper (R,=) x)).
    pose proof _ : R ⊆ C.
    rewrite (ComplexPair R $ E).
    exact (complex_to_complex_of_real x).
  Qed.

  Definition real_part_default : C ⇀ R := realpair_complexes.re ∘ g.
  Definition imag_part_default : C ⇀ R := realpair_complexes.im ∘ g.

  Notation re' := real_part_default.
  Notation im' := imag_part_default.

  Hint Unfold re' : typeclass_instances.
  Hint Unfold im' : typeclass_instances.

  Instance: Morphism (C ⇒ R) re' := _.
  Instance: Morphism (C ⇒ R) im' := _.

  Lemma complex_decompose_default z `{z ∊ C} : z = re' z + im' z * i.
  Proof. pose proof _ : R ⊆ C.
    apply (injective g _ _).
    rewrite (ComplexPair R $ preserves_plus _ _).
    rewrite (ComplexPair R $ preserves_mult _ _).
    rewrite (ComplexPair R $ preserves_i).
    unfold re', im', compose.
    set (z' := g z ). assert (z' ∊ ComplexPair R) as el. unfold z'. apply _.
    destruct z' as [a b], el as [??]. simpl in *.
    rewrite (ComplexPair R $ complex_to_complex_pair_real a).
    rewrite (ComplexPair R $ complex_to_complex_pair_real b).
    split; simpl; setring C.
  Qed.

  Lemma complex_decompose_alt z `{z ∊ C} : ∃ a `{a ∊ R} b `{b ∊ R}, z = a + b * i.
  Proof. exists_sub (re' z) (im' z). exact (complex_decompose_default _). Qed.

  Hint Extern 5 (_ ∊ C) => apply (_ : R ⊆ C) : typeclass_instances.

  Instance real_part_default_spec : RealPartSpec C (f:=real_part_default).
  Proof. split. apply _. intros z ? a ? b ? E. unfold re. rewrite (C $ E).
    unfold re', compose.
    rewrite (ComplexPair R $ preserves_plus _ _).
    rewrite (ComplexPair R $ preserves_mult _ _).
    rewrite (ComplexPair R $ preserves_i).
    rewrite (ComplexPair R $ complex_to_complex_pair_real a).
    rewrite (ComplexPair R $ complex_to_complex_pair_real b).
    simpl. setring C.
  Qed.

  Instance imag_part_default_spec : ImagPartSpec C (f:=imag_part_default).
  Proof. split. apply _. intros z ? a ? b ? E. unfold im. rewrite (C $ E).
    unfold im', compose.
    rewrite (ComplexPair R $ preserves_plus _ _).
    rewrite (ComplexPair R $ preserves_mult _ _).
    rewrite (ComplexPair R $ preserves_i).
    rewrite (ComplexPair R $ complex_to_complex_pair_real a).
    rewrite (ComplexPair R $ complex_to_complex_pair_real b).
    simpl. setring C.
  Qed.

  Lemma real_part_unique (f: C ⇀ R) `{!RealPartSpec C (f:=f)} : f = re'.
  Proof. intros z w E. unfold_sigs.
    assert (f z ∊ R) by now apply real_part_closed.
    red_sig. apply (real_part_spec z (re' w) (im' w)). subtransitivity w.
    exact (complex_decompose_default _).
  Qed.

  Instance real_part_mor {f:RealPart C} `{!RealPartSpec C} : Morphism (C ⇒ R) re.
  Proof. change ((f:C ⇀ R) = (f:C ⇀ R)).
    transitivity re'; [| symmetry]; exact (real_part_unique _).
  Qed.

  Lemma imag_part_unique (f: C ⇀ R) `{!ImagPartSpec C (f:=f)} : f = im'.
  Proof. intros z w E. unfold_sigs.
    assert (f z ∊ R) by now apply imag_part_closed.
    red_sig. apply (imag_part_spec z (re' w) (im' w)). subtransitivity w.
    exact (complex_decompose_default _).
  Qed.

  Instance imag_part_mor {f:ImagPart C} `{!ImagPartSpec C} : Morphism (C ⇒ R) im.
  Proof. change ((f:C ⇀ R) = (f:C ⇀ R)).
    transitivity im'; [| symmetry]; exact (imag_part_unique _).
  Qed.

  Context `{!RealPart C} `{!RealPartSpec C}.
  Context `{!ImagPart C} `{!ImagPartSpec C}.

  Lemma complex_decompose z `{z ∊ C} : z = re z + im z * i.
  Proof.
    assert (re z = re' z) as E1.
      cut ((R,=)%signature (re z) (re' z)). now intros [??].
      apply (real_part_unique _). now red_sig. 
    assert (im z = im' z) as E2.
      cut ((R,=)%signature (im z) (im' z)). now intros [??].
      apply (imag_part_unique _). now red_sig.
    rewrite (C $ E1), (C $ E2).
    exact (complex_decompose_default _).
  Qed.

  Instance: UnitalCommutativeAlgebra R C := complex_numbers_algebra.

  Let pres_dot r `{r ∊ R} z `{z ∊ C} : g (r*z) = r · g z.
  Proof.
    rewrite (ComplexPair R $ preserves_mult _ _).
    rewrite (ComplexPair R $ complex_to_complex_pair_real r).
    set (z' := g z). assert (z' ∊ ComplexPair R) as el. unfold z'. apply _.
    destruct z' as [a b], el as [??]. split; simpl in *; setring C.
  Qed.

  Instance: Module_Morphism R C R re.
  Proof. rewrite (real_part_unique re). apply (module_morphism_alt _ _).
  + intros z ? w ?. unfold re' at 1. unfold compose.
    rewrite (ComplexPair R $ preserves_plus _ _).
    now rewrite (R $ preserves_plus (R1:=ComplexPair R) (R2:=R) _ _).
  + intros r ? z ?. unfold re' at 1. unfold compose.
    rewrite (ComplexPair R $ pres_dot r z).
    exact (preserves_dot (M₁:=ComplexPair R) (M₂:=R) (f:=realpair_complexes.re) (R:=R) r (g z)).
  Qed.

  Instance: Module_Morphism R C R im.
  Proof. rewrite (imag_part_unique re). apply (module_morphism_alt _ _).
  + intros z ? w ?. unfold im' at 1. unfold compose.
    rewrite (ComplexPair R $ preserves_plus _ _).
    now rewrite (R $ preserves_plus (R1:=ComplexPair R) (R2:=R) _ _).
  + intros r ? z ?. unfold im' at 1. unfold compose, dot.
    rewrite (ComplexPair R $ pres_dot r z).
    exact (preserves_dot (M₁:=ComplexPair R) (M₂:=R) (f:=realpair_complexes.im) (R:=R) r (g z)).
  Qed.

  Lemma re_0 : re 0 = 0.  Proof preserves_0.
  Lemma im_0 : im 0 = 0.  Proof preserves_0.

  Lemma re_real x `{x ∊ R} : re x = x.
  Proof. apply (real_part_spec x x 0). setring C. Qed.

  Lemma im_real x `{x ∊ R} : im x = 0.
  Proof. apply (imag_part_spec x x 0). setring C. Qed.

  Lemma re_1 : re 1 = 1.  Proof re_real 1.
  Lemma im_1 : im 1 = 0.  Proof im_real 1.

  Lemma re_i : re i = 0.
  Proof. apply (real_part_spec i 0 1). setring C. Qed.

  Lemma im_i : im i = 1.
  Proof. apply (imag_part_spec i 0 1). setring C. Qed.
  
  Lemma re_plus z `{z ∊ C} w `{w ∊ C} : re (z + w) = re z + re w.
  Proof preserves_plus _ _.

  Lemma im_plus z `{z ∊ C} w `{w ∊ C} : im (z + w) = im z + im w.
  Proof preserves_plus _ _.

  Lemma re_dot x `{x ∊ R} z `{z ∊ C} : re (x * z) = x * re z.
  Proof preserves_dot (R:=R) _ _.

  Lemma im_dot x `{x ∊ R} z `{z ∊ C} : im (x * z) = x * im z.
  Proof preserves_dot (R:=R) _ _.

  Lemma re_negate z `{z ∊ C} : re (-z) = - re z.
  Proof preserves_negate _.

  Lemma im_negate z `{z ∊ C} : im (-z) = - im z.
  Proof preserves_negate _.

  Let mult_decompose z `{z ∊ C} w `{w ∊ C} :
    z * w = (re z * re w - im z * im w) + (re z * im w + im z * re w) * i.
  Proof.
    subtransitivity (re z * re w + (re z * im w + im z * re w) * i + (im z * im w) * (i*i)).
      rewrite (C $ complex_decompose z) at 1.
      rewrite (C $ complex_decompose w) at 1.
      setring C.
    rewrite (C $ i_sqr_neg_1).
    setring C.
  Qed.

  Lemma re_mult z `{z ∊ C} w `{w ∊ C} : re (z * w) = re z * re w - im z * im w.
  Proof. apply (real_part_spec (z*w) _ _ (mult_decompose z w)). Qed.

  Lemma im_mult z `{z ∊ C} w `{w ∊ C} : im (z * w) = re z * im w + im z * re w.
  Proof. apply (imag_part_spec (z*w) _ _ (mult_decompose z w)). Qed.

  Lemma uneq_0_decompose z `{z ∊ C} : z ≠ 0 ↔ re z ≠ 0 ∨ im z ≠ 0.
  Proof. split.
  + intro E.
    rewrite (C $ complex_decompose z) in E.
    rewrite (C $ complex_decompose 0) in E.
    rewrite (C $ re_0), (C $ im_0) in E.
    destruct (strong_binary_extensionality (+) E) as [E2|E2]; intuition. right.
    exact (strong_extensionality (.* i) E2).
  + intro E. rewrite (C $ complex_decompose z).
    cut (re z + im z * i ∊ C ₀). now intros [??].
    apply (mult_apart_zero_l _ (re z - im z * i)). split. apply _. red.
    mc_replace ((re z + im z * i) * (re z - im z * i))
         with  (re z * re z - (i*i) * (im z * im z)) on C by setring C.
    rewrite (C $ i_sqr_neg_1). 
    mc_replace (re z * re z - -1 * (im z * im z))
         with  (re z * re z + im z * im z) on C by setring C.
    cut (re z * re z + im z * im z ∊ R₊). intro.
      now destruct (_ : re z * re z + im z * im z ∊ R ₀).
    apply (sum_of_squares_pos_iff _ _).
    destruct E as [?|?]; [left|right]; split; trivial; apply _.
  Qed.

  Lemma uneq_decompose z `{z ∊ C} w `{w ∊ C} : z ≠ w ↔ re z ≠ re w ∨ im z ≠ im w.
  Proof. split.
  + intro E.
    rewrite (C $ complex_decompose z) in E.
    rewrite (C $ complex_decompose w) in E.
    destruct (strong_binary_extensionality (+) E) as [E2|E2]; intuition. right.
    exact (strong_extensionality (.* i) E2).
  + intro E.
    apply (strong_extensionality (+ (-w))).
    mc_replace (w-w) with 0 on C by setring C.
    apply (uneq_0_decompose (z-w)).
    rewrite (_ $ re_plus _ _), (_ $ im_plus _ _), (_ $ re_negate _), (_ $ im_negate _).
    destruct E as [E|E]; [left|right].
      rewrite <-(C $ plus_negate_r (re w)).
      exact (strong_right_cancellation (+) (-re w) C _ _ E).
    rewrite <-(C $ plus_negate_r (im w)).
    exact (strong_right_cancellation (+) (-im w) C _ _ E).
  Qed.

  Instance: ∀ z, z ∊ C ₀ → re z * re z + im z * im z ∊ R₊ .
  Proof. intros z [??]. apply (sum_of_squares_pos_iff _ _).
    cut (re z ≠ 0 ∨ im z ≠ 0). intros [?|?]; [left|right]; split; trivial; apply _.
    now apply (uneq_0_decompose z).
  Qed.

  Instance: ∀ z, z ∊ C ₀ → re z * re z + im z * im z ∊ R ₀ .
  Proof. intros z ?. pose proof (_ : re z * re z + im z * im z ∊ R₊). apply _. Qed.

  Instance: ∀ z, z ∊ C ₀ → re z * re z + im z * im z ∊ C ₀ .
  Proof. intros z ?. split. apply _. red. now destruct (_ : re z * re z + im z * im z ∊ R ₀ ). Qed.

  Let inv_decompose z `{z ∊ C ₀} :
    z⁻¹ = (  re z / (re z * re z + im z * im z))
         +(- im z / (re z * re z + im z * im z)) * i.
  Proof. subtransitivity ((re z - im z * i)/(re z * re z + im z * im z)). 2: setring C.
    apply (left_cancellation (.*.) z C _ _).
    rewrite (C $ field_inv_r z).
    rewrite (C $ complex_decompose z) at 1.
    rewrite (C $ associativity (.*.) _ _ _).
    apply (mult_inv_cancel_r _ _ _).
    subtransitivity (re z * re z - (i*i) * im z * im z).
      rewrite (C $ i_sqr_neg_1). setring C.
    setring C.
  Qed.

  Lemma re_inv z `{z ∊ C ₀} : re z⁻¹ = re z / (re z * re z + im z * im z).
  Proof. apply (real_part_spec z⁻¹ _ _ (inv_decompose z)). Qed.

  Lemma im_inv z `{z ∊ C ₀} : im z⁻¹ = - im z / (re z * re z + im z * im z).
  Proof. apply (imag_part_spec z⁻¹ _ _ (inv_decompose z)). Qed.

End re.

(*
 (complex_reals C)).
    Check _ : ToReals R.
    Instance real_part_default : RealPart C := λ z, realpair_complexes.re (complex_to_complex C (ComplexPair (complex_reals C)) z).

  Lemma real_part_unique (f g: C ⇀ R) `{!RealPartSpec C (f:=f)} `{!RealPartSpec C (f:=g)} : f = g.
  Proof.
  
  

Class RealPartSpec
*)
(*
Section poly.
  Context `{Reals A (R:=R)}
    `{CommutativeRing (R:=P)}
    `{!ToPolynomialRing R P} `{!PolynomialVar P} `{!PolynomialEval R P}
    `{!Dot R P} `{!Polynomial_Ring R P}.

  Notation φ := (to_polynomial_ring (R:=R) P).
  Notation x := polynomial_var.

  Lemma poly_complex_decompose p `{p ∊ P} : ∃ `{q ∊ P} `{a ∊ R} `{b ∊ R},
    p = φ a + φ b * x + q * (x*x+1) .
  Proof.
    destruct (poly_div_monic (R:=R) (P:=P) p (x*x+1) _ x_sqr_plus_1_monic)
      as [q[elq[r[elr[E Er]]]]].
    eq_replace (2-1:ZA) with (1:ZA) in Er by reflexivity.
    rewrite (deg_le_linear _) in Er.
    destruct Er as [b[elb[a[ela Er]]]].
    rewrite (_ $ poly_ring_dot_def _ _), (_ $ commutativity (+) _ _) in Er.
    rewrite (_ $ commutativity (+) _ _), (_ $ Er) in E.
    now exists_sub q a b.
  Qed.
End poly.

Section poly_to_complex.
  Context `{Reals A (R:=R₁)}
    `{CommutativeRing (R:=P)}
    `{!ToPolynomialRing R₁ P} `{!PolynomialVar P} `{!PolynomialEval R₁ P}
    `{!Dot R₁ P} `{!Polynomial_Ring R₁ P}.
  Context `{ComplexNumbers (R:=R₂) (C:=C)}.
  Context (f:R₁ ⇀ R₂) `{!SemiRing_Morphism R₁ R₂ f} `{!StrictOrderEmbedding R₁ R₂ f}.

  Notation φ := (to_polynomial_ring (R:=R₁) P).
  Notation x := polynomial_var.
  Notation g := ((id:R₂ ⇀ C) ∘ f) .
  Notation π := (polynomial_eval (R:=R₁) (P:=P) g i) .

  Instance: SemiRing_Morphism R₁ C g := _.
  Instance: Polynomial_Evaluable g i := _.
  Instance poly_to_complex_mor: SemiRing_Morphism P C π := _.

  Lemma poly_to_complex_eq : π (x*x + 1) = 0 .
  Proof. preserves_simplify (π).
    pose proof polynomial_eval_var (R:=R₁) (P:=P) g i as E. rewrite (C $ E).
    exact (imaginary_unit_def R₂ C).
  Qed.

  Hint Extern 5 (_ ∊ C) => apply (_ : R₂ ⊆ C) : typeclass_instances.

  Lemma poly_to_complex_eval p `{p ∊ P} q `{q ∊ P} a `{a ∊ R₁} b `{b ∊ R₁}
    : p = φ a + φ b * x + q * (x*x+1) → π p = f a + f b * i.
  Proof. intros E. rewrite (P $ E). clear E. preserves_simplify (π).
    change (π (φ a) + π (φ b) * π x + π q * (π x * π x + 1) = f a + f b * i).
    pose proof polynomial_eval_var (R:=R₁) (P:=P) g i as E. rewrite (C $ E).
    rewrite (C $ imaginary_unit_def R₂ C), (_ $ mult_0_r _), (_ $ plus_0_r _).
    setoid_rewrite (polynomial_eval_const (R:=R₁) (P:=P) g i _ _ (_ : Proper (R₁,=) a)).
    setoid_rewrite (polynomial_eval_const (R:=R₁) (P:=P) g i _ _ (_ : Proper (R₁,=) b)).
    now unfold id,compose.
  Qed.

End poly_to_complex.

Section complex_to_complex.
  Context `{ComplexNumbers (R:=R₁) (C:=C₁)}.
  Context `{ComplexNumbers (R:=R₂) (C:=C₂)}.

  Notation f := ((id:R₂ ⇀ C₂) ∘ to_reals R₂ R₁) .
  Notation g := (polynomial_eval (R:=R₁) (P:=Poly R₁) ((id:R₂ ⇀ C₂) ∘ to_reals R₂ R₁) i) .

  Instance: SemiRing_Morphism R₁ C₂ f := _.
  Instance: Polynomial_Evaluable f i := _.

  Instance: SemiRing_Morphism (Poly R₁) C₂ g := _.

  Notation x := (polynomial_var (P:=Poly R₁)).

  Let Egi : g x = i := polynomial_eval_var (R:=R₁) (P:=Poly R₁) f i.
  Let Eg : g (x*x+1) = 0 := poly_to_complex_eq (P:=Poly R₁) (to_reals R₂ R₁).

  Definition complex_to_complex : C₁ ⇀ C₂ := complex_to_ring R₁ C₁ (Poly R₁) g.

  Instance: ComplexToRingSpec R₁ C₁ C₂ g complex_to_complex.
  Proof complex_to_ring_spec R₁ C₁ (ComplexSpec := complex_spec R₁ C₁ (P:=Poly R₁)) g Eg.

  Instance complex_to_complex_srmor: SemiRing_Morphism C₁ C₂ complex_to_complex.
  Proof complex_to_ring_srmor R₁ C₁ C₂ g.

  Notation π := (polynomial_eval (id:R₁⇀C₁) i).

  Let factors: g = complex_to_complex ∘ π.
  Proof complex_to_ring_factors R₁ C₁ C₂ g.

  Hint Extern 5 (_ ∊ C₁) => apply (_ : R₁ ⊆ C₁) : typeclass_instances.
  Hint Extern 5 (_ ∊ C₂) => apply (_ : R₂ ⊆ C₂) : typeclass_instances.

  Let complex_to_complex_of_real a `{a ∊ R₁} : complex_to_complex a = to_reals R₂ R₁ a .
  Proof. subtransitivity ((complex_to_complex ∘ π) (to_polynomial_ring (Poly R₁) a)).
    cut ((π ∘ to_polynomial_ring (Poly R₁)) a = a). unfold compose. intro E. now rewrite (C₁ $ E).
    now destruct (polynomial_eval_const (R:=R₁) (P:=Poly R₁) (id:R₁ ⇀ C₁) i _ _ (_ : Proper (R₁,=) a)).
    rewrite <-(factors _ _ (_ : Proper (Poly R₁,=) (to_polynomial_ring (Poly R₁) a))) .
    subtransitivity (to_reals R₂ R₁ a + to_reals R₂ R₁ 0 * i).
      apply (poly_to_complex_eval (P:=Poly R₁) (to_reals R₂ R₁) _ 0 _ _).
      rewrite (_ $ preserves_0). now rewrite 2!(Poly R₁ $ mult_0_l _), 2!(Poly R₁ $ plus_0_r _).
    pose proof _ : SemiRing_Morphism R₁ R₂ (to_reals R₂ R₁).
    now rewrite (_ $ preserves_0), (_ $ mult_0_l _), (_ $ plus_0_r _).
  Qed.

  Let complex_to_complex_of_i : complex_to_complex i = i .
  Proof. pose proof polynomial_eval_var (R:=R₁) (P:=Poly R₁) (id:R₁⇀C₁) i as E. rewrite <-(C₁ $ E).
    setoid_rewrite <-(factors _ _ (_ : Proper (Poly R₁,=) (polynomial_var (P:=Poly R₁)))) .
    exact Egi.
  Qed.

  Instance: ∀ a `{a ∊ R₁}, complex_to_complex a ∊ R₂ .
  Proof. intros a ?. rewrite (C₂ $ complex_to_complex_of_real a). apply _. Qed.

  Lemma complex_to_complex_to_reals : (complex_to_complex : R₁ ⇀ R₂) = to_reals R₂ R₁ .
  Proof. intros a b E. unfold_sigs. red_sig. now rewrite (C₂ $ complex_to_complex_of_real a), (R₁ $ E). Qed.

  Instance: StrictOrderEmbedding R₁ R₂ complex_to_complex.
  Proof. rewrite complex_to_complex_to_reals. apply _. Qed.

  Context (h:C₁ ⇀ C₂) `{!SemiRing_Morphism C₁ C₂ h} `{!StrictOrderEmbedding R₁ R₂ h} (Eh: h i = i).

  Instance : SemiRing_Morphism R₁ R₂ h.
  Proof. destruct (_ : StrictOrder_Morphism R₁ R₂ h) as [? _ _].
    apply (ring_morphism_alt (h:R₁ ⇀ R₂) _).
    intros. exact (preserves_plus _ _).
    intros. exact (preserves_mult _ _).
    exact preserves_1.
  Qed.

  Let h_factors : g = h ∘ π .
  Proof. intros q p E. unfold_sigs. red_sig. rewrite (Poly R₁ $ E). clear dependent q.
    destruct (poly_complex_decompose (R:=R₁) (P:=Poly R₁) p)
      as [q[elq[a[ela[b[elb Ep]]]]]].
    subtransitivity (to_reals R₂ R₁ a + to_reals R₂ R₁ b * i).
    exact (poly_to_complex_eval (P:=Poly R₁) (to_reals R₂ R₁) p q a b Ep).
    unfold compose.
    assert (polynomial_eval (id:R₁ ⇀ C₁) i p = a + b * i) as E.
      exact (poly_to_complex_eval (P:=Poly R₁) (id:R₁⇀R₁) p q a b Ep).
    setoid_rewrite (C₁ $ E).
    preserves_simplify h.
    assert (h a = to_reals R₂ R₁ a) as Ea by now
      destruct (to_reals_terminal R₂ h _ _ (_ : Proper (R₁,=) a)).
    rewrite <-(C₂ $ Ea).
    assert (h b = to_reals R₂ R₁ b) as Eb by now
      destruct (to_reals_terminal R₂ h _ _ (_ : Proper (R₁,=) b)).
    rewrite <-(C₂ $ Eb).
    now rewrite (C₂ $ Eh).
  Qed.

  Lemma complex_to_complex_unique : h = complex_to_complex.
  Proof complex_to_ring_unique R₁ C₁ C₂ g h h_factors.
End complex_to_complex.
*)
