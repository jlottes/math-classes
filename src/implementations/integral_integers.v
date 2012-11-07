Require Import stdlib_binary_integers.
Require Import
  abstract_algebra interfaces.naturals interfaces.integers
  theory.strong_setoids theory.fields theory.subrings theory.integers theory.jections
  peano_naturals natpair_integers.

Local Notation nat := (every nat).
Local Notation Zc := (SRpair nat).

Section contents.
  Context `(R:Subset) `{CommutativeRing _ (R:=R)}.

  Notation ZctoR := (integers_to_ring Zc R).

  Definition integral : Subset := ZctoR⁺¹(Zc).

  Hint Unfold integral : typeclass_instances.

  Notation Z := integral.

  Instance integral_subset    : SubsetOf Z R := _.
  Instance integral_subsetoid : Z ⊆ R := _.
  Instance integral_comring: CommutativeRing Z := image_preserves_comring _.
  Instance integral_ring : Ring Z := _.
  Instance integral_rng  : Rng  Z := _.
  Instance integral_comsring: CommutativeSemiRing Z := _.
  Instance integral_sring: SemiRing Z := _.
  Instance integral_srng : SemiRng Z := _.
  Instance integral_setoid: Setoid Z := _.
  Instance integral_addmon : AdditiveMonoid Z := _.
  Instance integral_multsgroup : MultiplicativeSemiGroup Z := _.
End contents.

Hint Extern 2 (Equiv (elt_type (integral ?X))) => eexact (_ : Equiv X) : typeclass_instances.
Hint Extern 2 (UnEq  (elt_type (integral ?X))) => eexact (_ : UnEq X) : typeclass_instances.

Hint Extern 2 (SubsetOf (integral _) _) => eapply @integral_subset : typeclass_instances.
Hint Extern 2 (SubSetoid (integral _) _) => eapply @integral_subsetoid : typeclass_instances.
Hint Extern 2 (CommutativeRing (integral _)) => eapply @integral_comring : typeclass_instances.
Hint Extern 2 (Ring (integral _)) => eapply @integral_ring : typeclass_instances.
Hint Extern 2 (Rng (integral _)) => eapply @integral_rng : typeclass_instances.
Hint Extern 2 (CommutativeSemiRing (integral _)) => eapply @integral_comsring : typeclass_instances.
Hint Extern 2 (SemiRing (integral _)) => eapply @integral_sring : typeclass_instances.
Hint Extern 2 (SemiRng (integral _)) => eapply @integral_srng : typeclass_instances.
Hint Extern 2 (Setoid (integral _)) => eapply @integral_setoid : typeclass_instances.
Hint Extern 2 (AdditiveMonoid (integral _)) => eapply @integral_addmon : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup (integral _)) => eapply @integral_multsgroup : typeclass_instances.

Hint Extern 20 (?x ∊ ?R) => match goal with
  | sub : x ∊ integral R |- _ => eapply (integral_subset R x sub)
end : typeclass_instances.

Require Import interfaces.rationals theory.rationals implementations.intfrac_rationals.
Require Import misc.quote.

Section rationals.

  Open Scope mc_fun_scope.

  Notation Zb := (every BinNums.Z).

  Definition Z_to_FracZ : Zb ⇀ integral (Frac Zb) := integers_to_ring Zb (Frac Zb).
  Instance FracZ_to_Z : Inverse Z_to_FracZ := λ x, Zdiv.Zdiv (num x) (den x).

  Hint Unfold Z_to_FracZ : typeclass_instances.

  Instance: Closed (Zb ⇀ integral (Frac Zb)) Z_to_FracZ.
  Proof. intros x ?. split. apply _. exists_sub (integers_to_ring Zb Zc x).
    unfold Z_to_FracZ. apply (to_ring_twice _ _ _ _).
  Qed.

  Instance: Morphism (Zb ⇒ integral (Frac Zb)) Z_to_FracZ.
  Proof. intros x y E. unfold_sigs. pose proof @closed_range. red_sig.
    unfold Z_to_FracZ. now rewrite (Zb $ E).
  Qed.

  Instance: Ring_Morphism Zb (integral (Frac Zb)) Z_to_FracZ.
  Proof. apply ring_morphism_alt; try apply _; intros; unfold Z_to_FracZ.
  + exact (preserves_plus _ _).
  + exact (preserves_mult _ _).
  + exact preserves_1.
  Qed.

  Instance: Injective Zb (integral (Frac Zb)) Z_to_FracZ.
  Proof. split. 2: apply _. exact (injective (integers_to_ring Zb (Frac Zb))). Qed.

  Lemma FracZ_to_Z_correct x `{x ∊ integral (Frac Zb)}
    : x = Z_to_FracZ (FracZ_to_Z x).
  Proof. destruct (_ : x ∊ integral (Frac Zb)) as [el [xc [? E]]].
    rewrite <-(Frac Zb $ to_ring_unique (integers_to_ring Zb (Frac Zb) ∘ integers_to_ring Zc Zb) xc) in E.
    unfold compose in E. set (xb := integers_to_ring Zc Zb xc) in E.
    unfold Z_to_FracZ.
    rewrite <-(Frac Zb $ to_ring_unique (cast Zb (Frac Zb)) _).
    rewrite <-(Frac Zb $ to_ring_unique (cast Zb (Frac Zb)) _) in E.
    destruct x as [n d]. destruct el as [_ [_ d0]].
    unfold cast, frac_inject, equiv, frac_equiv in E |- *.
    unfold FracZ_to_Z. simpl.
    rewrite (mult_1_l n) in E. change (BinInt.Z.mul xb d ≡ n) in E.
    rewrite <- E.
    rewrite (Zdiv.Z_div_mult_full xb d d0).
    rewrite (mult_1_r _). exact (commutativity (.*.) _ _).
  Qed.

  Instance: Surjective Zb (integral (Frac Zb)) Z_to_FracZ.
  Proof. split; [| apply _ |]; unfold inverse.
  + intros x y E. unfold_sigs. unfold compose. red_sig.
    now rewrite <- (Frac Zb $ FracZ_to_Z_correct x).
  + intros x ?. apply _.
  Qed.

  Instance: Bijective Zb (integral (Frac Zb)) Z_to_FracZ := {}.

  Instance: Ring_Morphism (integral (Frac Zb)) Zb Z_to_FracZ⁻¹ := _.
  Instance: Bijective (integral (Frac Zb)) Zb Z_to_FracZ⁻¹ := _.

  Section another_rationals.
    Context `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)}.
    Notation Q1_to_Q2 := (rationals_to_field Q1 Q2).

    Instance rat_to_rat_int_closed: Closed (integral Q1 ⇀ integral Q2) Q1_to_Q2.
    Proof. intros. intros x ?. split. apply _.
      destruct (_ : x ∊ integral Q1) as [_ [xc [? Ex]]].
      exists_sub xc. rewrite <- (Q1 $ Ex). subsymmetry. apply (to_ring_twice _ _ _ _).
    Qed.

    Instance rat_to_rat_int_mor: Morphism (integral Q1 ⇒ integral Q2) Q1_to_Q2.
    Proof. intros. intros x y E. unfold_sigs. pose proof @closed_range. red_sig.
      now rewrite (Q1 $ E).
    Qed.

    Instance rat_to_rat_int_ring_mor: Ring_Morphism (integral Q1) (integral Q2) Q1_to_Q2.
    Proof. apply ring_morphism_alt; try apply _; intros.
    + exact (preserves_plus _ _).
    + exact (preserves_mult _ _).
    + exact preserves_1.
    Qed.

    Instance rat_to_rat_int_inj: Injective (integral Q1) (integral Q2) Q1_to_Q2.
    Proof. split. 2: apply _.
      intros x ? y ?. exact (injective Q1_to_Q2 _ _).
    Qed.

    Instance rat_to_rat_int_inv: @Inverse _ (integral Q1) _ (integral Q2) Q1_to_Q2 := inverse Q1_to_Q2.

  End another_rationals.

  Existing Instance rat_to_rat_int_closed.
  Existing Instance rat_to_rat_int_mor.
  Existing Instance rat_to_rat_int_ring_mor.
  Existing Instance rat_to_rat_int_inj.
  Existing Instance rat_to_rat_int_inv.

  Instance: ∀ `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)},
    Surjective (integral Q1) (integral Q2) (rationals_to_field Q1 Q2).
  Proof. intros. split; unfold inverse, rat_to_rat_int_inv, inverse, compose; try apply _.
    intros x y E. unfold_sigs.  red_sig.
    rewrite <- (Q2 $ E). apply (jections.surjective_applied _ _).
  Qed.

  Instance rat_to_rat_int_bij: ∀ `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)},
    Bijective (integral Q1) (integral Q2) (rationals_to_field Q1 Q2) := {}.

  Context `{Rationals (Q:=Q)}.
  Notation Z := (integral Q).

  Definition Zb_to_Q := (rationals_to_field (Frac Zb) Q : integral (Frac Zb) ⇀ integral Q) ∘ Z_to_FracZ.

  Hint Unfold Zb_to_Q : typeclass_instances.

  Instance: Bijective Zb Z Zb_to_Q := _.
  Instance: Ring_Morphism Zb Z Zb_to_Q := _.

  Instance integral_rat_to_ring : IntegersToRing Z := retract_is_int_to_ring Zb_to_Q.
  Instance integral_rat_integers : Integers Z := retract_is_int Zb_to_Q.

  Instance integral_rat_std_uneq : StandardUnEq Z.
  Proof. intros x ? y ?. exact (standard_uneq x y). Qed.

End rationals.

Hint Extern 10 (IntegersToRing (integral _)) => eapply @integral_rat_to_ring : typeclass_instances.
Hint Extern 10 (Integers (integral _)) => eapply @integral_rat_integers : typeclass_instances.
Hint Extern 10 (StandardUnEq (integral _)) => eapply @integral_rat_std_uneq : typeclass_instances.

Section more_rationals.
  Context `{Rationals (Q:=Q)}.
  Notation Z := (integral Q).

  Lemma rationals_decompose_integral x `{x ∊ Q} : ∃ `{n ∊ Z} `{d ∊ Z ₀}, x = n / d.
  Proof rationals_decompose (id:Z ⇀ Q) x.

End more_rationals.
