Require Import
  abstract_algebra theory.setoids theory.common_props theory.jections theory.groups.

(** Operations are closed and proper *)

Section plus.
  Context `{Aplus: Plus A} {Azero: Zero A} {Ae:Equiv A} {R:@set A}.
  Context `{!AdditiveMonoid R}.

  Lemma plus_closed : Closed (R ⇀ R ⇀ R) (+). Proof sg_op_closed.

  Lemma plus_0_l: LeftIdentity (+) 0 R. Proof _.
  Lemma plus_0_r: RightIdentity (+) 0 R. Proof _.
End plus.
Arguments plus_0_l {A Aplus Azero Ae R _} _ {_}.
Arguments plus_0_r {A Aplus Azero Ae R _} _ {_}.

Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (+)) => eapply @plus_closed : typeclass_instances.
Hint Extern 5 (_ + _ ∊ _) => eapply @plus_closed : typeclass_instances. 

Lemma plus_proper: Find_Proper_Signature (@plus) 0
  (∀ A (Aplus:Plus A) (Azero:Zero A) (Ae:Equiv A) R `{!AdditiveMonoid R},
   Proper ((R,=)==>(R,=)==>(R,=)) (+)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@plus) 0 _) => eexact plus_proper : typeclass_instances.

Lemma mult_proper: Find_Proper_Signature (@mult) 0
  (∀ A (Amult:Mult A) (Ae:Equiv A) R `{!MultiplicativeSemiGroup R},
   Proper ((R,=)==>(R,=)==>(R,=)) (.*.)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@mult) 0 _) => eexact mult_proper : typeclass_instances.

Lemma mult_closed `{Mult} `{Equiv _} {R} `{!MultiplicativeSemiGroup R}
  : Closed (R ⇀ R ⇀ R) (.*.).
Proof sg_op_closed.

Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (.*.)) => eapply @mult_closed : typeclass_instances.
Hint Extern 5 (_ * _ ∊ _) => eapply @mult_closed : typeclass_instances. 

Lemma negate_closed `{Plus} `{Zero _} `{Negate _} `{Equiv _} {R} `{!AdditiveGroup R}
  : Closed (R ⇀ R) (-).
Proof _.

Hint Extern 5 (- _ ∊ _) => eapply @negate_closed : typeclass_instances. 

Lemma negate_proper: Find_Proper_Signature (@negate) 0
  (∀ `{Plus A} `{Zero A} `{Negate A} `{Equiv A} R `{!AdditiveGroup R},
   Proper ((R,=)==>(R,=)) (-)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@negate) 0 _) => eexact negate_proper : typeclass_instances.


(** Deducible structure instances *)

Instance semiring_mult_monoid `{sr: SemiRing (R:=R)} : MultiplicativeMonoid R.
Proof. destruct sr. split; apply _. Qed.

Instance comsemiring_semiring `{csr: CommutativeSemiRing (R:=R)} : SemiRing R.
Proof. destruct csr. destruct (_:MultiplicativeMonoid R). do 2 (split; try apply _).
  exact right_distr_from_left. exact right_absorb_from_left.
Qed.

Instance rng_semirng `{r: Rng (R:=R)} : SemiRng R.
Proof. destruct r. split; try apply _.
+ intros y ?. apply (right_cancellation (&) (0*y) R _ _).
  now rewrite_on R <-(distribute_r 0 0 y), (plus_0_r 0), (plus_0_l (0*y)).
+ intros y ?. apply (left_cancellation (&) (y*0) R _ _).
  now rewrite_on R <-(distribute_l y 0 0), (plus_0_l 0), (plus_0_r (y*0)).
Qed.

Instance ring_semiring `{r: Ring (R:=R)} : SemiRing R.
Proof. destruct r. split; apply _. Qed.

Instance comring_ring `{r: CommutativeRing (R:=R)} : Ring R.
Proof. destruct r. destruct (_:MultiplicativeMonoid R). do 2 (split; try apply _).
  exact right_distr_from_left.
Qed.

Instance comring_comsemiring `{r: CommutativeRing (R:=R)} : CommutativeSemiRing R := {}.

Lemma comsemiring_from_semiring `{SemiRing (R:=R)} : Commutative (.*.) R → CommutativeSemiRing R.
Proof. repeat (split; try apply _). Qed.

Lemma comring_from_ring `{Ring (R:=R)} : Commutative (.*.) R → CommutativeRing R.
Proof. repeat (split; try apply _). Qed.

(** Properness of structure predicates *)

Lemma semirng_proper: Find_Proper_Signature (@SemiRng) 0
  (∀ A Aplus Amult Azero Ae, Proper ((=)==>impl) (@SemiRng A Aplus Amult Azero Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng) 0 _) => eexact semirng_proper : typeclass_instances.

Lemma semiring_proper: Find_Proper_Signature (@SemiRing) 0
  (∀ A Aplus Amult Azero Aone Ae, Proper ((=)==>impl) (@SemiRing A Aplus Amult Azero Aone Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing) 0 _) => eexact semiring_proper : typeclass_instances.

Lemma comsemiring_proper: Find_Proper_Signature (@CommutativeSemiRing) 0
  (∀ A Aplus Amult Azero Aone Ae, Proper ((=)==>impl) (@CommutativeSemiRing A Aplus Amult Azero Aone Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeSemiRing) 0 _) => eexact comsemiring_proper : typeclass_instances.

Lemma rng_proper: Find_Proper_Signature (@Rng) 0
  (∀ A Aplus Amult Azero Anegate Ae,
   Proper ((=)==>impl) (@Rng A Aplus Amult Azero Anegate Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Rng) 0 _) => eexact rng_proper : typeclass_instances.

Lemma ring_proper: Find_Proper_Signature (@Ring) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae,
   Proper ((=)==>impl) (@Ring A Aplus Amult Azero Aone Anegate Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Ring) 0 _) => eexact ring_proper : typeclass_instances.

Lemma comring_proper: Find_Proper_Signature (@CommutativeRing) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae,
   Proper ((=)==>impl) (@CommutativeRing A Aplus Amult Azero Aone Anegate Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeRing) 0 _) => eexact comring_proper : typeclass_instances.

Section semiring_misc.
  Context `{SemiRing (R:=R)}.

  Lemma plus_2_2 : 2 + 2 = 4.
  Proof. subsymmetry. exact (associativity (+) _ _ _). Qed.

  Lemma mult_2_plus_l x `{x ∊ R} : 2 * x = x + x.
  Proof. now rewrite (R $ plus_mult_distr_r _ _ _), (R $ mult_1_l _). Qed.

  Lemma mult_2_plus_r x `{x ∊ R} : x * 2 = x + x.
  Proof. now rewrite (R $ plus_mult_distr_l _ _ _), (R $ mult_1_r _). Qed.

  Lemma mult_2_2 : 2 * 2 = 4.
  Proof. subtransitivity (2+2). exact (mult_2_plus_l 2). exact plus_2_2. Qed.

  Lemma mult_2_comm x `{x ∊ R} : 2 * x = x * 2.
  Proof. subtransitivity (x+x). exact (mult_2_plus_l x). subsymmetry. exact (mult_2_plus_r x). Qed.
End semiring_misc.

Section additive_group_props.
  Context `{Aplus: Plus A} {Azero: Zero A} {Anegate:Negate A} {Ae:Equiv A} {R:@set A}.
  Context `{!AdditiveGroup R}.

  Instance plus_left_cancellation  z `{z ∊ R} :  LeftCancellation (+) z R := group_left_cancellation z.
  Instance plus_right_cancellation z `{z ∊ R} : RightCancellation (+) z R := group_right_cancellation z.

  Instance negate_injective : Injective R R (-) := inverse_injective. 

  Definition negate_involutive x `{x ∊ R} : - - x = x := inverse_involutive x.
  Lemma plus_negate_r x `{x ∊ R} : x + -x = 0. Proof right_inverse (&) x.
  Lemma plus_negate_l x `{x ∊ R} : -x + x = 0. Proof left_inverse (&) x.
  Lemma negate_swap_r x `{x ∊ R} y `{y ∊ R} : x - y = -(y - x).
  Proof. now rewrite_on R -> (inv_sg_op_distr y (-x) : -(y-x) = --x -y), (negate_involutive x). Qed.
  Lemma negate_swap_l x `{x ∊ R} y `{y ∊ R} : -x + y = -(x - y).
  Proof. now rewrite_on R -> (abgroup_inv_distr x (-y) : -(x-y) = -x --y), (negate_involutive y). Qed.
  Lemma negate_plus_distr x `{x ∊ R} y `{y ∊ R} : -(x + y) = -x + -y. Proof abgroup_inv_distr x y.

  Lemma plus_negate_l_split x `{x ∊ R} y `{y ∊ R} : -x + y + x = y.
  Proof.
    rewrite (R $ commutativity (+) (-x) _), <- (R $ associativity (+) _ _ _), (R $ plus_negate_l _).
    exact (plus_0_r _).
  Qed.

  Lemma plus_negate_r_split x `{x ∊ R} y `{y ∊ R} : x + y - x = y.
  Proof. rewrite_on R <- (negate_involutive x) at 1. exact (plus_negate_l_split _ _). Qed.

  Lemma plus_negate_l_split_alt x `{x ∊ R} y `{y ∊ R} : -x + (y + x) = y.
  Proof. rewrite_on R -> (associativity (+) (-x) y x). exact (plus_negate_l_split _ _). Qed.

  Lemma plus_negate_r_split_alt x `{x ∊ R} y `{y ∊ R} : x + (y - x) = y.
  Proof. rewrite_on R -> (associativity (+) x y (-x)). exact (plus_negate_r_split _ _). Qed.

  Lemma plus_plus_negate_l x `{x ∊ R} y `{y ∊ R} : x - y + y = x.
  Proof. rewrite_on R -> (commutativity (+) x (-y)). exact (plus_negate_l_split _ _). Qed.

End additive_group_props.

Hint Extern 2 (LeftCancellation (+) _ _) => eapply @plus_left_cancellation : typeclass_instances.
Hint Extern 2 (RightCancellation (+) _ _) => eapply @plus_right_cancellation : typeclass_instances.
Hint Extern 2 (Injective _ _ (-)) => eapply @negate_injective : typeclass_instances.

Section rng_props.
  Context `{rng: Rng A (R:=R)}.

  Lemma negate_mult_distr_l x `{x ∊ R} y `{y ∊ R} : -(x * y) = -x * y.
  Proof. apply (left_cancellation (+) (x*y) R _ _).
    rewrite_on R -> (plus_negate_r (x*y)), <-(plus_mult_distr_r x (-x) y).
    now rewrite_on R ->(plus_negate_r x), (mult_0_l y).
  Qed.

  Lemma negate_mult_distr_r x `{x ∊ R} y `{y ∊ R} : -(x * y) = x * -y.
  Proof. apply (left_cancellation (+) (x*y) R _ _).
    rewrite_on R -> (plus_negate_r (x*y)), <-(plus_mult_distr_l x y (-y)).
    now rewrite_on R ->(plus_negate_r y), (mult_0_r x).
  Qed.

  Lemma negate_mult_negate x `{x ∊ R} y `{y ∊ R} : -x * -y = x * y.
  Proof. now rewrite_on R <-(negate_mult_distr_l x (-y)), <-(negate_mult_distr_r x y),
                            (negate_involutive (x*y)).
  Qed.

  Lemma negate_0: -0 = 0. Proof inv_mon_unit.

  Lemma mult_minus_distr_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : x * (y - z) = x*y - x*z.
  Proof. rewrite_on R ->(negate_mult_distr_r x z). exact (plus_mult_distr_l x y (-z)). Qed.

  Lemma mult_minus_distr_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : (x - y) * z = x*z - y*z.
  Proof. rewrite_on R ->(negate_mult_distr_l y z). exact (plus_mult_distr_r x (-y) z). Qed.

  Lemma equal_by_zero_sum x `{x ∊ R} y `{y ∊ R} : x - y = 0 ↔ x = y.
  Proof.
    split; intros E.
     rewrite_on R <- (plus_0_l y), <- E, <- (associativity (+) x (-y) y).
     now rewrite_on R ->(plus_negate_l y), (plus_0_r x).
    rewrite_on R ->E. exact (plus_negate_r y).
  Qed.

  Lemma flip_negate x `{x ∊ R} y `{y ∊ R} : -x = y ↔ x = -y.
  Proof. split; intros E. rewrite_on R <-E. subsymmetry. exact (negate_involutive x).
                          rewrite_on R ->E. exact (negate_involutive y). Qed.

  Lemma flip_negate_0 x `{x ∊ R} : -x = 0 ↔ x = 0.
  Proof. rewrite (flip_negate x 0).
    split; intros. now rewrite_on R <- negate_0. now rewrite_on R -> negate_0.
  Qed.

  Lemma negate_zero_prod_l x `{x ∊ R} y `{y ∊ R} : -x * y = 0 ↔ x * y = 0.
  Proof.
    split; intros E.
     apply (injective (-) (x*y) 0). now rewrite_on R -> (negate_mult_distr_l x y), negate_0.
    apply (injective (-) (-x * y) 0). rewrite_on R -> (negate_mult_distr_l (- x) y), negate_0.
    now rewrite_on R ->(negate_involutive x).
  Qed.

  Lemma negate_zero_prod_r x `{x ∊ R} y `{y ∊ R} : x * -y = 0 ↔ x * y = 0.
  Proof.
    split; intros E.
     apply (injective (-) (x*y) 0). now rewrite_on R -> (negate_mult_distr_r x y), negate_0.
    apply (injective (-) (x * -y) 0). rewrite_on R -> (negate_mult_distr_r x (- y)), negate_0.
    now rewrite_on R ->(negate_involutive y).
  Qed.

End rng_props.

Hint Extern 2 (LeftCancellation (+) _ _) => eapply @plus_left_cancellation : typeclass_instances.
Hint Extern 2 (RightCancellation (+) _ _) => eapply @plus_right_cancellation : typeclass_instances.
Hint Extern 2 (Injective _ _ (-)) => eapply @negate_injective : typeclass_instances.

Lemma dec_negate_nonzero `{Rng (R:=R)} `{UnEq _} `{!DenialInequality R} x `{x ∊ R ₀} : -x ∊ R ₀.
Proof. destruct (_ : x ∊ R ₀) as [? E]. red in E. rewrite (denial_inequality _ _) in E.
  split. apply _. red. rewrite (denial_inequality _ _). mc_contradict E. now apply (flip_negate_0 x).
Qed.
(* Hint Extern 15 (-_ ∊ _ ₀) => eapply @dec_negate_nonzero : typeclass_instances. *)

Section ring_props.
  Context `{Ring (R:=R)}.

  Lemma negate_mult x `{x ∊ R} : -x = -1 * x.
  Proof. now rewrite_on R <-(negate_mult_distr_l 1 x), (mult_1_l x). Qed.

End ring_props.

Lemma ZeroDivisor_proper2: Find_Proper_Signature (@ZeroDivisor) 1
  (∀ `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} R `{!InequalitySetoid R}
     `{0 ∊ R} `{!MultiplicativeSemiGroup R},
   Proper ((R,=)==>impl) (ZeroDivisor R)).
Proof. red. intros. intros x x' E [?[y[? Z]]]. unfold_sigs.
  assert (x' ∊ R ₀) by now rewrite_on R <-E. split. trivial. exists_sub y.
  destruct Z; [ left | right ]; now rewrite_on R <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 1 _) => eexact ZeroDivisor_proper2 : typeclass_instances.

Lemma dec_mult_nonzero `{SemiRng A (R:=R)} `{UnEq A} `{!DenialInequality R} `{!NoZeroDivisors R}
  : Closed (R ₀ ⇀ R ₀ ⇀ R ₀) (.*.).
Proof. intros x ? y ?. split. apply _.
  pose proof (no_zero_divisors x) as nzd. red. rewrite (denial_inequality _ _). mc_contradict nzd.
  split. apply _. exists_sub y. now left.
Qed.
(*Hint Extern 21 (Closed (?R ₀ ⇀ ?R ₀ ⇀ ?R ₀) (.*.)) => eapply @dec_mult_nonzero : typeclass_instances.
Hint Extern 12 (?x * ?y ∊ ?R ₀) => eapply @dec_mult_nonzero: typeclass_instances.*)

Instance: ∀ `{SemiRng (R:=R)} `{UnEq _} `{!DenialInequality R}, NonZeroProduct R.
Proof. intros. intros x ? y ? [_ E]. red in E. rewrite (denial_inequality _ _) in E.
  split; (split; [ apply _ |]); red; rewrite (denial_inequality _ _);
  mc_contradict E; rewrite_on R -> E.
  exact (mult_0_l _). exact (mult_0_r _).
Qed.

Section cancellation.
  Context `{Rng A (R:=R)} `{UnEq A} `{!DenialInequality R} `{!NoZeroDivisors R}
          `{∀ `{x ∊ R} `{y ∊ R}, Stable (x=y)}.

  Instance dec_mult_left_cancellation z `{z ∊ R ₀} : LeftCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (z*x) (z*y)) in E.
    rewrite_on R <-(mult_minus_distr_l z x y) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. assert (x-y ∊ R ₀). split. apply _.
      red. now rewrite -> (denial_inequality _ _), (equal_by_zero_sum _ _).
    exists_sub (x-y). tauto.
  Qed.

  Instance dec_mult_right_cancellation z `{z ∊ R ₀} : RightCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (x*z) (y*z)) in E.
    rewrite_on R <-(mult_minus_distr_r x y z) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. assert (x-y ∊ R ₀). split. apply _.
      red. now rewrite -> (denial_inequality _ _), (equal_by_zero_sum _ _).
    exists_sub (x-y). tauto.
  Qed.

End cancellation.

Local Notation U := RingUnits.

Lemma RingUnits_subsetoid `{Mult} `{One _} `{Equiv _} R `{!MultiplicativeMonoid R}
  : U R ⊆ R.
Proof. apply subsetoid_alt; try apply _. intros ? x' E [?[y[??]]]. unfold_sigs.
  split. assumption. exists_sub y. now rewrite_on R <- E.
Qed.
Hint Extern 5 (SubSetoid (U _) _) => eapply @RingUnits_subsetoid : typeclass_instances.

Lemma RingUnits_setoid `{Mult A} `{One A} `{Equiv A} R `{!MultiplicativeMonoid R}
  : Setoid (U R).
Proof subsetoid_a.
Hint Extern 5 (Setoid (U _)) => eapply @RingUnits_setoid : typeclass_instances.

Lemma RingUnits_mult_closed `{Ring (R:=R)} : Closed (U R ⇀ U R ⇀ U R) (.*.).
Proof with try apply _. intros x [?[xi [?[Rx Lx]]]] y [?[yi [?[Ry Ly]]]].
  split... exists_sub (yi * xi). split.
  + rewrite (R $ associativity (.*.) _ _ _), <- (R $ associativity (.*.) x _ _).
    now rewrite_on R -> Ry, (mult_1_r x).
  + rewrite (R $ associativity (.*.) _ _ _), <- (R $ associativity (.*.) yi _ _).
    now rewrite_on R -> Lx, (mult_1_r yi).
Qed.

Local Hint Extern 7 (_ * _ ∊ _) => eapply @RingUnits_mult_closed : typeclass_instances.

(*Local Existing Instance closed_binary.*)

Lemma RingUnits_monoid `{Ring (R:=R)} : MultiplicativeMonoid (U R).
Proof with try apply _. split. split...
+ rewrite (_ : U R ⊆ R)...
+ apply binary_morphism_proper_back.
  change (Proper ((U R,=) ==> (U R,=) ==> (U R,=)) (.*.)).
  pose proof _ : U R ⊆ R.
  intros ?? E1 ?? E2. unfold_sigs. red_sig.
  now rewrite_on R -> E1, E2.
+ change (1 ∊ U R). split... exists_sub 1. split; exact (mult_1_r 1).
+ rewrite (_ : U R ⊆ R)...
+ rewrite (_ : U R ⊆ R)...
Qed.
Hint Extern 5 (MultiplicativeMonoid (U _)) => eapply @RingUnits_monoid : typeclass_instances.

Lemma RingUnits_group `{Ring (R:=R)} `{Inv _}
 `{!Morphism (U R ⇒ U R) (⁻¹)}
 `{!LeftInverse  (.*.) (⁻¹) 1 (U R)}
 `{!RightInverse (.*.) (⁻¹) 1 (U R)}
 : MultiplicativeGroup (U R).
Proof. split; apply _. Qed.

Lemma RingUnits_abgroup `{CommutativeRing (R:=R)} `{Inv _}
 : Morphism (U R ⇒ U R) (⁻¹)
 → LeftInverse  (.*.) (⁻¹) 1 (U R)
 → MultiplicativeAbGroup (U R).
Proof with try apply _. intros.
  assert (Commutative (.*.) (U R)). rewrite (_ : U R ⊆ R)...
  pose proof commonoid_from_monoid : MultiplicativeComMonoid (U R).
  split...
Qed.

Lemma RingUnit_not_zero_divisor `{Ring (R:=R)} `{UnEq _} `{!InequalitySetoid R} x {ru:x ∊ U R} : ¬ZeroDivisor R x.
Proof. destruct ru as [?[y[? [E1 E2]]]]. intros [[??][z[[? zn0][E|E]]]];
  red in zn0; apply (uneq_ne _ _) in zn0; contradict zn0.
+ rewrite_on R <- (mult_1_l z), <- E2.
  rewrite_on R <- (associativity (.*.) y x z), E. exact (mult_0_r y).
+ rewrite_on R <- (mult_1_r z), <- E1.
  rewrite_on R -> (associativity (.*.) z x y), E. exact (mult_0_l y).
Qed.

Lemma RingUnit_left_cancellation `{Ring (R:=R)} z `{z ∊ U R} : LeftCancellation (.*.) z R.
Proof. destruct (_ : z ∊ U R) as [?[y[? [E1 E2]]]]. intros a ? b ? E.
  rewrite_on R <- (mult_1_l a), <- (mult_1_l b), <- E2.
  now rewrite <- !(R $ associativity (.*.) _ _ _), (R $ E).
Qed.

Lemma RingUnit_right_cancellation `{Ring (R:=R)} z `{z ∊ U R} : RightCancellation (.*.) z R.
Proof. destruct (_ : z ∊ U R) as [?[y[? [E1 E2]]]]. intros a ? b ? E.
  rewrite_on R <- (mult_1_r a), <- (mult_1_r b), <- E1.
  now rewrite !(R $ associativity (.*.) _ _ _), (R $ E).
Qed.


Section from_another_semirng.
  Context `{SemiRng (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0).

  Existing Instance injective_mor.

  Instance projected_semirng : SemiRng R2.
  Proof.
    pose proof (projected_com_monoid f plus_correct zero_correct : AdditiveMonoid R2).
    pose proof (projected_sg f mult_correct : MultiplicativeSemiGroup R2).
    split; [ apply _ | apply _ |
      repeat intro; apply (injective f _ _);
      rewrite !(R1 $ mult_correct _ _ _ _), ?(R1 $ plus_correct _ _ _ _),
              ?(R1 $ mult_correct _ _ _ _), ?(R1 $ zero_correct) .. ].
    + exact (plus_mult_distr_l _ _ _).
    + exact (plus_mult_distr_r _ _ _).
    + exact (mult_0_l _).
    + exact (mult_0_r _).
  Qed.
End from_another_semirng.

Section from_another_semiring.
  Context `{SemiRing (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B} `{Bone : One B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2} `{1 ∊ R2}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0) (one_correct : f 1 = 1).

  Instance: SemiRng R2. Proof. now apply (projected_semirng f). Qed.
  Instance: MultiplicativeMonoid R2. Proof. now apply (projected_monoid f). Qed.

  Instance projected_semiring : SemiRing R2.
  Proof. split; try apply _. exact monoid_left_id. exact monoid_right_id. Qed.
End from_another_semiring.

Section from_another_com_semiring.
  Context `{CommutativeSemiRing (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B} `{Bone : One B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2} `{1 ∊ R2}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0) (one_correct : f 1 = 1).

  Instance: SemiRing R2. Proof. now apply (projected_semiring f). Qed.
  Instance: MultiplicativeComMonoid R2. Proof. now apply (projected_com_monoid f). Qed.

  Instance projected_com_semiring : CommutativeSemiRing R2 := {}.
End from_another_com_semiring.

Section from_another_rng.
  Context `{Rng (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B} `{Bnegate : Negate B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2} `{!Closed (R2 ⇀ R2) (-)}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0)
    (negate_correct : ∀ `{x ∊ R2}, f (-x) = -(f x)).

  Instance: SemiRng R2. Proof. now apply (projected_semirng f). Qed.
  Instance: AdditiveGroup R2. Proof. now apply (projected_ab_group f). Qed.

  Instance projected_rng: Rng R2 := {}.
End from_another_rng.

Section from_another_ring.
  Context `{Ring (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B} `{Bone : One B} `{Bnegate : Negate B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2} `{1 ∊ R2} `{!Closed (R2 ⇀ R2) (-)}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0) (one_correct : f 1 = 1)
    (negate_correct : ∀ `{x ∊ R2}, f (-x) = -(f x)).

  Instance: SemiRing R2. Proof. now apply (projected_semiring f). Qed.
  Instance: Rng R2. Proof. now apply (projected_rng f). Qed.

  Instance projected_ring: Ring R2 := {}.
End from_another_ring.

Section from_another_com_ring.
  Context `{CommutativeRing (R:=R1)}.
  Context `{Setoid B (S:=R2)} (f : R2 ⇀ R1) `{!Injective R2 R1 f}
   `{Bplus : Plus B} `{Bmult : Mult B} `{Bzero : Zero B} `{Bone : One B} `{Bnegate : Negate B}
   `{!Closed (R2 ⇀ R2 ⇀ R2) (+)} `{!Closed (R2 ⇀ R2 ⇀ R2) (.*.)} `{0 ∊ R2} `{1 ∊ R2} `{!Closed (R2 ⇀ R2) (-)}
    (plus_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x + y) = f x + f y)
    (mult_correct : ∀ `{x ∊ R2} `{y ∊ R2}, f (x * y) = f x * f y)
    (zero_correct : f 0 = 0) (one_correct : f 1 = 1)
    (negate_correct : ∀ `{x ∊ R2}, f (-x) = -(f x)).

  Instance: CommutativeSemiRing R2. Proof. now apply (projected_com_semiring f). Qed.
  Instance: Ring R2. Proof. now apply (projected_ring f). Qed.

  Instance projected_com_ring: CommutativeRing R2 := {}.
End from_another_com_ring.




Local Existing Instance srngmor_a.
Local Existing Instance srngmor_b.
Local Existing Instance sringmor_a.
Local Existing Instance sringmor_b.
(*
Local Existing Instance rngmor_a.
Local Existing Instance rngmor_b.
Local Existing Instance ringmor_a.
Local Existing Instance ringmor_b.
*)

Section semirng_morphisms.
  Context `{R1:set} `{R2:set} {f : R1 ⇀ R2} `{SemiRng _ (R:=R1)} `{SemiRng _ (R:=R2)}
    `{!AdditiveMonoid_Morphism R1 R2 f} `{!MultiplicativeSemiGroup_Morphism R1 R2 f}.

  Lemma preserves_plus x `{x ∊ R1} y `{y ∊ R1} : f (x+y) = f x + f y. Proof preserves_sg_op x y.
  Lemma preserves_mult x `{x ∊ R1} y `{y ∊ R1} : f (x*y) = f x * f y. Proof preserves_sg_op x y.
  Lemma preserves_0: f 0 = 0. Proof preserves_mon_unit.

End semirng_morphisms.

Section semiring_morphisms.
  Context `{R1:set} `{R2:set} {f : R1 ⇀ R2} `{SemiRing _ (R:=R1)} `{SemiRing _ (R:=R2)}
    `{!SemiRing_Morphism R1 R2 f}.

  Lemma preserves_2 : f 2 = 2.
  Proof. now rewrite (R2 $ preserves_plus _ _), (R2 $ preserves_1). Qed.

  Lemma preserves_3 : f 3 = 3.
  Proof. now rewrite (R2 $ preserves_plus _ _), (R2 $ preserves_1), (R2 $ preserves_2). Qed.

  Lemma preserves_4 : f 4 = 4.
  Proof. now rewrite (R2 $ preserves_plus _ _), (R2 $ preserves_1), (R2 $ preserves_3). Qed.

End semiring_morphisms.

(*
Instance rng_morphism_is_srng_morphism `{Rng_Morphism (R:=R1) (S:=R2) (f:=f)}
  : SemiRng_Morphism R1 R2 f := {}.
*)

Section rng_morphisms.
  Context `{Aplus: Plus A} {Azero: Zero A} {Anegate:Negate A} {Ae:Equiv A} {R1:@set A}.
  Context `{Bplus: Plus B} {Bzero: Zero B} {Bnegate:Negate B} {Be:Equiv B} {R2:@set B}.
  Context `{!AdditiveGroup R1} `{!AdditiveGroup R2}.

  Context {f : R1 ⇀ R2} `{!AdditiveSemiGroup_Morphism R1 R2 f}.

  Lemma preserves_negate x `{x ∊ R1} : f (-x) = - f x. Proof preserves_inverse x.
  Lemma preserves_minus x `{x ∊ R1} y `{y ∊ R1} : f (x - y) = f x - f y.
  Proof. now rewrite (R2 $ preserves_plus _ _), (R2 $ preserves_negate _). Qed.

End rng_morphisms.

(*
Instance ring_morphism_is_sring_morphism `{Ring_Morphism (R:=R) (S:=R') (f:=f)} 
 : SemiRing_Morphism R R' f.
Proof. split; try apply _. change (elt_type (R ⇀ R')) in f.
  destruct ringmor_1 as [x [? E]].
  rewrite_on R' <- (mult_1_r (f 1)), <- E, <- (preserves_mult 1 x).
  now rewrite_on R -> (mult_1_l x).
Qed.
*)

Lemma semirng_morphism_alt `{R:set} `{S:set}
  (f:R ⇀ S) `{SemiRng _ (R:=R)} `{SemiRng _ (R:=S)} :
  Morphism (R ⇒ S) f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 0 = 0
  → SemiRng_Morphism R S f.
Proof. intros ? fplus fmult f0. repeat (split; try apply _); assumption. Qed.

Lemma semiring_morphism_alt `{R:set} `{S:set}
  (f:R ⇀ S) `{SemiRing _ (R:=R)} `{SemiRing _ (R:=S)} :
  Morphism (R ⇒ S) f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 0 = 0
  → f 1 = 1
  → SemiRing_Morphism R S f.
Proof. intros ? fplus fmult f0 f1. repeat (split; try apply _); assumption. Qed.

Lemma rng_morphism_alt `{R:set} `{S:set}
  (f:R ⇀ S) `{Rng _ (R:=R)} `{Rng _ (R:=S)} :
  Morphism (R ⇒ S) f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → SemiRng_Morphism R S f.
Proof. intros ? fplus fmult. split; try apply _;
  [cut (AdditiveSemiGroup_Morphism R S f); try apply _|];
  split; try apply _; assumption.
Qed.

Lemma ring_morphism_alt `{R:set} `{S:set}
  (f:R ⇀ S) `{Ring _ (R:=R)} `{Ring _ (R:=S)} :
  Morphism (R ⇒ S) f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 1 = 1
  → SemiRing_Morphism R S f.
Proof. intros ? fplus fmult f1.
  assert (SemiRng_Morphism R S f) by now apply (rng_morphism_alt f).
  repeat (split; try apply _); trivial.
Qed.

Instance: ∀ `{SemiRng (R:=R)} `{x ∊ R}, AdditiveMonoid_Morphism R R (x *.).
Proof. intros. apply (monoid_morphism_alt _ _).
+ exact (plus_mult_distr_l _).
+ exact (mult_0_r _).
Qed.

Instance: ∀ `{SemiRng (R:=R)} `{x ∊ R}, AdditiveMonoid_Morphism R R (.* x).
Proof. intros. apply (monoid_morphism_alt _ _).
+ intros. exact (plus_mult_distr_r _ _ _).
+ exact (mult_0_l _).
Qed.

Lemma semirng_morphism_proper: Find_Proper_Signature (@SemiRng_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Bplus Bmult Bzero R S,
    Proper ((@equiv (R ⇀ S) _) ==> impl)
   (@SemiRng_Morphism A Ae B Be Aplus Amult Azero Bplus Bmult Bzero R S)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng_Morphism) 0 _) => eexact semirng_morphism_proper : typeclass_instances.

Lemma semiring_morphism_proper: Find_Proper_Signature (@SemiRing_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone R S,
    Proper ((@equiv (R ⇀ S) _) ==> impl)
   (@SemiRing_Morphism A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone R S)).
Proof. red; intros. intros f g E ?. split; try apply _. rewrite <- E; apply _.
  rewrite <- (E 1 1); try now red_sig. exact preserves_1.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing_Morphism) 0 _) => eexact semiring_morphism_proper : typeclass_instances.

Lemma semirng_morphism_proper2: Find_Proper_Signature (@SemiRng_Morphism) 1
  (∀ A Ae B Be Aplus Amult Azero Bplus Bmult Bzero,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@SemiRng_Morphism A Ae B Be Aplus Amult Azero Bplus Bmult Bzero)).
Proof. structure_mor_proper. rewrite <-ES, <-ET. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng_Morphism) 1 _) => eexact semirng_morphism_proper2 : typeclass_instances.

Lemma semiring_morphism_proper2: Find_Proper_Signature (@SemiRing_Morphism) 1
  (∀ A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@SemiRing_Morphism A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone)).
Proof. structure_mor_proper. assumption. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing_Morphism) 1 _) => eexact semiring_morphism_proper2 : typeclass_instances.

Hint Extern 0 (?S ∊ SemiRng)  => red; apply _ : typeclass_instances.
Hint Extern 0 (?S ∊ SemiRing) => red; apply _ : typeclass_instances.
Hint Extern 0 (?S ∊ Rng)      => red; apply _ : typeclass_instances.
Hint Extern 0 (?S ∊ Ring)     => red; apply _ : typeclass_instances.

Lemma semirng_morphism_proper3: Find_Proper_Signature (@SemiRng_Morphism) 2
  (∀ A Ae B Be Aplus Amult Azero Bplus Bmult Bzero,
    Proper ((SemiRng,⊆) --> (SemiRng,⊆) ++> eq ==> impl)
   (@SemiRng_Morphism A Ae B Be Aplus Amult Azero Bplus Bmult Bzero)).
Proof. structure_mor_proper3 EX EY.
  rewrite (Monoid $ EX), <-(Monoid $ EY). apply _.
  rewrite (SemiGroup $ EX), <-(SemiGroup $ EY). apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng_Morphism) 2 _) => eexact semirng_morphism_proper3 : typeclass_instances.

Lemma semiring_morphism_proper3: Find_Proper_Signature (@SemiRing_Morphism) 2
  (∀ A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone,
    Proper ((SemiRing,⊆) --> (SemiRing,⊆) ++> eq ==> impl)
   (@SemiRing_Morphism A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone)).
Proof. structure_mor_proper3 EX EY.
  rewrite (SemiRng $ EX), <-(SemiRng $ EY). apply _.
  exact preserves_1.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing_Morphism) 2 _) => eexact semiring_morphism_proper3 : typeclass_instances.

(* The identity morphism; covers also the injection from a sub semirng *)
Lemma id_semirng_mor `(R:set) S `{!Subset R S} `{SemiRng _ (R:=R)} `{!SemiRng S} : SemiRng_Morphism R S id.
Proof. split; apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ id) => eapply @id_semirng_mor : typeclass_instances.

Lemma id_semiring_mor `(R:set) S `{!Subset R S} `{SemiRing _ (R:=R)} `{!SemiRing S} : SemiRing_Morphism R S id.
Proof. split; try apply _. subreflexivity. Qed.
Hint Extern 4 (SemiRing_Morphism _ _ id) => eapply @id_semiring_mor : typeclass_instances.

Lemma compose_semirng_morphism `{SemiRng (R:=R)} `{S:set} `{SemiRng _ (R:=S)} `{SemiRng (R:=T)}
  (f:R ⇀ S) (g:S ⇀ T) `{!SemiRng_Morphism R S f} `{!SemiRng_Morphism S T g}: SemiRng_Morphism R T (g ∘ f).
Proof. split; try apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ (_ ∘ _)) => class_apply @compose_semirng_morphism : typeclass_instances.

Lemma compose_semiring_morphism `{SemiRing (R:=R)} `{S:set} `{SemiRing _ (R:=S)} `{SemiRing (R:=T)}
  (f:R ⇀ S) (g:S ⇀ T) `{!SemiRing_Morphism R S f} `{!SemiRing_Morphism S T g}: SemiRing_Morphism R T (g ∘ f).
Proof. split; try apply _.
  unfold compose. rewrite (S $ preserves_1). exact preserves_1.
Qed.
Hint Extern 4 (SemiRing_Morphism _ _ (_ ∘ _)) => class_apply @compose_semiring_morphism : typeclass_instances.

Local Open Scope mc_fun_scope.

Lemma invert_semirng_morphism `{R:set} `{S:set}
 (f:R ⇀ S) `{SemiRng_Morphism _ _ (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  SemiRng_Morphism S R f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ (inverse _)) => eapply @invert_semirng_morphism : typeclass_instances.

Lemma invert_semiring_morphism `{R:set} `{S:set}
 (f:R ⇀ S) `{SemiRing_Morphism _ _ (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  SemiRing_Morphism S R f⁻¹.
Proof. split; try apply _.
  apply (injective f _ _).
  now rewrite (S $ preserves_1), (S $ surjective_applied _ _).
Qed.
Hint Extern 4 (SemiRing_Morphism _ _ (inverse _)) => eapply @invert_semiring_morphism : typeclass_instances.

