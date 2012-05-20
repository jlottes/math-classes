Require Import
  abstract_algebra theory.setoids theory.common_props theory.jections theory.groups.

(* Operations are closed and proper *)

Section plus.
  Context `{Aplus: Plus A} {Azero: Zero A} {Ae:Equiv A} {R:Subset A}.
  Context `{!AdditiveMonoid R}.

  Lemma plus_closed : Closed (R ==> R ==> R) (+). Proof sg_op_closed.

  Lemma plus_0_l: LeftIdentity (+) 0 R. Proof _.
  Lemma plus_0_r: RightIdentity (+) 0 R. Proof _.
End plus.
Arguments plus_0_l {A Aplus Azero Ae R _} _ {_}.
Arguments plus_0_r {A Aplus Azero Ae R _} _ {_}.

Hint Extern 20 (Closed (_==>_==>_) (+)) => eapply @plus_closed : typeclass_instances.
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

Lemma mult_closed `{Mult A} `{Equiv A} {R} `{!MultiplicativeSemiGroup R}
  : Closed (R ==> R ==> R) (.*.).
Proof sg_op_closed.

Hint Extern 20 (Closed (_==>_==>_) (.*.)) => eapply @mult_closed : typeclass_instances.
Hint Extern 5 (_ * _ ∊ _) => eapply @mult_closed : typeclass_instances. 

Lemma negate_closed `{Plus A} `{Zero A} `{Negate A} `{Equiv A} {R} `{!AdditiveGroup R}
  : Closed (R ==> R) (-).
Proof _.

Hint Extern 5 (- _ ∊ _) => eapply @negate_closed : typeclass_instances. 

Lemma negate_proper: Find_Proper_Signature (@negate) 0
  (∀ `{Plus A} `{Zero A} `{Negate A} `{Equiv A} R `{!AdditiveGroup R},
   Proper ((R,=)==>(R,=)) (-)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@negate) 0 _) => eexact negate_proper : typeclass_instances.


(* Deducible structure instances *)

Instance semiring_mult_monoid `{sr: SemiRing (R:=R)} : MultiplicativeMonoid R.
Proof. destruct sr. split; apply _. Qed.

Instance comsemiring_semiring `{csr: CommutativeSemiRing (R:=R)} : SemiRing R.
Proof. destruct csr. destruct (_:MultiplicativeMonoid R). do 2 (split; try apply _).
  exact right_distr_from_left. exact right_absorb_from_left.
Qed.

Instance rng_semirng `{r: Rng (R:=R)} : SemiRng R.
Proof. destruct r. split; try apply _.
+ intros y ?. apply (right_cancellation (+) (0*y) R _ _).
  now rewrite_on R <-(distribute_r 0 0 y), (plus_0_r 0), (plus_0_l (0*y)).
+ intros y ?. apply (left_cancellation (+) (y*0) R _ _).
  now rewrite_on R <-(distribute_l y 0 0), (plus_0_l 0), (plus_0_r (y*0)).
Qed.

Instance ring_semiring `{r: Ring (R:=R)} : SemiRing R.
Proof. destruct r. split; apply _. Qed.

Instance comring_ring `{r: CommutativeRing (R:=R)} : Ring R.
Proof. destruct r. destruct (_:MultiplicativeMonoid R). do 2 (split; try apply _).
  exact right_distr_from_left.
Qed.

Instance comring_comsemiring `{r: CommutativeRing (R:=R)} : CommutativeSemiRing R := {}.


(* Properness of structure predicates *)

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

Lemma intdomain_proper: Find_Proper_Signature (@IntegralDomain) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae Aue,
   Proper ((=)==>impl) (@IntegralDomain A Aplus Amult Azero Aone Anegate Ae Aue)).
Proof with try apply _. red. intros. intros S T E. destruct 1. split...
  rewrite <- E... rewrite <- E...
  intros ? el ? el2. rewrite <- E in el, el2 |- *...
  intros ? el. rewrite <- E in el |- *...
Qed.
Hint Extern 0 (Find_Proper_Signature (@IntegralDomain) 0 _) => eexact intdomain_proper : typeclass_instances.

Section rng_props.
  Context `{rng: Rng A (R:=R)}.

  Definition negate_involutive x `{x ∊ R} : - - x = x := inverse_involutive x _.
  Lemma plus_negate_r x `{x ∊ R} : x + -x = 0. Proof right_inverse (&) x.
  Lemma plus_negate_l x `{x ∊ R} : -x + x = 0. Proof left_inverse (&) x.
  Lemma negate_swap_r x `{x ∊ R} y `{y ∊ R} : x - y = -(y - x).
  Proof. now rewrite_on R -> (inv_sg_op_distr y (-x) : -(y-x) = --x -y), (negate_involutive x). Qed.
  Lemma negate_swap_l x `{x ∊ R} y `{y ∊ R} : -x + y = -(x - y).
  Proof. now rewrite_on R -> (abgroup_inv_distr x (-y) : -(x-y) = -x --y), (negate_involutive y). Qed.
  Lemma negate_plus_distr x `{x ∊ R} y `{y ∊ R} : -(x + y) = -x + -y. Proof abgroup_inv_distr x y.

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

(*
  Lemma flip_negate_ne_0 x `{x ∊ R} : -x ≠ 0 ↔ x ≠ 0.
  Proof. split; intros E ?; apply E; now apply flip_negate_0. Qed.
*)

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

End rng_props.

Lemma negate_nonzero `{Rng A (R:=R)} `{UnEq A} `{!StandardUnEq R} x `{x ∊ R ₀} : -x ∊ R ₀.
Proof. destruct (_ : x ∊ R ₀) as [_ E]. rewrite (standard_uneq _ _) in E.
  split. apply _. rewrite (standard_uneq _ _). mc_contradict E. now apply (flip_negate_0 x).
Qed.
Hint Extern 4 (-_ ∊ _ ₀) => eapply @negate_nonzero : typeclass_instances.

Section ring_props.
  Context `{Ring (R:=R)}.
  Lemma negate_mult x `{x ∊ R} : -x = -1 * x.
  Proof. now rewrite_on R <-(negate_mult_distr_l 1 x), (mult_1_l x). Qed.
End ring_props.

Lemma ZeroDivisor_proper2: Find_Proper_Signature (@ZeroDivisor) 1
  (∀ `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} R `{!UnEqualitySetoid R}
     `{0 ∊ R} `{!MultiplicativeSemiGroup R},
   Proper ((R,=)==>impl) (ZeroDivisor R)).
Proof. red. intros. intros x x' E [?[y[? Z]]]. unfold_sigs.
  assert (x' ∊ R ₀) by now rewrite_on R <-E. split. trivial. exists_sub y.
  destruct Z; [ left | right ]; now rewrite_on R <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 1 _) => eexact ZeroDivisor_proper2 : typeclass_instances.

Lemma mult_nonzero `{SemiRng A (R:=R)} `{UnEq A} `{!StandardUnEq R} `{!NoZeroDivisors R}
  : Closed (R ₀ ==> R ₀ ==> R ₀) (.*.).
Proof. intros x ? y ?. split. apply _.
  pose proof (no_zero_divisors x) as nzd. rewrite (standard_uneq _ _). mc_contradict nzd.
  split. apply _. exists_sub y. now left.
Qed.
Hint Extern 20 (Closed (?R ₀ ==> ?R ₀ ==> ?R ₀) (.*.)) => eapply @mult_nonzero : typeclass_instances.
Hint Extern 4 (?x * ?y ∊ ?R ₀) => eapply @mult_nonzero: typeclass_instances.

Instance: ∀ `{SemiRng A (R:=R)} `{UnEq A} `{!StandardUnEq R}, NonZeroProduct R.
Proof. intros. intros x ? y ? [_ E]. rewrite (standard_uneq _ _) in E.
  split; (split; [ apply _ |]); rewrite (standard_uneq _ _);
  mc_contradict E; rewrite_on R -> E.
  exact (mult_0_l _). exact (mult_0_r _).
Qed.

Section cancellation.
  Context `{Rng A (R:=R)} `{UnEq A} `{!StandardUnEq R} `{!NoZeroDivisors R}
          `{∀ `{x ∊ R} `{y ∊ R}, Stable (x=y)}.

  Global Instance mult_left_cancellation z `{z ∊ R ₀} : LeftCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (z*x) (z*y)) in E.
    rewrite_on R <-(mult_minus_distr_l z x y) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. assert (x-y ∊ R ₀). split. apply _.
      now rewrite -> (standard_uneq _ _), (equal_by_zero_sum _ _).
    exists_sub (x-y). tauto.
  Qed.

  Global Instance mult_right_cancellation z `{z ∊ R ₀} : RightCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (x*z) (y*z)) in E.
    rewrite_on R <-(mult_minus_distr_r x y z) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. assert (x-y ∊ R ₀). split. apply _.
      now rewrite -> (standard_uneq _ _), (equal_by_zero_sum _ _).
    exists_sub (x-y). tauto.
  Qed.

End cancellation.

Hint Extern 10 (Closed (?R ₀ ==> ?R ₀ ==> ?R ₀) (.*.)) => eapply @intdom_nozeroes.
Hint Extern 4 (?x * ?y ∊ ?R ₀) => eapply @intdom_nozeroes : typeclass_instances.

Lemma intdom_nozerodivs `{IntegralDomain (R:=R)} : NoZeroDivisors R.
Proof. intros x [?[y[?[E|E]]]]; contradict E; apply (uneq_ne _ _).
  now destruct (_ : x * y ∊ R ₀). now destruct (_ : y * x ∊ R ₀).
Qed.

Lemma dec_intdom `{CommutativeRing A (R:=R)} `{UnEq A} `{!StandardUnEq R}
  `{PropHolds (1 ≠ 0)} `{!NoZeroDivisors R} `{∀ `{x ∊ R} `{y ∊ R}, Stable (x=y)}
  : IntegralDomain R.
Proof. split; apply _. Qed.

Local Notation U := RingUnits.

Lemma RingUnits_subsetoid `{Mult A} `{One A} `{Equiv A} R `{!MultiplicativeMonoid R}
  : SubSetoid (U R) R.
Proof. split. apply _. split. apply _. intros ? x' E [?[y[??]]]. unfold_sigs.
  split. assumption. exists_sub y. now rewrite_on R <- E.
Qed.
Hint Extern 5 (SubSetoid (U _) _) => eapply @RingUnits_subsetoid : typeclass_instances.

Lemma RingUnits_setoid `{Mult A} `{One A} `{Equiv A} R `{!MultiplicativeMonoid R}
  : Setoid (U R).
Proof subsetoid_a.
Hint Extern 5 (Setoid (U _)) => eapply @RingUnits_setoid : typeclass_instances.

Lemma RingUnits_mult_closed `{Ring (R:=R)} : Closed (U R ==> U R ==> U R) (.*.).
Proof with try apply _. intros x [?[xi [?[Rx Lx]]]] y [?[yi [?[Ry Ly]]]].
  split... exists_sub (yi * xi). split.
  + rewrite (R $ associativity (.*.) _ _ _), <- (R $ associativity (.*.) x _ _).
    now rewrite_on R -> Ry, (mult_1_r x).
  + rewrite (R $ associativity (.*.) _ _ _), <- (R $ associativity (.*.) yi _ _).
    now rewrite_on R -> Lx, (mult_1_r yi).
Qed.

Lemma RingUnits_monoid `{Ring (R:=R)} : MultiplicativeMonoid (U R).
Proof with try apply _. split. split...
+ rewrite (_ : U R ⊆ R)...
+ split... change (Proper ((U R,=) ==> (U R,=) ==> (U R,=)) (.*.)).
  pose proof RingUnits_mult_closed. pose proof _ : U R ⊆ R.
  intros ?? E1 ?? E2. unfold_sigs. red_sig.
  now rewrite_on R -> E1, E2.
+ change (1 ∊ U R). split... exists_sub 1. split; exact (mult_1_r 1).
+ rewrite (_ : U R ⊆ R)...
+ rewrite (_ : U R ⊆ R)...
Qed.
Hint Extern 5 (MultiplicativeMonoid (U _)) => eapply @RingUnits_monoid : typeclass_instances.

Lemma RingUnits_group `{Ring (R:=R)} `{Inv A}
 `{!Setoid_Morphism (U R) (U R) (⁻¹)}
 `{!LeftInverse  (.*.) (⁻¹) 1 (U R)}
 `{!RightInverse (.*.) (⁻¹) 1 (U R)}
 : MultiplicativeGroup (U R).
Proof. split; apply _. Qed.

Lemma RingUnits_abgroup `{CommutativeRing (R:=R)} `{Inv A}
 : Setoid_Morphism (U R) (U R) (⁻¹)
 → LeftInverse  (.*.) (⁻¹) 1 (U R)
 → MultiplicativeAbGroup (U R).
Proof with try apply _. intros.
  assert (Commutative (.*.) (U R)). rewrite (_ : U R ⊆ R)...
  pose proof commonoid_from_monoid : MultiplicativeComMonoid (U R).
  split...
Qed.

Lemma RingUnit_not_zero_divisor `{Ring A (R:=R)} `{UnEq A} `{!UnEqualitySetoid R} x {ru:x ∊ U R} : ¬ZeroDivisor R x.
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




Local Existing Instance srngmor_a.
Local Existing Instance srngmor_b.
Local Existing Instance sringmor_a.
Local Existing Instance sringmor_b.
Local Existing Instance rngmor_a.
Local Existing Instance rngmor_b.
Local Existing Instance ringmor_a.
Local Existing Instance ringmor_b.

Section semirng_morphisms.
  Context `{SemiRng (R:=R1)} `{SemiRng (R:=R2)} {f : R1 ⇀ R2} `{!SemiRng_Morphism R1 R2 f}.

  Lemma preserves_plus x `{x ∊ R1} y `{y ∊ R1} : f (x+y) = f x + f y. Proof preserves_sg_op x y.
  Lemma preserves_mult x `{x ∊ R1} y `{y ∊ R1} : f (x*y) = f x * f y. Proof preserves_sg_op x y.
  Lemma preserves_0: f 0 = 0. Proof preserves_mon_unit.

End semirng_morphisms.

Section rng_morphisms.
  Context `{Rng (R:=R1)} `{Rng (R:=R2)} {f : R1 ⇀ R2} `{!Rng_Morphism R1 R2 f}.

  Global Instance rng_morphism_is_srng_morphism : SemiRng_Morphism R1 R2 f := {}.

  Lemma preserves_negate x `{x ∊ R1} : f (-x) = - f x. Proof preserves_inverse x.

End rng_morphisms.

Instance ring_morphism_is_sring_morphism `{Ring_Morphism (R:=R) (S:=R') (f:=f)} 
 : SemiRing_Morphism R R' f.
Proof. split; try apply _.
  destruct ringmor_1 as [x [? E]].
  rewrite_on R' <- (mult_1_r (f 1)), <- E, <- (preserves_mult 1 x).
  now rewrite_on R -> (mult_1_l x).
Qed.

Lemma semirng_morphism_alt {A B} `{R:Subset A} `{S:Subset B}
  (f:R ⇀ S) `{SemiRng A (R:=R)} `{SemiRng B (R:=S)} :
  Setoid_Morphism R S f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 0 = 0
  → SemiRng_Morphism R S f.
Proof. intros ? fplus fmult f0. repeat (split; try apply _); assumption. Qed.

Lemma semiring_morphism_alt {A B} `{R:Subset A} `{S:Subset B}
  (f:R ⇀ S) `{SemiRing A (R:=R)} `{SemiRing B (R:=S)} :
  Setoid_Morphism R S f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 0 = 0
  → f 1 = 1
  → SemiRing_Morphism R S f.
Proof. intros ? fplus fmult f0 f1. repeat (split; try apply _); assumption. Qed.

Lemma rng_morphism_alt {A B} `{R:Subset A} `{S:Subset B}
  (f:R ⇀ S) `{Rng A (R:=R)} `{Rng B (R:=S)} :
  Setoid_Morphism R S f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → Rng_Morphism R S f.
Proof. intros ? fplus fmult. repeat (split; try apply _); assumption. Qed.

Lemma ring_morphism_alt {A B} `{R:Subset A} `{S:Subset B}
  (f:R ⇀ S) `{Ring A (R:=R)} `{Ring B (R:=S)} :
  Setoid_Morphism R S f
  → (∀ `{x ∊ R} `{y ∊ R}, f (x + y) = f x + f y)
  → (∀ `{x ∊ R} `{y ∊ R}, f (x * y) = f x * f y)
  → f 1 = 1
  → Ring_Morphism R S f.
Proof. intros ? fplus fmult f1. repeat (split; try apply _); trivial. now exists_sub (1:A). Qed.

Lemma semirng_morphism_proper: Find_Proper_Signature (@SemiRng_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Bplus Bmult Bzero,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@SemiRng_Morphism A Ae B Be Aplus Amult Azero Bplus Bmult Bzero)).
Proof. structure_mor_proper. rewrite <-ES, <-ET. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng_Morphism) 0 _) => eexact semirng_morphism_proper : typeclass_instances.

Lemma semiring_morphism_proper: Find_Proper_Signature (@SemiRing_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@SemiRing_Morphism A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone)).
Proof. structure_mor_proper. assumption. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing_Morphism) 0 _) => eexact semiring_morphism_proper : typeclass_instances.

Lemma rng_morphism_proper: Find_Proper_Signature (@Rng_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Anegate Bplus Bmult Bzero Bnegate,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@Rng_Morphism A Ae B Be Aplus Amult Azero Anegate Bplus Bmult Bzero Bnegate)).
Proof. structure_mor_proper. rewrite <-ES, <-ET. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@Rng_Morphism) 0 _) => eexact rng_morphism_proper : typeclass_instances.

Lemma ring_morphism_proper: Find_Proper_Signature (@Ring_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Aone Anegate Bplus Bmult Bzero Bone Bnegate,
    Proper ((=) ==> (=) ==> eq ==> impl)
   (@Ring_Morphism A Ae B Be Aplus Amult Azero Aone Anegate Bplus Bmult Bzero Bone Bnegate)).
Proof. structure_mor_proper.
  destruct ringmor_1 as [x [el ?]]. rewrite ES in el. now exists_sub x.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Ring_Morphism) 0 _) => eexact ring_morphism_proper : typeclass_instances.

(* The identity morphism; covers also the injection from a sub semirng *)
Lemma id_semirng_mor `(R:Subset A) S `{R ⊆ S} `{SemiRng A (R:=R)} `{!SemiRng S} : SemiRng_Morphism R S id.
Proof. split; apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ id) => class_apply @id_semirng_mor : typeclass_instances.

Lemma id_semiring_mor `(R:Subset A) S `{R ⊆ S} `{SemiRing A (R:=R)} `{!SemiRing S} : SemiRing_Morphism R S id.
Proof. split; try apply _. subreflexivity. Qed.
Hint Extern 4 (SemiRing_Morphism _ _ id) => class_apply @id_semiring_mor : typeclass_instances.

Lemma id_rng_mor `(R:Subset A) S `{R ⊆ S} `{Rng A (R:=R)} `{!Rng S} : Rng_Morphism R S id.
Proof. split; apply _. Qed.
Hint Extern 4 (Rng_Morphism _ _ id) => class_apply @id_rng_mor : typeclass_instances.

Lemma id_ring_mor `(R:Subset A) S `{R ⊆ S} `{Ring A (R:=R)} `{!Ring S} : Ring_Morphism R S id.
Proof. split; try apply _. now exists_sub 1. Qed.
Hint Extern 4 (Ring_Morphism _ _ id) => class_apply @id_ring_mor : typeclass_instances.

Lemma compose_semirng_morphism `{SemiRng (R:=R)} `{S:Subset B} `{SemiRng B (R:=S)} `{SemiRng (R:=T)}
  f g `{!SemiRng_Morphism R S f} `{!SemiRng_Morphism S T g}: SemiRng_Morphism R T (g ∘ f).
Proof. split; try apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ (_ ∘ _)) => class_apply @compose_semirng_morphism : typeclass_instances.

Lemma compose_semiring_morphism `{SemiRing (R:=R)} `{S:Subset B} `{SemiRing B (R:=S)} `{SemiRing (R:=T)}
  f g `{!SemiRing_Morphism R S f} `{!SemiRing_Morphism S T g}: SemiRing_Morphism R T (g ∘ f).
Proof. split; try apply _.
  unfold compose. rewrite_on S -> preserves_1. exact preserves_1.
Qed.
Hint Extern 4 (SemiRing_Morphism _ _ (_ ∘ _)) => class_apply @compose_semiring_morphism : typeclass_instances.

Lemma compose_rng_morphism `{Rng (R:=R)} `{S:Subset B} `{Rng B (R:=S)} `{Rng (R:=T)}
  f g `{!Rng_Morphism R S f} `{!Rng_Morphism S T g}: Rng_Morphism R T (g ∘ f).
Proof. split; try apply _. Qed.
Hint Extern 4 (Rng_Morphism _ _ (_ ∘ _)) => class_apply @compose_rng_morphism : typeclass_instances.

Lemma compose_ring_morphism `{Ring (R:=R)} `{S:Subset B} `{Ring B (R:=S)} `{Ring (R:=T)}
  f g `{!Ring_Morphism R S f} `{!Ring_Morphism S T g}: Ring_Morphism R T (g ∘ f).
Proof. split; try apply _. exists_sub 1.
  unfold compose. rewrite_on S -> preserves_1. exact preserves_1.
Qed.
Hint Extern 4 (Ring_Morphism _ _ (_ ∘ _)) => class_apply @compose_ring_morphism : typeclass_instances.

Local Open Scope mc_fun_scope.

Lemma invert_semirng_morphism {A B} `{R:Subset A} `{S:Subset B}
 (f:R ⇀ S) `{SemiRng_Morphism A B (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  SemiRng_Morphism S R f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (SemiRng_Morphism _ _ (inverse _)) => eapply @invert_semirng_morphism : typeclass_instances.

Lemma invert_semiring_morphism {A B} `{R:Subset A} `{S:Subset B}
 (f:R ⇀ S) `{SemiRing_Morphism A B (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  SemiRing_Morphism S R f⁻¹.
Proof. split; try apply _.
  apply (injective f _ _).
  now rewrite (S $ preserves_1), (S $ surjective_applied _ _).
Qed.
Hint Extern 4 (SemiRing_Morphism _ _ (inverse _)) => eapply @invert_semiring_morphism : typeclass_instances.

Lemma invert_rng_morphism {A B} `{R:Subset A} `{S:Subset B}
 (f:R ⇀ S) `{Rng_Morphism A B (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  Rng_Morphism S R f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (Rng_Morphism _ _ (inverse _)) => eapply @invert_rng_morphism : typeclass_instances.

Lemma invert_ring_morphism {A B} `{R:Subset A} `{S:Subset B}
  (f:R ⇀ S) `{Ring_Morphism A B (R:=R) (S:=S) (f:=f)} `{!Inverse f} `{!Bijective R S f} :
  Ring_Morphism S R f⁻¹.
Proof. split; try apply _.
  exists_sub (1:B).
  apply (injective f _ _).
  now rewrite (S $ preserves_1), (S $ surjective_applied _ _).
Qed.
Hint Extern 4 (Ring_Morphism _ _ (inverse _)) => eapply @invert_ring_morphism : typeclass_instances.
