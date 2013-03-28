Require Import
  abstract_algebra interfaces.orders orders.rings
  theory.strong_setoids theory.rings.

Local Open Scope mc_abs_scope.

Hint Extern 20 (Closed _ _ abs) => eapply abs_closed : typeclass_instances.
Hint Extern 5 (abs ?x ∊ _) => eapply (abs_closed x) : typeclass_instances.

Local Ltac abs_case R x := destruct (nonneg_or_nonpos x);
  [ rewrite (R $ abs_nonneg x) | rewrite (R $ abs_nonpos x) ].

Lemma abs_closed_nonneg `{Ring (R:=R)} `{Le _} `{!TotalOrder R} `{!SemiRingOrder R}
  `{Abs _} `{!DecAbs R} : Closed (R ⇀ R⁺) |·|.
Proof. intros x ?. abs_case R x; apply _. Qed.
Hint Extern 10 (Closed (_ ⇀ _⁺) |·|) => eapply @abs_closed_nonneg : typeclass_instances.
Hint Extern 2 (abs _ ∊ _⁺) => eapply @abs_closed_nonneg : typeclass_instances.

Lemma abs_unique_respectful `{Ring (R:=R)} `{Le _} `{!TotalOrder R} `{!SemiRingOrder R}
 `{!DecAbs R (a:=a1)} `{!DecAbs R (a:=a2)} : (abs (Abs:=a1) : R ⇀ R⁺) = abs (Abs:=a2).
Proof. intros x y E. unfold_sigs. red_sig.
  abs_case R x; subsymmetry; rewrite (R $ E);
  [ apply abs_nonneg | apply abs_nonpos ]; now rewrite <-(R $ E).
Qed.

Lemma abs_morphism_nonneg `{Ring (R:=R)} `{Le _} `{!TotalOrder R} `{!SemiRingOrder R}
  `{Abs _} `{!DecAbs R} : Morphism (R ⇒ R⁺) |·|.
Proof abs_unique_respectful.
Hint Extern 2 (Morphism (_ ⇒ _⁺) abs) => eapply @abs_morphism_nonneg : typeclass_instances.

Lemma abs_morphism `{Ring (R:=R)} `{Le _} `{!TotalOrder R} `{!SemiRingOrder R}
  `{Abs _} `{!DecAbs R} : Morphism (R ⇒ R) |·|.
Proof. rewrite <- (_ : SubsetOf (R ⇒ R⁺) (R ⇒ R)). apply _. Qed.
Hint Extern 3 (Morphism _ abs) => eapply @abs_morphism : typeclass_instances.

Section contents.
Context `{Ring (R:=R)} `{Le _} `{!TotalOrder R} `{!SemiRingOrder R} `{Abs _} `{!DecAbs R}.

Lemma abs_nonneg_plus x `{x ∊ R⁺} y `{y ∊ R⁺} : |x+y| = |x|+|y|.
Proof. now rewrite ?(R $ abs_nonneg _). Qed.

Lemma abs_nonpos_plus x `{x ∊ R⁻} y `{y ∊ R⁻} : |x+y| = |x|+|y|.
Proof. rewrite ?(R $ abs_nonpos _). exact (negate_plus_distr _ _). Qed.

Lemma abs_0 : | 0 | = 0.
Proof abs_nonneg 0.

Lemma abs_negate x `{x ∊ R} : | -x | = |x|.
Proof. abs_case R x. rewrite <- (R $ negate_involutive x) at 2.
  exact (abs_nonpos _). exact (abs_nonneg _).
Qed.

Lemma abs_mult x `{x ∊ R} y `{y ∊ R} : |x*y| = |x|*|y|.
Proof. abs_case R x; abs_case R y; first [ rewrite (R $ abs_nonneg _) | rewrite (R $ abs_nonpos _) ].
+ subreflexivity.
+ exact (negate_mult_distr_r _ _).
+ exact (negate_mult_distr_l _ _).
+ now rewrite (R $ negate_mult_negate _ _).
Qed.


Lemma abs_le_iff x `{x ∊ R} y `{y ∊ R} : |x| ≤ y ↔ -y ≤ x ≤ y.
Proof. split.
+ intro E. assert (y ∊ R⁺). split. apply _. subtransitivity (|x|). now destruct (_ : |x| ∊ R⁺).
  generalize E; abs_case R x; intro E2; split.
  * apply (flip_nonneg_minus _ _). apply _.
  * trivial.
  * now rewrite <- (flip_le_negate _ _), (R $ negate_involutive _).
  * apply (flip_nonneg_minus _ _). apply _.
+ intro. abs_case R x. easy. now rewrite <- (flip_le_negate _ _), (R $ negate_involutive _).
Qed.

Lemma abs_between x `{x ∊ R} : - (|x|) ≤ x ≤ |x|.
Proof. now rewrite <- (abs_le_iff _ _). Qed.

Lemma abs_triangle x `{x ∊ R} y `{y ∊ R} : |x+y| ≤ |x|+|y|.
Proof. rewrite (abs_le_iff _ _), (R $ negate_plus_distr _ _).
 apply (plus_le_compat_2 _ _ _ _ _ _); exact (abs_between _).
Qed.

Lemma abs_0_iff x `{x ∊ R} : |x| = 0 ↔ x = 0.
Proof. split; intro E. 2: rewrite (R $ E); exact abs_0.
  pose proof abs_between x as E2. rewrite (R $ E), (R $ negate_0) in E2.
  now apply (subantisymmetry le _ _).
Qed.

Context `{UnEq _} `{Lt _} `{!FullPseudoSemiRingOrder R}.

Lemma abs_1 : | 1 | = 1.
Proof abs_nonneg 1.

End contents.

Definition default_abs {A} {Ale:Le A} `{Zero A} `{Negate A} {R} `{!StrongSubDecision R R (≤)}
  : Abs A := λ x, if (decide_sub_strong (≤) 0 x) then x else -x.

(* force instance resolution to pick the relation {Le A} before looking for the decision procedure *)
Hint Extern 20 (Abs ?A) =>
  let H := constr:(_ : PartialOrder (A:=A) _) in
  match type of H with PartialOrder (Ale:=?l) ?R =>
    eapply (default_abs (Ale:=l) (R:=R)) end : typeclass_instances.

Section default_abs.
  Context `{Ring A (R:=R)} `{Le A} `{!PartialOrder R} `{!StrongSubDecision R R (≤)}.

  Instance default_abs_spec : DecAbs R.
  Proof. split; unfold abs, default_abs; intros x ?;
    destruct (decide_sub_strong le 0 x) as [P|P]; pose proof (P _ _) as E; clear P;
    try apply _; try subreflexivity.
  + contradict E. firstorder.
  + assert (x=0) as E2 by (apply (subantisymmetry le _ _); firstorder).
    now rewrite (R $ E2), (R $ negate_0).
  Qed.
End default_abs.

Hint Extern 2 (@DecAbs _ _ _ _ _ default_abs _) => eapply @default_abs_spec : typeclass_instances.

Section order_preserving.
  Context `{Ring (R:=R1)} {le1:Le _} `{!TotalOrder R1} `{!SemiRingOrder R1} {a1:Abs _} `{!DecAbs R1}.
  Context `{Ring (R:=R2)} {le2:Le _} `{!TotalOrder R2} `{!SemiRingOrder R2} {a2:Abs _} `{!DecAbs R2}.
  Context (f: R1 ⇀ R2) `{!OrderPreserving R1 R2 f} `{!Ring_Morphism R1 R2 f}.

  Lemma preserves_abs x `{x ∊ R1} : f (|x|) = |f x|.
  Proof. abs_case R1 x; subsymmetry. apply (abs_nonneg _).
    rewrite (R2 $ preserves_negate _). apply (abs_nonpos _).
  Qed.
End order_preserving.

