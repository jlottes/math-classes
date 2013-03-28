Require Import
  abstract_algebra interfaces.orders interfaces.affine_extension theory.strong_setoids theory.rings.
Require Export
  orders.rings.

Local Notation F  := (aff_ext_full _).
Local Notation "R∞" := (aff_ext _).
Local Notation U := (ae_undef _).
Local Notation notR := (ae_inf_undef _).


Section closed.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_plus_closed_F : Closed (F ⇀ F ⇀ F) (+).   Proof binary_morphism_closed (+).
  Lemma ae_mult_closed_F : Closed (F ⇀ F ⇀ F) (.*.). Proof binary_morphism_closed (.*.).
  Lemma ae_negate_closed_F : Closed (F ⇀ F) (-). Proof morphism_closed (-).

  Lemma ae_zero_el_F : 0 ∊ F. Proof. apply (_ : SubsetOf R F). apply _. Qed.
  Lemma ae_one_el_F : 1 ∊ F. Proof. apply (_ : SubsetOf R F). apply _. Qed.

  Lemma ae_le_proper_flip : Proper ((F,=) ==> (F,=) ==> flip impl) le.
  Proof. intros ?? E1 ?? E2 E. unfold_sigs.
    exact (ae_le_proper _ _ (F $ subsymmetry _ _ E1) _ _ (F $ subsymmetry _ _ E2) E).
  Qed.
  Lemma ae_lt_proper_flip : Proper ((F,=) ==> (F,=) ==> flip impl) lt.
  Proof. intros ?? E1 ?? E2 E. unfold_sigs.
    exact (ae_lt_proper _ _ (F $ subsymmetry _ _ E1) _ _ (F $ subsymmetry _ _ E2) E).
  Qed.

  Lemma ae_neg_proper_F : Proper ((F,=) ==> (F,=)) (-). Proof morphism_proper _.
  Lemma ae_plus_proper_F : Proper ((F,=) ==> (F,=) ==> (F,=)) (+). Proof binary_morphism_proper _.
  Lemma ae_mult_proper_F : Proper ((F,=) ==> (F,=) ==> (F,=)) (.*.). Proof binary_morphism_proper _.

  Lemma ae_decompose_ext x `{el: x ∊ R∞} : x ∊ R ∨ (x ∊ F ∧ (x = ∞ ∨ x = -∞)).
  Proof. now rewrite ae_set_def in el. Qed.

End closed.

Hint Extern 4 (_ + _ ∊ F) => eapply @ae_plus_closed_F : typeclass_instances.
Hint Extern 4 (_ * _ ∊ F) => eapply @ae_mult_closed_F : typeclass_instances.
Hint Extern 4 (- _ ∊ F) => eapply @ae_negate_closed_F : typeclass_instances.
Hint Extern 2 (0 ∊ F) => eapply @ae_zero_el_F : typeclass_instances.
Hint Extern 2 (1 ∊ F) => eapply @ae_one_el_F : typeclass_instances.

Hint Extern 2 (∞ ∊ notR) => eexact (conj ae_inf_el_F ae_inf_not_el) : typeclass_instances.

Hint Extern 2 (Proper ((F,=) ==> _ ==> impl) (≤)) => eapply @ae_le_proper : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> impl) (≤)) => eapply @ae_le_proper : typeclass_instances.
Hint Extern 2 (Proper ((F,=) ==> _ ==> impl) (<)) => eapply @ae_lt_proper : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> impl) (<)) => eapply @ae_lt_proper : typeclass_instances.
Hint Extern 2 (Proper ((F,=) ==> _ ==> flip impl) (≤)) => eapply @ae_le_proper_flip : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> flip impl) (≤)) => eapply @ae_le_proper_flip : typeclass_instances.
Hint Extern 2 (Proper ((F,=) ==> _ ==> flip impl) (<)) => eapply @ae_lt_proper_flip : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> flip impl) (<)) => eapply @ae_lt_proper_flip : typeclass_instances.

Hint Extern 2 (Proper ((F,=) ==> _) (-)) => eapply @ae_neg_proper_F : typeclass_instances.
Hint Extern 2 (Proper ((F,=) ==> _ ==> _) (+)) => eapply @ae_plus_proper_F : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> _) (+)) => eapply @ae_plus_proper_F : typeclass_instances.
Hint Extern 2 (Proper ((F,=) ==> _ ==> _) (.*.)) => eapply @ae_mult_proper_F : typeclass_instances.
Hint Extern 2 (Proper (_ ==> (F,=) ==> _) (.*.)) => eapply @ae_mult_proper_F : typeclass_instances.

Local Ltac cases_ext x E := destruct (ae_decompose_ext x) as [?|[? [E|E]]].
Local Ltac decompose_ext x := let E := fresh "E" in cases_ext x E; [| rewrite (F $ E)..].

Section subsetoid.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Instance: SubsetOf R∞ F.
  Proof. intros ? el. rewrite ae_set_def in el.
    destruct el as [?|[??]]; trivial. now apply (_ : SubsetOf R F).
  Qed.

  Lemma ae_inf_el_ext : ∞ ∊ R∞.
  Proof. rewrite ae_set_def. right. split. apply _. now left. Qed.

  Instance ae_im_subsetoid : R ⊆ R∞.
  Proof. split. apply _.
  + intros ?? [[el1 el2] E].
    apply (_ : SubsetOf R∞ F) in el1.
    apply (_ : SubsetOf R∞ F) in el2.
    intro. now rewrite <-(F $ E).
  + rewrite ae_set_def. intros ??. now left.
  Qed.

  Instance ae_ext_subsetoid : R∞ ⊆ F.
  Proof. split; try apply _.
    intros ?? [[el1 el2] E]. rewrite ae_set_def. intros [?|[? E2]];
    [left|right]; rewrite <-(F $ E); tauto.
  Qed.

  Lemma ae_notR_subsetoid : notR ⊆ F.
  Proof. split. apply _.
    intros ?? [[??] E] [? el]. split. apply _. contradict el. now rewrite (F $ E).
    now intros ?[??].
  Qed.

  Lemma ae_undef_notR : SubsetOf U notR.
  Proof. intros ? [? el]. split. apply _. contradict el.
    rewrite ae_set_def. now left.
  Qed.

  Lemma ae_undef_subsetoid : U ⊆ F.
  Proof. split. apply _.
    intros ?? [[??] E] [? el]. split. apply _. contradict el. now rewrite (F $ E).
    now intros ?[??].
  Qed.

  Instance: 0 ∊ R∞. Proof. apply (_:SubsetOf R (aff_ext R)). apply _. Qed.

  Instance ae_nonneg_subsetoid : R∞⁺ ⊆ F.   Proof. transitivity R∞; apply _. Qed.
  Instance ae_nonpos_subsetoid : R∞⁻ ⊆ F.   Proof. transitivity R∞; apply _. Qed.
  Instance ae_pos_subsetoid    : R∞₊ ⊆ F.   Proof. transitivity R∞; apply _. Qed.
  Instance ae_neg_subsetoid    : R∞₋ ⊆ F.   Proof. transitivity R∞; apply _. Qed.

  Local Ltac solve_cone := split; [ apply _ 
  | intros ?? [[[??][??]]E]; intros [??]; split; [| apply _ ]; now rewrite <- (R∞ $ E)
  | intros ? [??]; split; [apply (_:SubsetOf R (aff_ext R))|]; apply _
  ].

  Instance ae_nonneg_subsetoid_ext : R⁺ ⊆ R∞⁺.  Proof. solve_cone. Qed.
  Instance ae_nonpos_subsetoid_ext : R⁻ ⊆ R∞⁻.  Proof. solve_cone. Qed.
  Instance ae_pos_subsetoid_ext    : R₊ ⊆ R∞₊.  Proof. solve_cone. Qed.
  Instance ae_neg_subsetoid_ext    : R₋ ⊆ R∞₋.  Proof. solve_cone. Qed.

  Instance ae_im_nonneg_subsetoid : R⁺ ⊆ F.   Proof. transitivity R∞⁺; apply _. Qed.
  Instance ae_im_nonpos_subsetoid : R⁻ ⊆ F.   Proof. transitivity R∞⁻; apply _. Qed.
  Instance ae_im_pos_subsetoid    : R₊ ⊆ F.   Proof. transitivity R∞₊; apply _. Qed.
  Instance ae_im_neg_subsetoid    : R₋ ⊆ F.   Proof. transitivity R∞₋; apply _. Qed.

  Lemma ae_negate_closed_ext : Closed (R∞ ⇀ R∞) (-).
  Proof. intros ?. rewrite ae_set_def. intros [?|[? E2]]; [left|right].
    apply _. split. apply _.
    destruct E2 as [E|E]. right. now rewrite (F $ E).
    left. rewrite (F $ E). now rewrite (F $ ae_neg_inf_invl).
  Qed.

End subsetoid.

Hint Extern 2 (∞ ∊ R∞) => eapply @ae_inf_el_ext : typeclass_instances.
Hint Extern 2 (?R ⊆ aff_ext ?R) => eapply @ae_im_subsetoid : typeclass_instances.
Hint Extern 2 (R∞ ⊆ F) => eapply @ae_ext_subsetoid : typeclass_instances.
Hint Extern 2 (U ⊆ F) => eapply @ae_undef_subsetoid : typeclass_instances.
Hint Extern 2 (notR ⊆ F) => eapply @ae_notR_subsetoid : typeclass_instances.
Hint Extern 2 (SubsetOf U notR) => eapply @ae_undef_notR : typeclass_instances.
Hint Extern 2 (R∞⁺ ⊆ F) => eapply @ae_nonneg_subsetoid : typeclass_instances.
Hint Extern 2 (R∞⁻ ⊆ F) => eapply @ae_nonpos_subsetoid : typeclass_instances.
Hint Extern 2 (R∞₊ ⊆ F) => eapply @ae_pos_subsetoid : typeclass_instances.
Hint Extern 2 (R∞₋ ⊆ F) => eapply @ae_neg_subsetoid : typeclass_instances.
Hint Extern 2 (?R⁺ ⊆ (aff_ext ?R)⁺) => eapply @ae_nonneg_subsetoid_ext : typeclass_instances.
Hint Extern 2 (?R⁻ ⊆ (aff_ext ?R)⁻) => eapply @ae_nonpos_subsetoid_ext : typeclass_instances.
Hint Extern 2 (?R₊ ⊆ (aff_ext ?R)₊) => eapply @ae_pos_subsetoid_ext : typeclass_instances.
Hint Extern 2 (?R₋ ⊆ (aff_ext ?R)₋) => eapply @ae_neg_subsetoid_ext : typeclass_instances.
Hint Extern 2 (?R⁺ ⊆ (aff_ext_full ?R)) => eapply @ae_im_nonneg_subsetoid : typeclass_instances.
Hint Extern 2 (?R⁻ ⊆ (aff_ext_full ?R)) => eapply @ae_im_nonpos_subsetoid : typeclass_instances.
Hint Extern 2 (?R₊ ⊆ (aff_ext_full ?R)) => eapply @ae_im_pos_subsetoid : typeclass_instances.
Hint Extern 2 (?R₋ ⊆ (aff_ext_full ?R)) => eapply @ae_im_neg_subsetoid : typeclass_instances.
Hint Extern 4 (- _ ∊ R∞) => eapply @ae_negate_closed_ext : typeclass_instances.
Hint Extern 2 (∞ ∊ R∞₊) => eexact (conj ae_inf_el_ext (ae_inf_sub 0)) : typeclass_instances.

Hint Extern 10 (_ ∊ (aff_ext ?R)⁺) => eapply (_:SubsetOf R⁺ (aff_ext R)⁺) : typeclass_instances.
Hint Extern 10 (_ ∊ (aff_ext ?R)⁻) => eapply (_:SubsetOf R⁻ (aff_ext R)⁻) : typeclass_instances.
Hint Extern 10 (_ ∊ (aff_ext ?R)₊) => eapply (_:SubsetOf R₊ (aff_ext R)₊) : typeclass_instances.
Hint Extern 10 (_ ∊ (aff_ext ?R)₋) => eapply (_:SubsetOf R₋ (aff_ext R)₋) : typeclass_instances.
Hint Extern 10 (_ ∊ aff_ext ?R) => eapply (_:SubsetOf R (aff_ext R)) : typeclass_instances.
Hint Extern 10 (_ ∊ F) => eapply (_:SubsetOf R∞ F) : typeclass_instances.

Local Ltac undef_eq  := apply (ae_undef_eq); apply _.
Local Ltac destr_F x := destruct (ae_decompose_full x); [| undef_eq ].

Section negate.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_minf_lt_inf : -∞ < ∞.
  Proof.
    apply (subtransitivity (S:=R∞) _ 0 _).
    exact (ae_minf_slb 0).
    exact (ae_inf_sub 0).
  Qed.

  Lemma ae_minf_inf_uneq : -∞ ≠ ∞.
  Proof. apply (pseudo_order_lt_apart (S:=R∞) _ _). exact ae_minf_lt_inf. Qed.

  Lemma ae_inf_minf_uneq : ∞ ≠ -∞.
  Proof. subsymmetry. exact ae_minf_inf_uneq. Qed.

  Lemma ae_inf_uneq_r x `{x ∊ R} : x ≠ ∞.
  Proof. apply (pseudo_order_lt_apart (S:=R∞) _ _). exact (ae_inf_sub _). Qed.

  Lemma ae_inf_uneq_l x `{x ∊ R} : ∞ ≠ x.
  Proof. subsymmetry. exact (ae_inf_uneq_r _). Qed.

  Lemma ae_minf_uneq_l x `{x ∊ R} : -∞ ≠ x.
  Proof. apply (pseudo_order_lt_apart (S:=R∞) _ _). exact (ae_minf_slb _). Qed.

  Lemma ae_minf_uneq_r x `{x ∊ R} :  x ≠ -∞.
  Proof. subsymmetry. exact (ae_minf_uneq_l _). Qed.

  Lemma ae_cases_ext (P: A → Prop) :
    Proper ((F,=) ==> impl) P
  → (∀ `{x ∊ R}, P x) → P ∞ → P (-∞) → (∀ `{x ∊ R∞}, P x).
  Proof. intros p PR Pinf Pminf x ?.
    decompose_ext x; [exact (PR x _) | easy..].
  Qed.

  Lemma ae_cases_ext2 (P: A → A → Prop) :
    Proper ((F,=) ==> (F,=) ==> impl) P
  → (∀ `{x ∊ R} `{y ∊ R}, P x y) → (∀ `{x ∊ R}, P x ∞) → (∀ `{x ∊ R}, P x (-∞))
  → (∀ `{y ∊ R}, P ∞ y) → P ∞ ∞ → P ∞ (-∞)
  → (∀ `{y ∊ R}, P (-∞) y) → P (-∞) ∞ → P (-∞) (-∞)
  → (∀ `{x ∊ R∞} `{y ∊ R∞}, P x y).
  Proof. intros.
    apply ae_cases_ext; [solve_proper |
      pattern x; apply ae_cases_ext..
    |trivial ]; try auto;
    intros ?? E ?; intros; rewrite <-E; auto.
  Qed.

  Lemma ae_cases_ext3 (P: A → A → A → Prop) :
    Proper ((F,=) ==> (F,=) ==> (F,=) ==> impl) P
  → (∀ `{x ∊ R} `{y ∊ R} `{z ∊ R}, P x y z)
  → (∀ `{x ∊ R} `{y ∊ R}, P x y ∞)
  → (∀ `{x ∊ R} `{y ∊ R}, P x y (-∞))
  → (∀ `{x ∊ R} `{z ∊ R}, P x ∞ z)
  → (∀ `{x ∊ R}, P x ∞ ∞)
  → (∀ `{x ∊ R}, P x ∞ (-∞))
  → (∀ `{x ∊ R} `{z ∊ R}, P x (-∞) z)
  → (∀ `{x ∊ R}, P x (-∞) ∞)
  → (∀ `{x ∊ R}, P x (-∞) (-∞))
  → (∀ `{y ∊ R} `{z ∊ R}, P ∞ y z)
  → (∀ `{y ∊ R}, P ∞ y ∞)
  → (∀ `{y ∊ R}, P ∞ y (-∞))
  → (∀ `{z ∊ R}, P ∞ ∞ z)
  → P ∞ ∞ ∞
  → P ∞ ∞ (-∞)
  → (∀ `{z ∊ R}, P ∞ (-∞) z)
  → P ∞ (-∞) ∞
  → P ∞ (-∞) (-∞)
  → (∀ `{y ∊ R} `{z ∊ R}, P (-∞) y z)
  → (∀ `{y ∊ R}, P (-∞) y ∞)
  → (∀ `{y ∊ R}, P (-∞) y (-∞))
  → (∀ `{z ∊ R}, P (-∞) ∞ z)
  → P (-∞) ∞ ∞
  → P (-∞) ∞ (-∞)
  → (∀ `{z ∊ R}, P (-∞) (-∞) z)
  → P (-∞) (-∞) ∞
  → P (-∞) (-∞) (-∞)
  → (∀ `{x ∊ R∞} `{y ∊ R∞} `{z ∊ R∞}, P x y z).
  Proof. intros p. intros. pattern x.
    apply ae_cases_ext; [solve_proper |
      intros; apply ae_cases_ext2; try auto..
    |trivial]; apply p; now red_sig.
  Qed.

  Lemma ae_inf_ub x `{el : x ∊ R∞} : x ≤ ∞.
  Proof. decompose_ext x.
    apply (lt_le (P:=R∞) _ _). exact (ae_inf_sub _).
    apply (subreflexivity (S:=R∞)). apply _.
    apply (lt_le (P:=R∞) _ _). exact (ae_minf_lt_inf).
  Qed.

  Lemma ae_minf_lb x `{el : x ∊ R∞} : -∞ ≤ x.
  Proof. decompose_ext x.
    apply (lt_le (P:=R∞) _ _). exact (ae_minf_slb _).
    apply (lt_le (P:=R∞) _ _). exact (ae_minf_lt_inf).
    apply (subreflexivity (S:=R∞)). apply _.
  Qed.

  Lemma ae_sub_inf x `{el: x ∊ R∞} : (∀ `{y ∊ R}, y < x) → x = ∞.
  Proof. intro P. decompose_ext x.
  + destruct (subirreflexivity (<) x). exact (P x _).
  + easy.
  + destruct ( lt_flip (S:=R∞) (-∞) 0 ). exact (ae_minf_slb 0).
    rewrite <- (R∞ $ E). exact (P 0 _).
  Qed.

  Lemma ae_slb_minf x `{el: x ∊ R∞} : (∀ `{y ∊ R}, x < y) → x = -∞.
  Proof. intro P. decompose_ext x.
  + destruct (subirreflexivity (<) x). exact (P x _).
  + destruct ( lt_flip (S:=R∞) 0 ∞). exact (ae_inf_sub 0).
    rewrite <- (R∞ $ E). exact (P 0 _).
  + easy.
  Qed.

  Lemma ae_inf_le x `{el : x ∊ R∞} : ∞ ≤ x → x = ∞.
  Proof. intro P. apply (ae_sub_inf x). intros y ?.
    apply (lt_le_trans (P:=R∞) _ infty _); trivial.
    exact (ae_inf_sub _).
  Qed.

  Lemma ae_le_minf x `{el : x ∊ R∞} : x ≤ -∞ → x = -∞.
  Proof. intro P. apply (ae_slb_minf x). intros y ?.
    apply (le_lt_trans (P:=R∞) _ (-infty) _); trivial.
    exact (ae_minf_slb _).
  Qed.

  Instance ae_stduneq_ext `{!StandardUnEq R} : StandardUnEq R∞.
  Proof. red. apply ae_cases_ext2; [| intros; split; [rewrite <-(tight_apart _ _);tauto|intro E]..].
  + intros ?? E1 ?? E2 ?. unfold_sigs. now rewrite <-(F $ E1), <-(F $ E2).
  + now rewrite (standard_uneq _ _).
  + exact (ae_inf_uneq_r _).
  + exact (ae_minf_uneq_r _).
  + exact (ae_inf_uneq_l _).
  + now contradict E.
  + exact ae_inf_minf_uneq.
  + exact (ae_minf_uneq_l _).
  + exact ae_minf_inf_uneq.
  + now contradict E.
  Qed.

  Instance ae_stduneq `{!StandardUnEq R} : StandardUnEq F.
  Proof. intros x ? y ?.
    destruct (ae_decompose_full x) as [Ex|Ex];
    destruct (ae_decompose_full y) as [Ey|Ey].
    + exact (standard_uneq (S:=R∞) _ _).
    + split. intros ? E. rewrite (F $ E) in Ex. now destruct Ey.
             intro. subsymmetry. exact (ae_undef_uneq _ _).
    + split. intros ? E. rewrite (F $ E) in Ex. now destruct Ex.
             intro. exact (ae_undef_uneq _ _).
    + split. intro E. contradict E. now apply (equiv_nue (S:=F) _ _).
             intro E. contradict E. undef_eq.
  Qed.

  Instance ae_sub_dec_ext (rel:relation _) `{!SubDecision F F rel} : SubDecision R∞ R∞ rel.
  Proof. intros x ? y ?. exact (decide_sub rel x y). Qed.

  Program Instance ae_str_sub_dec_ext `{!StrongSubDecision F F rel} : StrongSubDecision R∞ R∞ rel
    := λ x y, if (decide_sub_strong rel x y) then in_left else in_right.
  Next Obligation. match goal with H : _ -> _ -> rel _ _ |- _ => exact (H _ _) end. Qed.
  Next Obligation. match goal with H : _ -> _ -> ¬ rel _ _ |- _ => exact (H _ _) end. Qed.

  Lemma ae_negate_invl_ext : Involutive (-) R∞.
  Proof. intros x ?. decompose_ext x. exact (involutive _).
    exact ae_neg_inf_invl.
    now rewrite (F $ ae_neg_inf_invl).
  Qed.

  Instance ae_negate_involutive : Involutive (-) F.
  Proof. intros x ?. destr_F x. exact (ae_negate_invl_ext _ _). Qed.

  Lemma ae_negate_closed_notR : Closed (notR ⇀ notR) (-).
  Proof. intros x [? P]. split. apply _. contradict P.
    rewrite <- (F $ ae_negate_involutive x _). apply _.
  Qed.

  Lemma ae_decompose_nonneg x `{el: x ∊ R∞⁺} : x = ∞ ∨ x ∊ R⁺ .
  Proof. destruct el. cases_ext x E. right. now split. now left.
    destruct (le_not_lt_flip (P:=R∞) (-infty) 0). now rewrite <-(F $ E).
    exact (ae_minf_slb 0).
  Qed.

  Lemma ae_decompose_nonpos x `{el: x ∊ R∞⁻} : x = -∞ ∨ x ∊ R⁻ .
  Proof. destruct el. cases_ext x E. right. now split.
    destruct (le_not_lt_flip (P:=R∞) 0 infty). now rewrite <-(F $ E).
    exact (ae_inf_sub 0). now left.
  Qed.

  Lemma ae_decompose_pos x `{el: x ∊ R∞₊} : x = ∞ ∨ x ∊ R₊ .
  Proof. destruct el. cases_ext x E. right. now split. now left.
    destruct (lt_flip (S:=R∞) (-infty) 0). exact (ae_minf_slb 0).
    now rewrite <-(F $ E).
  Qed.

  Lemma ae_decompose_neg x `{el: x ∊ R∞₋} : x = -∞ ∨ x ∊ R₋ .
  Proof. destruct el. cases_ext x E. right. now split.
    destruct (lt_flip (S:=R∞) 0 infty). exact (ae_inf_sub 0).
    now rewrite <-(F $ E). now left.
  Qed.

End negate.

Hint Extern 2 (StandardUnEq R∞) => eapply ae_stduneq_ext : typeclass_instances.
Hint Extern 2 (StandardUnEq F) => eapply ae_stduneq : typeclass_instances.
Hint Extern 2 (SubDecision R∞ R∞ _) => eapply @ae_sub_dec_ext : typeclass_instances.
Hint Extern 2 (StrongSubDecision R∞ R∞ _) => eapply @ae_str_sub_dec_ext : typeclass_instances.
Hint Extern 2 (∞ ∊ R∞⁺) => eexact (conj ae_inf_el_ext (ae_inf_ub 0)) : typeclass_instances.

Local Ltac cases_nonneg x E := destruct (ae_decompose_nonneg x) as [E|?].
Local Ltac decompose_nonneg x := let E := fresh "E" in cases_nonneg x E; [rewrite (F $ E) |].
Local Ltac cases_nonpos x E := destruct (ae_decompose_nonpos x) as [E|?].
Local Ltac decompose_nonpos x := let E := fresh "E" in cases_nonpos x E; [rewrite (F $ E) |].
Local Ltac cases_neg x E := destruct (ae_decompose_neg x) as [E|?].
Local Ltac decompose_neg x := let E := fresh "E" in cases_neg x E; [rewrite (F $ E) |].
Local Ltac cases_pos x E := destruct (ae_decompose_pos x) as [E|?].
Local Ltac decompose_pos x := let E := fresh "E" in cases_pos x E; [rewrite (F $ E) |].

Section negate2.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_nonneg_negate : Closed (R∞⁺ ⇀ R∞⁻) (-).
  Proof. intros x ?. decompose_nonneg x.
    split. apply _. exact (ae_minf_lb 0).
    split. apply _. now destruct (nonneg_negate x).
  Qed.

  Lemma ae_nonpos_negate : Closed (R∞⁻ ⇀ R∞⁺) (-).
  Proof. intros x ?. decompose_nonpos x.
    rewrite (F $  ae_neg_inf_invl ). apply _.
    split. apply _. now destruct (nonpos_negate x).
  Qed.

  Lemma ae_pos_negate : Closed (R∞₊ ⇀ R∞₋) (-).
  Proof. intros x ?. decompose_pos x.
    split. apply _. exact (ae_minf_slb 0).
    split. apply _. now destruct (pos_negate x).
  Qed.

  Lemma ae_neg_negate : Closed (R∞₋ ⇀ R∞₊) (-).
  Proof. intros x ?. decompose_neg x.
    rewrite (F $  ae_neg_inf_invl ). apply _.
    split. apply _. now destruct (neg_negate x).
  Qed.

  Lemma ae_decompose_notR x `{el: x ∊ notR} : x ∊ U ∨ x = ∞ ∨ x = -∞.
  Proof. destruct el. destruct (ae_decompose_full x) as [?|[??]].
    right. cases_ext x E. contradiction. now left. now right.
    left. now split.
  Qed.

  Lemma ae_decompose_nonzero x `{x ∊ R∞ ₀} : x ∊ R∞₊ ∨ x ∊ R∞₋ .
  Proof. destruct (_ : x ∊ R∞ ₀).
    assert (0 ≠ x) as Ex by subsymmetry.
    rewrite (apart_iff_total_lt (S:=R∞) 0 x) in Ex.
    destruct Ex; [left | right]; now split.
  Qed.

End negate2.

Hint Extern 4 (- _ ∊ notR) => eapply @ae_negate_closed_notR : typeclass_instances.
Hint Extern 4 (- _ ∊ R∞⁻) => eapply @ae_nonneg_negate : typeclass_instances.
Hint Extern 4 (- _ ∊ R∞⁺) => eapply @ae_nonpos_negate : typeclass_instances.
Hint Extern 4 (- _ ∊ R∞₋) => eapply @ae_pos_negate : typeclass_instances.
Hint Extern 4 (- _ ∊ R∞₊) => eapply @ae_neg_negate : typeclass_instances.

Ltac cases_notR x E := destruct (ae_decompose_notR x) as [?|[E|E]].
Ltac destr_notR x := let E := fresh "E" in cases_notR x E; [| rewrite (F $ E)..].

Section plus.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_inf_plus_inf   :  ∞ + ∞ =  ∞.  Proof ae_plus_inf_l    ∞  ae_minf_lt_inf.
  Lemma ae_minf_minus_inf : -∞ - ∞ = -∞.  Proof ae_minus_inf_l (-∞) ae_minf_lt_inf.

  Lemma ae_plus_inf_comm x `{x ∊ F} : x + ∞ = ∞ + x.
  Proof. destr_F x. decompose_ext x.
    subtransitivity infty;[|subsymmetry].
      exact (ae_plus_inf_r _ (ae_minf_slb _)).
      exact (ae_plus_inf_l _ (ae_minf_slb _)).
    subreflexivity. undef_eq.
  Qed.

  Lemma ae_plus_minf_comm x `{x ∊ F} : x - ∞ = -∞ + x.
  Proof. destr_F x. decompose_ext x.
    subtransitivity (-infty);[|subsymmetry].
      exact (ae_minus_inf_r _ (ae_inf_sub _)).
      exact (ae_minus_inf_l _ (ae_inf_sub _)).
    undef_eq. subreflexivity.
  Qed.

  Instance ae_plus_comm : Commutative (+) F.
  Proof. intros x ? y ?. destr_F x. destr_F y.
    decompose_ext x.
    + decompose_ext y.
      * exact (commutativity (+) _ _).
      * exact (ae_plus_inf_comm _).
      * exact (ae_plus_minf_comm _).
    + subsymmetry. exact (ae_plus_inf_comm _).
    + subsymmetry. exact (ae_plus_minf_comm _).
  Qed.

  Instance ae_plus_ass : Associative (+) F.
  Proof. intros x ? y ? z ?. destr_F x. destr_F y. destr_F z.
    decompose_ext x; decompose_ext y; decompose_ext z;
      repeat match goal with
      | |- context [ ∞  + ∞ ] => rewrite (F $ ae_inf_plus_inf)
      | |- context [ -∞ - ∞ ] => rewrite (F $ ae_minf_minus_inf)
      | |- context [ ?x + ∞ ] => rewrite (F $ ae_plus_inf_r x (ae_minf_slb _))
      | |- context [ ∞ + ?x ] => rewrite (F $ ae_plus_inf_l x (ae_minf_slb _))
      | |- context [ ?x - ∞ ] => rewrite (F $ ae_minus_inf_r x (ae_inf_sub x))
      | |- context [ -∞ + ?x] => rewrite (F $ ae_minus_inf_l x (ae_inf_sub x))
      end; try undef_eq; try subreflexivity.
    exact (associativity (+) _ _ _).
  Qed.

  Lemma ae_nonneg_plus_inf_r x `{x ∊ R∞⁺} : x + ∞ = ∞.
  Proof. decompose_nonneg x.
    exact ae_inf_plus_inf. exact (ae_plus_inf_r x (ae_minf_slb _)).
  Qed.

  Lemma ae_nonneg_plus_inf_l x `{x ∊ R∞⁺} : ∞ + x = ∞.
  Proof. decompose_nonneg x.
    exact ae_inf_plus_inf. exact (ae_plus_inf_l x (ae_minf_slb _)).
  Qed.

  Lemma ae_nonpos_minus_inf_r x `{x ∊ R∞⁻} : x - ∞ = -∞.
  Proof. decompose_nonpos x.
    exact ae_minf_minus_inf. exact (ae_minus_inf_r x (ae_inf_sub _)).
  Qed.

  Lemma ae_nonpos_minus_inf_l x `{x ∊ R∞⁻} : -∞ + x = -∞.
  Proof. decompose_nonpos x.
    exact ae_minf_minus_inf. exact (ae_minus_inf_l x (ae_inf_sub _)).
  Qed.

  Lemma ae_plus_0_l x `{x ∊ F} : 0 + x = x.
  Proof. destr_F x. decompose_ext x.
    exact (plus_0_l _).
    exact (ae_nonneg_plus_inf_r 0).
    exact (ae_nonpos_minus_inf_r 0).
  Qed.

  Lemma ae_plus_0_r x `{x ∊ F} : x + 0 = x.
  Proof. destr_F x. decompose_ext x.
    exact (plus_0_r _).
    exact (ae_nonneg_plus_inf_l 0).
    exact (ae_nonpos_minus_inf_l 0).
  Qed.

  Instance ae_nonneg_plus_compat : Closed (R∞⁺ ⇀ R∞⁺ ⇀ R∞⁺) (+).
  Proof. intros x ? y ?.
    decompose_nonneg x. rewrite (F $ ae_nonneg_plus_inf_l _). apply _.
    decompose_nonneg y. rewrite (F $ ae_nonneg_plus_inf_r _). apply _.
    split. apply _. now destruct (_ : x + y ∊ R⁺).
  Qed.

  Instance ae_nonpos_plus_compat : Closed (R∞⁻ ⇀ R∞⁻ ⇀ R∞⁻) (+).
  Proof. intros x ? y ?.
    decompose_nonpos x. rewrite (F $ ae_nonpos_minus_inf_l _). apply _.
    decompose_nonpos y. rewrite (F $ ae_nonpos_minus_inf_r _). apply _.
    split. apply _. now destruct (_ : x + y ∊ R⁻).
  Qed.

  Instance ae_pos_plus_compat : Closed (R∞₊ ⇀ R∞₊ ⇀ R∞₊) (+).
  Proof. intros x ? y ?.
    decompose_pos x. rewrite (F $ ae_nonneg_plus_inf_l _). apply _.
    decompose_pos y. rewrite (F $ ae_nonneg_plus_inf_r _). apply _.
    split. apply _. now destruct (_ : x + y ∊ R₊).
  Qed.

  Instance ae_neg_plus_compat : Closed (R∞₋ ⇀ R∞₋ ⇀ R∞₋) (+).
  Proof. intros x ? y ?.
    decompose_neg x. rewrite (F $ ae_nonpos_minus_inf_l _). apply _.
    decompose_neg y. rewrite (F $ ae_nonpos_minus_inf_r _). apply _.
    split. apply _. now destruct (_ : x + y ∊ R₋).
  Qed.

  Instance ae_nonneg_pos_plus : Closed (R∞⁺ ⇀ R∞₊ ⇀ R∞₊) (+).
  Proof. intros x ? y ?.
    decompose_nonneg x. rewrite (F $ ae_nonneg_plus_inf_l _). apply _.
    decompose_pos y.    rewrite (F $ ae_nonneg_plus_inf_r _). apply _.
    split. apply _. apply (nonneg_plus_lt_compat_l _ _ _). now destruct (_ : y ∊ R₊).
  Qed.

  Instance ae_pos_nonneg_plus : Closed (R∞₊ ⇀ R∞⁺ ⇀ R∞₊) (+).
  Proof. intros x ? y ?. rewrite (F $ commutativity (+) _ _). now apply ae_nonneg_pos_plus. Qed.

End plus.

Hint Extern 2 (Commutative (+) F) => eapply @ae_plus_comm : typeclass_instances.
Hint Extern 2 (Associative (+) F) => eapply @ae_plus_ass : typeclass_instances.

Hint Extern 3 (_ + _ ∊ R∞⁺) => eapply @ae_nonneg_plus_compat : typeclass_instances. 
Hint Extern 3 (_ + _ ∊ R∞⁻) => eapply @ae_nonpos_plus_compat : typeclass_instances. 
Hint Extern 3 (_ + _ ∊ R∞₊) => eapply @ae_nonneg_pos_plus : typeclass_instances. 
Hint Extern 3 (_ + _ ∊ R∞₊) => eapply @ae_pos_nonneg_plus : typeclass_instances. 
Hint Extern 3 (_ + _ ∊ R∞₋) => eapply @ae_neg_plus_compat : typeclass_instances. 

Section mult.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_decompose_R_notR x `{x ∊ F} : x ∊ R ∨ x ∊ notR.
  Proof. destruct (ae_decompose_full x). cases_ext x E. now left.
    right. rewrite (F $ E). apply _.
    right. rewrite (F $ E). apply _.
    right. now apply ae_undef_notR.
  Qed.

  Lemma ae_mult_inf_inf : ∞ * ∞ = ∞. Proof ae_pos_mult_inf_r _.
  Lemma ae_mult_inf_minf : ∞ * -∞ = -∞. Proof ae_pos_mult_minf_r _.
  Lemma ae_mult_minf_inf : -∞ * ∞ = -∞. Proof ae_neg_mult_inf_r _.
  Lemma ae_mult_minf_minf : -∞ * -∞ = ∞. Proof ae_neg_mult_minf_r _.

  Lemma ae_minf_not_el : ¬ -∞ ∊ R.
  Proof. intro. destruct ae_inf_not_el. rewrite <-(F $ ae_negate_involutive infty _). apply _. Qed.
 
  Instance ae_mult_closed_notR : Closed (notR ⇀ notR ⇀ notR) (.*.).
  Proof. intros x ? y ?.  assert (x ∊ F) by firstorder. assert (y ∊ F) by firstorder.
    split. apply _.
    destr_notR x. destruct (_ : x*y ∊ U) as [? el]. contradict el. apply _.
    destr_notR y. destruct (_ : infty*y ∊ U) as [? el]. contradict el. apply _.
      rewrite (F $ ae_mult_inf_inf). exact ae_inf_not_el.
      rewrite (F $ ae_mult_inf_minf). exact ae_minf_not_el.
    destr_notR y. destruct (_ : -infty*y ∊ U) as [? el]. contradict el. apply _.
      rewrite (F $ ae_mult_minf_inf). exact ae_minf_not_el.
      rewrite (F $ ae_mult_minf_minf). exact ae_inf_not_el.
  Qed.

  Instance ae_mult_0_notR_l : Closed (notR ⇀ U) (0 *.).
  Proof. intros x ?. assert (x ∊ F) by firstorder. destruct (ae_decompose_notR x) as [?|[E|E]];
    [| rewrite (F $ E)..]; apply _.
  Qed.

  Instance ae_mult_0_notR_r : Closed (notR ⇀ U) (.* 0).
  Proof. intros x ?. assert (x ∊ F) by firstorder. destruct (ae_decompose_notR x) as [?|[E|E]];
    [| rewrite (F $ E)..]; apply _.
  Qed.

  Lemma ae_pos_mult : Closed (R∞₊ ⇀ R∞₊ ⇀ R∞₊) (.*.).
  Proof. intros x ? y ?.
    destruct (ae_decompose_pos x) as [Ex|?].
    rewrite (F $ Ex), (F $ ae_pos_mult_inf_l _); apply _.
    destruct (ae_decompose_pos y) as [Ey|?].
    rewrite (F $ Ey), (F $ ae_pos_mult_inf_r _); apply _.
    split. apply _. now destruct (_ : x*y ∊ R₊).
  Qed.

  Lemma ae_neg_mult : Closed (R∞₋ ⇀ R∞₋ ⇀ R∞₊) (.*.).
  Proof. intros x ? y ?.
    destruct (ae_decompose_neg x) as [Ex|?].
    rewrite (F $ Ex), (F $ ae_neg_mult_minf_l _); apply _.
    destruct (ae_decompose_neg y) as [Ey|?].
    rewrite (F $ Ey), (F $ ae_neg_mult_minf_r _); apply _.
    split. apply _. now destruct (_ : x*y ∊ R₊).
  Qed.

  Lemma ae_neg_pos_mult : Closed (R∞₋ ⇀ R∞₊ ⇀ R∞₋) (.*.).
  Proof. intros x ? y ?.
    destruct (ae_decompose_neg x) as [Ex|?].
    rewrite (F $ Ex), (F $ ae_pos_mult_minf_l _); apply _.
    destruct (ae_decompose_pos y) as [Ey|?].
    rewrite (F $ Ey), (F $ ae_neg_mult_inf_r _); apply _.
    split. apply _. now destruct (_ : x*y ∊ R₋).
  Qed.

  Lemma ae_pos_neg_mult : Closed (R∞₊ ⇀ R∞₋ ⇀ R∞₋) (.*.).
  Proof. intros x ? y ?.
    destruct (ae_decompose_pos x) as [Ex|?].
    rewrite (F $ Ex), (F $ ae_neg_mult_inf_l _); apply _.
    destruct (ae_decompose_neg y) as [Ey|?].
    rewrite (F $ Ey), (F $ ae_pos_mult_minf_r _); apply _.
    split. apply _. now destruct (_ : x*y ∊ R₋).
  Qed.

  Context `{!StandardUnEq F} `{!SubDecision F F (=)}.

  Lemma ae_zero_nonzero x `{x ∊ R∞} : x = 0 ∨ x ∊ R∞ ₀.
  Proof. destruct (decide_sub (=) x 0). now left.
    right. split. apply _. now apply (standard_uneq _ _).
  Qed.

  Lemma ae_decompose_ext_sign x `{x ∊ R∞} : x = 0 ∨ (x ∊ R∞₊ ∨ x ∊ R∞₋).
  Proof. destruct (ae_zero_nonzero x). now left. right. apply (ae_decompose_nonzero x). Qed.

  Lemma ae_mult_inf_comm x `{x ∊ F} : x * ∞ = ∞ * x.
  Proof. destr_F x.
    destruct (ae_decompose_ext_sign x) as [Ex |[?|?]].
    rewrite (F $ Ex). undef_eq.
    subtransitivity infty;[|subsymmetry].
      exact (ae_pos_mult_inf_r _).
      exact (ae_pos_mult_inf_l _).
    subtransitivity (-infty);[|subsymmetry].
      exact (ae_neg_mult_inf_r _).
      exact (ae_neg_mult_inf_l _).
  Qed.

  Lemma ae_mult_minf_comm x `{x ∊ F} : x * -∞ = -∞ * x.
  Proof. destr_F x.
    destruct (ae_decompose_ext_sign x) as [Ex |[?|?]].
    rewrite (F $ Ex). undef_eq.
    subtransitivity (-infty);[|subsymmetry].
      exact (ae_pos_mult_minf_r _).
      exact (ae_pos_mult_minf_l _).
    subtransitivity infty;[|subsymmetry].
      exact (ae_neg_mult_minf_r _).
      exact (ae_neg_mult_minf_l _).
  Qed.

  Instance ae_mult_comm: Commutative (.*.) F.
  Proof. intros x ? y ?. destr_F x. destr_F y.
    decompose_ext x.
    + decompose_ext y.
      * exact (commutativity (.*.) _ _).
      * exact (ae_mult_inf_comm _).
      * exact (ae_mult_minf_comm _).
    + subsymmetry. exact (ae_mult_inf_comm _).
    + subsymmetry. exact (ae_mult_minf_comm _).
  Qed.

  Lemma ae_mult_closed_notR_l : Closed (notR ⇀ F ⇀ notR) (.*.).
  Proof. intros x ? y ?. assert (x ∊ F) by firstorder. destruct (ae_decompose_R_notR y).
    destr_notR x. apply (_ : SubsetOf U notR). apply _.
    destruct (ae_decompose_ext_sign y) as [Ey|[?|?]]. rewrite (F $ Ey).
      apply (_ : SubsetOf U notR). apply (ae_mult_0_notR_r _). apply _.
      rewrite (F $ ae_pos_mult_inf_l y). apply _.
      rewrite (F $ ae_neg_mult_inf_l y). apply _.
    destruct (ae_decompose_ext_sign y) as [Ey|[?|?]]. rewrite (F $ Ey).
      apply (_ : SubsetOf U notR). apply (ae_mult_0_notR_r _). apply _.
      rewrite (F $ ae_pos_mult_minf_l y). apply _.
      rewrite (F $ ae_neg_mult_minf_l y). apply _.
    now apply ae_mult_closed_notR.
  Qed.

  Lemma ae_mult_closed_notR_r : Closed (F ⇀ notR ⇀ notR) (.*.).
  Proof. intros x ? y ?. assert (y ∊ F) by firstorder.
    rewrite (F $ commutativity (.*.) x y).
    now apply ae_mult_closed_notR_l.
  Qed.

End mult.

Hint Extern 2 (0 * _ ∊ U) => eapply @ae_mult_0_notR_l : typeclass_instances.
Hint Extern 2 (_ * 0 ∊ U) => eapply @ae_mult_0_notR_r : typeclass_instances.
Hint Extern 3 (_ * _ ∊ notR) => eapply @ae_mult_closed_notR_l : typeclass_instances.
Hint Extern 3 (_ * _ ∊ notR) => eapply @ae_mult_closed_notR_r : typeclass_instances.
Hint Extern 4 (_ * _ ∊ R∞₊) => eapply @ae_pos_mult : typeclass_instances.
Hint Extern 7 (_ * _ ∊ R∞₊) => eapply @ae_neg_mult : typeclass_instances.
Hint Extern 7 (_ * _ ∊ R∞₋) => eapply @ae_pos_neg_mult : typeclass_instances.
Hint Extern 7 (_ * _ ∊ R∞₋) => eapply @ae_neg_pos_mult : typeclass_instances.

Hint Extern 2 (Commutative (.*.) F) => eapply @ae_mult_comm : typeclass_instances.

Section mult_ass.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.
  Context `{!StandardUnEq F} `{!SubDecision F F (=)}.

  Lemma ae_mult_ass_0_1 x `{x ∊ F} y `{y ∊ F} : 0 * (x * y) = 0 * x * y.
  Proof. destruct (ae_decompose_R_notR x). destruct (ae_decompose_R_notR y).
    exact (associativity (.*.) _ _ _).
    rewrite (F $ mult_0_l x). undef_eq.
    undef_eq.
  Qed.

  Lemma ae_mult_ass_0_2 x `{x ∊ F} y `{y ∊ F} : x * (0 * y) = x * 0 * y.
  Proof. destruct (ae_decompose_R_notR x); destruct (ae_decompose_R_notR y).
    exact (associativity (.*.) _ _ _).
    rewrite (F $ mult_0_r x). undef_eq.
    rewrite (F $ mult_0_l y). undef_eq.
    undef_eq.
  Qed.

  Lemma ae_mult_ass_0_3 x `{x ∊ F} y `{y ∊ F} : x * (y * 0) = x * y * 0.
  Proof. destruct (ae_decompose_R_notR y). destruct (ae_decompose_R_notR x).
    exact (associativity (.*.) _ _ _).
    rewrite (F $ mult_0_r y). undef_eq.
    undef_eq.
  Qed.

  Ltac mult_inf_tac := repeat match goal with
    | |- context [ ∞ * ?x ] =>
         first [ rewrite (F $ ae_pos_mult_inf_l x) | rewrite (F $ ae_neg_mult_inf_l x) ]
    | |- context [ ?x * ∞ ] =>
         first [ rewrite (F $ ae_pos_mult_inf_r x) | rewrite (F $ ae_neg_mult_inf_r x) ]
    | |- context [ -∞ * ?x ] =>
         first [ rewrite (F $ ae_pos_mult_minf_l x) | rewrite (F $ ae_neg_mult_minf_l x) ]
    | |- context [ ?x * -∞ ] =>
         first [ rewrite (F $ ae_pos_mult_minf_r x) | rewrite (F $ ae_neg_mult_minf_r x) ]
    end.

  Ltac mult_inf_ass_tac_pos x := let E := fresh "E" in
    destruct (ae_decompose_pos x) as [E|?]; [rewrite (F $ E); now mult_inf_tac |].
  Ltac mult_inf_ass_tac_neg x := let E := fresh "E" in
    destruct (ae_decompose_neg x) as [E|?]; [rewrite (F $ E); now mult_inf_tac |].
  Ltac mult_inf_ass_tac_aux x :=
    match goal with
    | H : x ∊ R∞₊ |- _ => mult_inf_ass_tac_pos x
    | H : x ∊ R∞₋ |- _ => mult_inf_ass_tac_neg x
    end.
  Ltac mult_inf_ass_tac x y z :=
    mult_inf_ass_tac_aux x; mult_inf_ass_tac_aux y; mult_inf_ass_tac_aux z;
    exact (associativity (.*.) _ _ _).

  Lemma ae_mult_ass_ppp x `{x ∊ R∞₊} y `{y ∊ R∞₊} z `{z ∊ R∞₊} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_ppn x `{x ∊ R∞₊} y `{y ∊ R∞₊} z `{z ∊ R∞₋} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_pnp x `{x ∊ R∞₊} y `{y ∊ R∞₋} z `{z ∊ R∞₊} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_pnn x `{x ∊ R∞₊} y `{y ∊ R∞₋} z `{z ∊ R∞₋} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_npp x `{x ∊ R∞₋} y `{y ∊ R∞₊} z `{z ∊ R∞₊} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_npn x `{x ∊ R∞₋} y `{y ∊ R∞₊} z `{z ∊ R∞₋} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_nnp x `{x ∊ R∞₋} y `{y ∊ R∞₋} z `{z ∊ R∞₊} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.
  Lemma ae_mult_ass_nnn x `{x ∊ R∞₋} y `{y ∊ R∞₋} z `{z ∊ R∞₋} : x*(y*z) = x*y*z. Proof. mult_inf_ass_tac x y z. Qed.

  Instance ae_mult_ass : Associative (.*.) F.
  Proof. intros x ? y ? z ?. destr_F x. destr_F y. destr_F z.
    destruct (ae_zero_nonzero x) as [E|?]. rewrite (F $ E). exact (ae_mult_ass_0_1 _ _).
    destruct (ae_zero_nonzero y) as [E|?]. rewrite (F $ E). exact (ae_mult_ass_0_2 _ _).
    destruct (ae_zero_nonzero z) as [E|?]. rewrite (F $ E). exact (ae_mult_ass_0_3 _ _).
    destruct (ae_decompose_nonzero x);
    destruct (ae_decompose_nonzero y);
    destruct (ae_decompose_nonzero z).
    exact (ae_mult_ass_ppp _ _ _).
    exact (ae_mult_ass_ppn _ _ _).
    exact (ae_mult_ass_pnp _ _ _).
    exact (ae_mult_ass_pnn _ _ _).
    exact (ae_mult_ass_npp _ _ _).
    exact (ae_mult_ass_npn _ _ _).
    exact (ae_mult_ass_nnp _ _ _).
    exact (ae_mult_ass_nnn _ _ _).
  Qed.
End mult_ass.

Hint Extern 2 (Associative (.*.) F) => eapply @ae_mult_ass : typeclass_instances.

Section misc.
  Context `{AffinelyExtendedRing A (R:=R)}.
  Hint Extern 10 (@Subset A) => eexact F : typeclass_instances.

  Lemma ae_nonneg_sum_finite_bound x `{x ∊ R∞⁺} y `{y ∊ R∞⁺} z `{z ∊ R}
    : x + y ≤ z → x ∊ R⁺ ∧ y ∊ R⁺.
  Proof. intro E.
    destruct (ae_decompose_nonneg x) as [Ex|?].
    rewrite (_ $ Ex), (_ $ ae_nonneg_plus_inf_l _) in E.
      destruct (lt_not_le_flip (P:=R∞) ∞ z). exact (ae_inf_sub _). trivial.
    destruct (ae_decompose_nonneg y) as [Ey|?].
    rewrite (_ $ Ey), (_ $ ae_nonneg_plus_inf_r _) in E.
      destruct (lt_not_le_flip (P:=R∞) ∞ z). exact (ae_inf_sub _). trivial.
    now split.
  Qed.

  Lemma ae_pos_sum_finite_bound x `{x ∊ R∞₊} y `{y ∊ R∞₊} z `{z ∊ R}
    : x + y ≤ z → x ∊ R₊ ∧ y ∊ R₊.
  Proof. intro E. destruct (ae_nonneg_sum_finite_bound _ _ _ E).
    split; split; try apply _.
    now destruct (_ : x ∊ R∞₊).
    now destruct (_ : y ∊ R∞₊).
  Qed.

  Lemma ae_pos_finite_bound x `{x ∊ R∞₊} z `{z ∊ R} : x ≤ z → x ∊ R₊ .
  Proof. intro E. rewrite <- (_ $ ae_plus_0_l x) in E.
    destruct (ae_nonneg_sum_finite_bound _ _ _ E).
    split. apply _. now destruct (_ : x ∊ R∞₊).
  Qed.

End misc.

