Require Import
  abstract_algebra interfaces.field_of_fractions theory.strong_setoids
  theory.common_props theory.subrings theory.fields.
Require Import stdlib_ring misc.quote.

Local Open Scope grp_scope. (* notation for inverse *)

Inductive FracPair (A:Type) := frac { num : A ; den : A }.
Arguments frac {A} _ _.
Arguments num {A} _.
Arguments den {A} _.

Section def.
  Context {A} {Aue:UnEq A} {Azero:Zero A} (D : @Subset A).

  Definition Frac : @Subset (FracPair A) := λ f, let (a,b) := f in a ∊ D ∧ b ∊ D ₀.

  Lemma Frac_num_elt x `{x ∊ Frac} : num x ∊ D.   Proof. unfold Frac in *. destruct x. firstorder. Qed.
  Lemma Frac_den_elt x `{x ∊ Frac} : den x ∊ D ₀. Proof. unfold Frac in *. destruct x. firstorder. Qed.
  Lemma Frac_den_elt2 x `{x ∊ Frac} : den x ∊ D. Proof. now destruct (Frac_den_elt x). Qed.
End def.

Hint Extern 10 (@Subset (FracPair _)) => eapply @Frac : typeclass_instances.
Hint Extern 5 (num _ ∊ _)   => eapply @Frac_num_elt : typeclass_instances.
Hint Extern 5 (den _ ∊ _ ₀) => eapply @Frac_den_elt : typeclass_instances.
Hint Extern 6 (den _ ∊ _)   => eapply @Frac_den_elt2 : typeclass_instances.

Section ops.
  Context `{IntegralDomain A (D:=D)}.

  Definition frac_equiv : Equiv (FracPair A) := λ f f', let (a,b) := f in let (c,d) := f' in a*d = b*c.
  Definition frac_uneq  : UnEq  (FracPair A) := λ f f', let (a,b) := f in let (c,d) := f' in a*d ≠ b*c.

  Global Instance frac_inject : Cast D (Frac D) := λ x, frac x 1.

  Definition frac_zero   : Zero   (FracPair _) := frac 0 1.
  Definition frac_one    : One    (FracPair _) := frac 1 1.
  Definition frac_plus   : Plus   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in frac (a*d + b*c) (b*d).
  Definition frac_mult   : Mult   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in frac (a*c) (b*d).
  Definition frac_negate : Negate (FracPair _) := λ f, let (a,b) := f in frac (- a) b.
  Definition frac_inv    : Inv    (FracPair A) := λ f, let (a,b) := f in frac b a.
End ops.

Hint Extern 0 (Equiv   (FracPair _ )) => eapply @frac_equiv  : typeclass_instances.
Hint Extern 0 (Equiv   (elt_type (Frac _ ))) => eapply @frac_equiv  : typeclass_instances.
Hint Extern 0 (UnEq    (FracPair _ )) => eapply @frac_uneq   : typeclass_instances.
Hint Extern 0 (UnEq    (elt_type (Frac _ ))) => eapply @frac_uneq  : typeclass_instances.
Hint Extern 0 (Zero    (FracPair _ )) => eapply @frac_zero   : typeclass_instances.
Hint Extern 0 (One     (FracPair _ )) => eapply @frac_one    : typeclass_instances.
Hint Extern 0 (Plus    (FracPair _ )) => eapply @frac_plus   : typeclass_instances.
Hint Extern 0 (Mult    (FracPair _ )) => eapply @frac_mult   : typeclass_instances.
Hint Extern 0 (Negate  (FracPair _ )) => eapply @frac_negate : typeclass_instances.
Hint Extern 0 (Inv     (FracPair _ )) => eapply @frac_inv    : typeclass_instances.

Section contents.
  Context `{IntegralDomain (D:=D)}.

  Add Ring D1 : (stdlib_ring_theory D).

  Notation F := (Frac D).

  Instance: StrongSetoid F.
  Proof. split; [split|]; unfold uneq, frac_uneq.
  + intros [a b] [??]. rewrite (D $ commutativity (.*.) a b). exact (subirreflexivity _ _).
  + intros [a b] [??] [c d] [??] E. 
    rewrite_on D -> (commutativity (.*.) c b), (commutativity (.*.) d a). subsymmetry.
  + intros [a b] [??] [c d] [??] E [e f] [??].
    pose proof strong_right_cancellation (.*.) f D _ _ E as E2.
    destruct (subcotransitivity E2 (b*d*e)); [left|right].
    * apply (strong_extensionality (.* d)).
      mc_replace (a*f*d) with (a*d*f) on D by subring D.
      mc_replace (b*e*d) with (b*d*e) on D by subring D. trivial.
    * apply (strong_extensionality (.* b)).
      mc_replace (e*d*b) with (b*d*e) on D by subring D.
      mc_replace (f*c*b) with (b*c*f) on D by subring D. trivial.
  + intros [a b] [??] [c d] [??]. exact (tight_apart (a*d) (b*c)).
  Qed.

  Instance: Strong_Binary_Morphism F F F (+).
  Proof. split.
  + intros [a b] [??] [c d] [??]. split; apply _.
  + rewrite strong_ext_equiv_2.
    intros [a1 b1] [??] [a2 b2] [??] [c1 d1] [??] [c2 d2] [??] E.
    unfold plus, frac_plus, uneq, frac_uneq in *.
    rewrite (D $ plus_mult_distr_l _ _ _), (D $ plus_mult_distr_r _ _ _) in E.
    destruct (strong_binary_extensionality (+) E) as [E2|E2]; [left|right]; clear E.
    * apply (strong_extensionality (.* (d1*d2))).
      mc_replace (a1*b2*(d1*d2)) with (a1*d1*(b2*d2)) on D by subring D.
      mc_replace (b1*a2*(d1*d2)) with (b1*d1*(a2*d2)) on D by subring D. trivial.
    * apply (strong_extensionality (.* (b1*b2))).
      mc_replace (c1*d2*(b1*b2)) with (b1*c1*(b2*d2)) on D by subring D.
      mc_replace (d1*c2*(b1*b2)) with (b1*d1*(b2*c2)) on D by subring D. trivial.
  Qed.

  Instance: Strong_Binary_Morphism F F F (.*.).
  Proof. split.
  + intros [a b] [??] [c d] [??]. split; apply _.
  + rewrite strong_ext_equiv_2.
    intros [a1 b1] [??] [a2 b2] [??] [c1 d1] [??] [c2 d2] [??] E.
    unfold mult, frac_mult, uneq, frac_uneq in *.
    apply (strong_binary_extensionality (.*.)).
    mc_replace (a1*b2*(c1*d2)) with (a1*c1*(b2*d2)) on D by subring D.
    mc_replace (b1*a2*(d1*c2)) with (b1*d1*(a2*c2)) on D by subring D. trivial.
  Qed.

  Local Ltac reduce := unfold equiv, frac_equiv; simpl.
  Local Ltac reduce_sig := split; [ split; split; apply _ | reduce ].
  Local Ltac dispatch1 E := change E; intros [a b] [??]; reduce; subring D.
  Local Ltac dispatch2 E := change E; intros [a b] [??] [c d] [??]; reduce; subring D.
  Local Ltac dispatch3 E := change E; intros [a b] [??] [c d] [??] [e f] [??]; reduce; subring D.

  Instance: Morphism (F ⇒ F) (-).
  Proof.
    intros [a1 b1] [a2 b2] E1. unfold_sigs.
    destruct el, el0. reduce_sig.
    rewrite_on D <- (negate_mult_distr_l a1 b2), E1. subring D.
  Qed.

  Instance: CommutativeRing F.
  Proof. split. split; try apply _. split. split. split; try apply _.
  + dispatch3 (Associative (+) F).
  + dispatch2 (Commutative (+) F).
  + change (0 ∊ F). split; apply _.
  + dispatch1 (LeftIdentity (+) 0 F).
  + dispatch1 (LeftInverse (+) (-) 0 F).
  + split. split. split; try apply _.
  - dispatch3 (Associative (.*.) F).
  - dispatch2 (Commutative (.*.) F).
  - change (1 ∊ F). split; apply _.
  - dispatch1 (LeftIdentity (.*.) 1 F).
  + dispatch3 (LeftDistribute (.*.) (+) F).
  Qed.

  Lemma frac_nonzero : F ₀ = λ f, let (a,b) := f in a ∊ D ₀ ∧ b ∊ D ₀.
  Proof. intros [a b]. split.
  + intros [[??]nz]. unfold uneq, frac_uneq in nz. simpl in nz.
    rewrite (D $ mult_1_r a), (D $ mult_0_r b) in nz.
    split. split; apply _. apply _.
  + intros [[? anz]?]. split. split; apply _.
    red. unfold uneq, frac_uneq. simpl.
    now rewrite (D $ mult_1_r a), (D $ mult_0_r b).
  Qed.

  Global Instance: Field F.
  Proof. split; try apply _. split; try apply _.
  + unfold uneq, frac_uneq. simpl. rewrite_on D -> (mult_1_l 1), (mult_1_l 0). apply _.
  + intros [a1 b1] [a2 b2] [[el0 el1] E1].
    rewrite frac_nonzero in el0. rewrite frac_nonzero in el1. destruct el0. destruct el1.
    split. split; rewrite frac_nonzero; now split. reduce. subsymmetry.
  + intros [a b] el. rewrite frac_nonzero in el. destruct el. reduce. subring D.
  Qed.

  Global Instance: Strong_Morphism D F (').
  Proof. split.
  + intros ?. split; apply _.
  + rewrite strong_ext_equiv_1. intros x ? y ? E.
    now rewrite <- (D $ mult_1_r x), <- (D $ mult_1_l y).
  Qed.

  Global Instance: Ring_Morphism D F (').
  Proof with try apply _. split... split...
  + split... intros x ? y ?. unfold cast, frac_inject. reduce.
    replace (x & y) with (x+y) by easy. subring D.
  + split... intros x ? y ?. unfold cast, frac_inject. reduce.
    replace (x & y) with (x*y) by easy. subring D.
  + exists_sub (1:D). apply (subreflexivity (S:=F)). apply _.
  Qed.

  Global Instance: StrongInjective D F (').
  Proof. apply strong_injective_preserves_0.
    intros x ?. rewrite frac_nonzero. split; apply _.
  Qed.

  Lemma Frac_num_div_den x {el:x ∊ F} : x = ' num x / ' den x.
  Proof. destruct x as [a b]. destruct el as [??].
    unfold cast, frac_inject. reduce. subring D.
  Qed.

  Lemma Frac_mult_den_num x {el:x ∊ F} : x * ' den x = ' num x.
  Proof. destruct x as [a b]. destruct el as [??].
    unfold cast, frac_inject. reduce. subring D.
  Qed.

  Lemma Frac_equiv_num_den x `{x ∊ F} y `{y ∊ F} : x = y ↔ num x * den y = den x * num y.
  Proof. destruct x as [a b], y as [c d]. now reduce. Qed.

  (*
  Lemma Frac_num_plus x {elx:x ∊ F} y {ely:y ∊ F} : num (x+y) = num x * den y + den x * num y.
  Proof. destruct x as [a b], elx as [??], y as [c d], ely as [??]. now reduce. Qed.

  Lemma Frac_den_plus x {elx:x ∊ F} y {ely:y ∊ F} : den (x+y) = den x * den y.
  Proof. destruct x as [a b], elx as [??], y as [c d], ely as [??]. now reduce. Qed.
  *)

  Instance intdom_to_Frac: ToFieldOfFracs D F := (').
  Instance Frac_to_field:  FracToField D F := λ _ _ _ _ _ _ _ _ h x, h (num x) / h (den x).

  Section another_field.

    Context `{Field (F:=F2)} (h:D ⇀ F2) `{!Ring_Morphism D F2 h} `{!StrongInjective D F2 h}.

    Add Ring F2 : (stdlib_ring_theory F2).

    Instance: Strong_Morphism D F2 h := strong_injective_mor _.

    Instance: Strong_Morphism F F2 (frac_to_field F F2 h).
    Proof. unfold frac_to_field, Frac_to_field. split.
    + intros [??] [??]. simpl. apply _.
    + rewrite strong_ext_equiv_1.
      intros [n1 d1] [??] [n2 d2] [??] E. simpl in E. do 2 red.
      rewrite <- (mult_inv_strong_cancel_both _ _ _ _) in E.
      apply (strong_extensionality h). now rewrite 2!(F2 $ preserves_mult _ _).
    Qed.

    Instance: Ring_Morphism F F2 (frac_to_field F F2 h).
    Proof. apply ring_morphism_alt; try apply _; unfold frac_to_field, Frac_to_field.
    + intros [n1 d1] [??] [n2 d2] [??]; simpl. preserves_simplify h.
      rewrite (F2 $ mult_inv_distr _ _).
      mc_replace ( (h n1 * h d2 + h d1 * h n2) * ((h d1)⁻¹ / h d2) )
           with ( (h n1 / h d1) * (h d2 / h d2) + (h n2 / h d2) * (h d1 / h d1) ) on F2 by subring F2.
      now rewrite 2!(F2 $ field_inv_r _), 2!(F2 $ mult_1_r _).
    + intros [n1 d1] [??] [n2 d2] [??]; simpl. preserves_simplify h.
      rewrite (F2 $ mult_inv_distr _ _). subring F2.
    + change (h 1 / h 1 = 1). preserves_simplify h. exact (field_inv_r 1).
    Qed.

    Instance Frac_to_field_spec : FracToFieldSpec D F F2 h (frac_to_field F F2 h).
    Proof. split; try apply _; unfold frac_to_field, Frac_to_field, to_field_of_fracs, intdom_to_Frac.
    + intros x y E. unfold_sigs. red_sig. unfold compose, cast, frac_inject. simpl.
      preserves_simplify h. now rewrite (F2 $ mult_inv_1), (F2 $ mult_1_r _), (D $ E).
    + intros g ? ? E. change (g ∘ (') = h) in E.
      unfold frac_to_field, Frac_to_field. intros y x [[? el] Ex]. red_sig.
      rewrite (F $ Ex). clear dependent y.
      rewrite (F $ Frac_num_div_den x) at 1.
      destruct x as [n d], el as [??]. simpl. preserves_simplify g.
      rewrite <- (mult_inv_cancel_both _ _ _ _).
      rewrite (E n n), (E d d); try now red_sig. exact (commutativity (.*.) _ _).
    Qed.

  End another_field.

  Existing Instance Frac_to_field_spec.

  Instance Frac_spec : Field_of_Fractions D F := {}.

End contents.

Hint Extern 2 (ToFieldOfFracs _ (Frac _)) => eapply @intdom_to_Frac : typeclass_instances.
Hint Extern 2 (FracToField _ (Frac _)) => eapply @Frac_to_field : typeclass_instances.
Hint Extern 2 (Field_of_Fractions _ (Frac _)) => eapply @Frac_spec : typeclass_instances.

Section dec.
  Context `{IntegralDomain A (D:=D)}.

  Notation F := (Frac D).

  Instance Frac_standard_uneq `{!StandardUnEq D} : StandardUnEq F.
  Proof. intros [a b][??] [c d][??]. unfold equiv, frac_equiv, uneq, frac_uneq.
    exact (standard_uneq _ _).
  Qed.

  Instance Frac_dec_eq `{∀ (x y : A), Decision (x = y)} (x y : FracPair A) : Decision (x=y).
  Proof. destruct x, y. unfold equiv, frac_equiv. exact (decide_rel (=) _ _). Defined.

  Program Instance Frac_strong_subdec_eq `{!StrongSubDecision D D (=)} : StrongSubDecision F F (=)
    := λ x y, match decide_sub_strong (=) (num x * den y) (den x * num y) with
       | left _ => left _
       | right _ => right _
       end.
  Next Obligation. rewrite (Frac_equiv_num_den _ _).
    pose proof (_ : num x * den y ∊ D). pose proof (_ : den x * num y ∊ D). auto.
  Qed.
  Next Obligation. rewrite (Frac_equiv_num_den _ _).
    pose proof (_ : num x * den y ∊ D). pose proof (_ : den x * num y ∊ D). auto.
  Qed.

  Instance Frac_subdec_eq `{!SubDecision D D (=)} : SubDecision F F (=).
  Proof. intros [a b][??][c d][??]. unfold equiv, frac_equiv.
    exact (decide_sub (=) _ _).
  Defined.
End dec.

Hint Extern 2 (StandardUnEq (Frac _)) => eapply @Frac_standard_uneq : typeclass_instances.
Hint Extern 2 (Decision (@equiv _ frac_equiv _ _)) => eapply @Frac_dec_eq : typeclass_instances.
Hint Extern 2 (StrongSubDecision (Frac _) (Frac _) (=)) => eapply @Frac_strong_subdec_eq : typeclass_instances.
Hint Extern 2 (SubDecision (Frac _) (Frac _) (=)) => eapply @Frac_subdec_eq : typeclass_instances.

