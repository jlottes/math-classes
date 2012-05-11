Require Import
  abstract_algebra theory.setoids theory.common_props theory.subrings
  theory.fields.
Require Import Ring stdlib_ring.

Local Open Scope grp_scope. (* notation for inverse *)

Inductive FracPair (A:Type) := C { num : A ; den : A }.
Arguments C {A} _ _.

Definition Frac {A} {Aue:UnEq A} {Azero:Zero A} D : Subset (FracPair A) := 
  λ f, let (a,b) := f in a ∊ D ∧ b ∊ D ₀.

Section ops.
  Context `{IntegralDomain A (R:=D)}.

  Definition frac_equiv : Equiv (FracPair A) := λ f f', let (a,b) := f in let (c,d) := f' in a*d = b*c.
  Definition frac_uneq  : UnEq  (FracPair A) := λ f f', let (a,b) := f in let (c,d) := f' in a*d ≠ b*c.

  Definition frac_inject : Cast A (FracPair A) := λ x, C x 1.

  Definition frac_zero   : Zero   (FracPair _) := C 0 1.
  Definition frac_one    : One    (FracPair _) := C 1 1.
  Definition frac_plus   : Plus   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in C (a*d + b*c) (b*d).
  Definition frac_mult   : Mult   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in C (a*c) (b*d).
  Definition frac_negate : Negate (FracPair _) := λ f, let (a,b) := f in C (- a) b.
  Definition frac_inv    : Inv    (FracPair A) := λ f, let (a,b) := f in C b a.
End ops.

Hint Extern 0 (Equiv   (FracPair _ )) => eexact frac_equiv  : typeclass_instances.
Hint Extern 0 (UnEq    (FracPair _ )) => eexact frac_uneq   : typeclass_instances.
Hint Extern 0 (Cast ?A (FracPair ?A)) => eexact frac_inject : typeclass_instances.
Hint Extern 0 (Zero    (FracPair _ )) => eexact frac_zero   : typeclass_instances.
Hint Extern 0 (One     (FracPair _ )) => eexact frac_one    : typeclass_instances.
Hint Extern 0 (Plus    (FracPair _ )) => eexact frac_plus   : typeclass_instances.
Hint Extern 0 (Mult    (FracPair _ )) => eexact frac_mult   : typeclass_instances.
Hint Extern 0 (Negate  (FracPair _ )) => eexact frac_negate : typeclass_instances.
Hint Extern 0 (Inv     (FracPair ?A)) => eexact (frac_inv (A:=A)) : typeclass_instances.

Section contents.
  Context `{IntegralDomain (R:=D)}.

  Add Ring D1 : (stdlib_ring_theory D).

  Notation F := (Frac D).

  Instance: Setoid F.
  Proof. split; unfold equiv, frac_equiv.
  + intros [a b] [??]. exact (commutativity (.*.) a b).
  + intros [a b] [??] [c d] [??] E.
    rewrite_on D -> (commutativity (.*.) c b), (commutativity (.*.) d a).
    subsymmetry.
  + intros [a b] [??] [c d] [??] [e f] [??] E1 E2.
    apply (left_cancellation (.*.) d D _ _).
    subtransitivity (a*d*f). subring D. rewrite_on D -> E1.
    subtransitivity (b*(c*f)). subring D. rewrite_on D -> E2.
    subring D.
  Qed.

  Local Ltac reduce := unfold equiv, frac_equiv; simpl.
  Local Ltac reduce_sig := split; [ split; split; apply _ | reduce ].
  Local Ltac dispatch1 E := change E; intros [a b] [??]; reduce; subring D.
  Local Ltac dispatch2 E := change E; intros [a b] [??] [c d] [??]; reduce; subring D.
  Local Ltac dispatch3 E := change E; intros [a b] [??] [c d] [??] [e f] [??]; reduce; subring D.

  Instance: Setoid_Binary_Morphism F F F (+).
  Proof.
    split; try apply _. intros [a1 b1] [a2 b2] E1 [c1 d1] [c2 d2] E2. unfold_sigs.
    destruct el, el0, el1, el2. reduce_sig.
    subtransitivity (d1 * (a1 * b2) * d2 + b1 * (c1 * d2) * b2). subring D.
    rewrite_on D -> E1, E2. subring D.
  Qed.

  Instance: Setoid_Morphism F F (-).
  Proof.
    split; try apply _. intros [a1 b1] [a2 b2] E1. unfold_sigs.
    destruct el, el0. reduce_sig.
    rewrite_on D <- (negate_mult_distr_l a1 b2), E1. subring D.
  Qed.

  Instance: Setoid_Binary_Morphism F F F (.*.).
  Proof.
    split; try apply _. intros [a1 b1] [a2 b2] E1 [c1 d1] [c2 d2] E2. unfold_sigs.
    destruct el, el0, el1, el2. reduce_sig.
    subtransitivity ((a1*b2)*(c1*d2)). subring D.
    rewrite_on D -> E1, E2. subring D.
  Qed.

  Global Instance: CommutativeRing F.
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

  Instance: Setoid_Morphism D F (cast _ _).
  Proof. split; try apply _. intros ?? E. unfold_sigs. reduce_sig. rewrite_on D -> E. subring D. Qed.

  Instance: Ring_Morphism D F (cast _ _).
  Proof with try apply _. split... split...
  + split... intros x ? y ?. unfold cast, frac_inject. reduce.
    replace (x & y) with (x+y) by easy. subring D.
  + split... intros x ? y ?. unfold cast, frac_inject. reduce.
    replace (x & y) with (x*y) by easy. subring D.
  + exists_sub (1:A). apply (subreflexivity (S:=F)). apply _.
  Qed.

  Instance: Injective D F (cast _ _).
  Proof. rewrite <- (rng_mor_injective (cast _ _)).
    intros x ? E. unfold cast, frac_inject, equiv, frac_equiv in E. simpl in E.
    subtransitivity (x*1). subsymmetry. exact (mult_1_r x).
    subtransitivity (1*0). exact (mult_1_l 0).
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

  Instance frac_nontrivial: PropHolds (1 ≠ (0:FracPair A)).
  Proof. unfold uneq, frac_uneq. simpl.
    rewrite_on D -> (mult_1_l 1), (mult_1_l 0). apply _.
  Qed.

  Lemma frac_inv_mor: Setoid_Morphism (F ₀) (F ₀) (⁻¹).
  Proof. rewrite frac_nonzero. pose proof _ : Setoid (F ₀) as S. rewrite frac_nonzero in S.
    split; try apply _.
    intros [a1 b1] [a2 b2] E1. unfold_sigs. destruct el, el0. reduce_sig. subsymmetry.
  Qed.

  Lemma frac_left_inv : LeftInverse (.*.) (⁻¹) 1 (F ₀).
  Proof. intros [a b] el. rewrite frac_nonzero in el. destruct el. reduce. subring D. Qed.

End contents.

Hint Extern 3 (PropHolds (@uneq _ frac_uneq 1 0)) => eapply @frac_nontrivial : typeclass_instances.

Section dec.
  Context `{IntegralDomain (R:=D)} `{!StandardUnEq D} `{!SubDecision D D (=)}.

  Add Ring D2 : (stdlib_ring_theory D).

  Notation F := (Frac D).

  Instance: StandardUnEq F.
  Proof. intros [a b][??] [c d][??]. unfold equiv, frac_equiv, uneq, frac_uneq.
    exact (standard_uneq _ _).
  Qed.

  Instance: SubDecision F F (=).
  Proof. intros [a b][??][c d][??]. unfold equiv, frac_equiv.
    exact (decide_sub (=) _ _).
  Defined.

  Instance: Field F.
  Proof. apply dec_field. exact frac_inv_mor. exact frac_left_inv. Qed.

End dec.




