Require Import
  Ring abstract_algebra interfaces.orders theory.strong_setoids theory.common_props
  theory.rings orders.rings stdlib_ring.

Inductive SRpairT (A : Type) := C { pos : A ; neg : A }.
Arguments C {A} _ _.
Arguments pos {A} _.
Arguments neg {A} _.

Definition SRpair `(SR:Subset) : @Subset (SRpairT _) :=  λ f, let (a,b) := f in a ∊ SR ∧ b ∊ SR.
Hint Extern 10 (@Subset (SRpairT _)) => eapply @SRpair : typeclass_instances.

Lemma SRpair_every {A} : ∀ x, x ∊ SRpair (every A).
Proof. intros [??]. split; apply _. Qed.
Hint Extern 1 (_ ∊ SRpair (every _)) => eapply @SRpair_every : typeclass_instances.

Section ops.
  Context `{CommutativeSemiRing A (R:=SR)}.

  Definition SRpair_equiv : Equiv (SRpairT A) := λ p q, let (a,b) := p in let (c,d) := q in a+d = c+b.
  Definition SRpair_uneq `{UnEq A} : UnEq  (SRpairT A) := λ p q, let (a,b) := p in let (c,d) := q in a+d ≠ c+b.
  Definition SRpair_le `{Le A} : Le (SRpairT A) := λ p q, let (a,b) := p in let (c,d) := q in a+d ≤ c+b.
  Definition SRpair_lt `{Lt A} : Lt (SRpairT A) := λ p q, let (a,b) := p in let (c,d) := q in a+d < c+b.

  Definition SRpair_inject : Cast SR (SRpair SR) := λ x, C x 0.

  Definition SRpair_zero   : Zero   (SRpairT _) := C 0 0.
  Definition SRpair_one    : One    (SRpairT _) := C 1 0.
  Definition SRpair_plus   : Plus   (SRpairT _) := λ p q, let (a,b) := p in let (c,d) := q in C (a+c) (b+d).
  Definition SRpair_mult   : Mult   (SRpairT _) := λ p q, let (a,b) := p in let (c,d) := q in C (a*c+b*d) (a*d+b*c).
  Definition SRpair_negate : Negate (SRpairT A) := λ p, let (a,b) := p in C b a.
End ops.

Global Existing Instance SRpair_inject.

Hint Extern 0 (Equiv   (SRpairT _)) => eapply @SRpair_equiv  : typeclass_instances.
Hint Extern 0 (Equiv   (elt_type (SRpair _))) => eapply @SRpair_equiv  : typeclass_instances.
Hint Extern 0 (UnEq    (SRpairT _)) => eapply @SRpair_uneq   : typeclass_instances.
Hint Extern 0 (UnEq    (elt_type (SRpair _))) => eapply @SRpair_uneq  : typeclass_instances.
Hint Extern 0 (Le      (SRpairT _)) => eapply @SRpair_le     : typeclass_instances.
Hint Extern 0 (Lt      (SRpairT _)) => eapply @SRpair_lt     : typeclass_instances.
Hint Extern 0 (Zero    (SRpairT _)) => eapply @SRpair_zero   : typeclass_instances.
Hint Extern 0 (One     (SRpairT _)) => eapply @SRpair_one    : typeclass_instances.
Hint Extern 0 (Plus    (SRpairT _)) => eapply @SRpair_plus   : typeclass_instances.
Hint Extern 0 (Mult    (SRpairT _)) => eapply @SRpair_mult   : typeclass_instances.
Hint Extern 0 (Negate  (SRpairT _)) => eapply @SRpair_negate : typeclass_instances.

Local Ltac reduce :=
  repeat match goal with
  |  |- (@equiv _ SRpair_equiv ?x ?y)      => change (SRpair_equiv x y)     ; unfold SRpair_equiv     ; simpl
  | E : (@equiv _ SRpair_equiv ?x ?y) |- _ => change (SRpair_equiv x y) in E; unfold SRpair_equiv in E; simpl in E
  |  |- (@uneq _ SRpair_uneq ?x ?y)      => change (SRpair_uneq x y)     ; unfold SRpair_uneq     ; simpl
  | E : (@uneq _ SRpair_uneq ?x ?y) |- _ => change (SRpair_uneq x y) in E; unfold SRpair_uneq in E; simpl in E
  |  |- (@le _ SRpair_le ?x ?y)      => change (SRpair_le x y)     ; unfold SRpair_le     ; simpl
  | E : (@le _ SRpair_le ?x ?y) |- _ => change (SRpair_le x y) in E; unfold SRpair_le in E; simpl in E
  |  |- (@lt _ SRpair_lt ?x ?y)      => change (SRpair_lt x y)     ; unfold SRpair_lt     ; simpl
  | E : (@lt _ SRpair_lt ?x ?y) |- _ => change (SRpair_lt x y) in E; unfold SRpair_lt in E; simpl in E
  end.

Section contents.
Context `{CommutativeSemiRing A (R:=SR)} `{∀ `{z ∊ SR} , LeftCancellation (+) z SR}.

Add Ring SR : (stdlib_semiring_theory SR).

Notation R := (SRpair SR).

Section ring.
  Instance: Setoid R.
  Proof. split; unfold equiv, SRpair_equiv.
  + now intros [??][??].
  + intros [??][??][??][??] E. subsymmetry.
  + intros [a b][??][c d][??][e f][??] E1 E2.
    apply (left_cancellation (+) d SR _ _).
    subtransitivity (a+d+f). subring SR. rewrite_on SR -> E1.
    subtransitivity (c+f+b). subring SR. rewrite_on SR -> E2.
    subring SR.
  Qed.

  Ltac reduce_sig := split; [ split; split; apply _ |]; reduce.
  Ltac dispatch1 E := change E; intros [??][??]; reduce; subring SR.
  Ltac dispatch2 E := change E; intros [??][??][??][??]; reduce; subring SR.
  Ltac dispatch3 E := change E; intros [??][??][??][??][??][??]; reduce; subring SR.

  Instance: Morphism (R ⇒ R ⇒ R) (+).
  Proof. apply binary_morphism_proper_back.
    intros [a1 b1] [a2 b2] [[[??][??]]E1] [c1 d1] [c2 d2] [[[??][??]]E2]. reduce_sig.
    subtransitivity (a1+b2+(c1+d2)). subring SR. rewrite_on SR -> E1,E2. subring SR.
  Qed.

  Instance: Morphism (R ⇒ R) (-).
  Proof.
    intros [a1 b1] [a2 b2] [[[??][??]]E1]. reduce_sig.
    rewrite_on SR -> (commutativity (+) b1 a2), (commutativity (+) b2 a1). subsymmetry.
  Qed.

  Let mult_proper_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : x = y → z * x = z * y.
  Proof. destruct x as [a b], y as [c d], z as [e f].
    repeat match goal with H : _ ∊ R |- _ => destruct H as [??] end.
    intro E. reduce.
    subtransitivity (e*(a+d) + f*(c+b)). subring SR.
    subtransitivity (e*(c+b) + f*(a+d)); [| subring SR].
    now rewrite_on SR -> E.
  Qed.

  Instance: Commutative (.*.) R.
  Proof. dispatch2 (Commutative (.*.) R). Qed.

  Instance: ∀ `{x ∊ R} `{y ∊ R}, x*y ∊ R.
  Proof. intros [??][??][??][??]. split; apply _. Qed.

  Instance: Morphism (R ⇒ R ⇒ R) (.*.).
  Proof. apply binary_morphism_proper_back.
    intros x1 y1 [[??]E1] x2 y2 [[??]E2]. split. split; apply _.
    apply (subtransitivity (S:=R) _ (x1 * y2) _).
    exact (mult_proper_r _ _ _ E2).
    rewrite !(R $ commutativity (S:=R) (.*.) _ y2).
    exact (mult_proper_r _ _ _ E1).
  Qed.

  Global Instance: CommutativeRing R.
  Proof with try apply _. split. split... split. split. split...
  + dispatch3 (Associative (+) R).
  + dispatch2 (Commutative (+) R).
  + change (0 ∊ R). split...
  + dispatch1 (LeftIdentity (+) 0 R).
  + dispatch1 (LeftInverse (+) (-) 0 R).
  + split. split... split...
  - dispatch3 (Associative (.*.) R).
  - change (1 ∊ R). split...
  - dispatch1 (LeftIdentity (.*.) 1 R).
  + dispatch3 (LeftDistribute (.*.) (+) R).
  Qed.

  Instance: Morphism (SR ⇒ R) (').
  Proof. intros ?? [[??]E]. reduce_sig. now rewrite_on SR -> E. Qed.

  Global Instance: SemiRing_Morphism SR R (').
  Proof. apply (semiring_morphism_alt (') _).
  + intros x ? y ?. unfold cast, SRpair_inject. reduce. subring SR.
  + intros x ? y ?. unfold cast, SRpair_inject. reduce. subring SR.
  + subreflexivity.
  + subreflexivity.
  Qed.

  Global Instance: Injective SR R (').
  Proof. split; try apply _. intros ?????. reduce. now rewrite_on SR <- (plus_0_r x), <- (plus_0_r y). Qed.

  Lemma SRpair_splits n `{n ∊ SR} m `{m ∊ SR} : C n m = cast SR R n + - cast SR R m.
  Proof associativity (+) n 0 m.
End ring.

Section dec.
  Instance SRpair_std_uneq `{UnEq _} `{!StandardUnEq SR} : StandardUnEq R.
  Proof. intros [??][??][??][??]. unfold equiv, SRpair_equiv, uneq, SRpair_uneq.
    exact (standard_uneq _ _).
  Qed.

  Instance SRpair_dec_eq `{∀ (x y:A), Decision (x=y)} (x y : SRpairT A) : Decision (x=y).
  Proof. destruct x, y. unfold equiv, SRpair_equiv. exact (decide_rel (=) _ _). Defined.

  Instance SRpair_dec_le `{Le _} `{∀ (x y:A), Decision (x≤y)} (x y : SRpairT A) : Decision (x≤y).
  Proof. destruct x, y. unfold le, SRpair_le. exact (decide_rel (≤) _ _). Defined.

  Ltac strong_subdec_tac_aux x y :=
    destruct x as [a b], y as [c d]; unfold equiv, le, SRpair_equiv, SRpair_le;
    repeat match goal with H : _ ∊ R |- _ => destruct H end; simpl in *;
    pose proof (_ : a + d ∊ SR); pose proof (_ : c + b ∊ SR); auto.

  Ltac strong_subdec_tac := match goal with
    | |-   ?Rel ?x ?y =>  strong_subdec_tac_aux x y
    | |- ¬ ?Rel ?x ?y =>  strong_subdec_tac_aux x y
  end.

  Program Instance SRpair_strong_subdec_eq `{!StrongSubDecision SR SR (=)} : StrongSubDecision R R (=)
    := λ x y, match decide_sub_strong (=) (pos x + neg y) (pos y + neg x) with
       | left _ => left _
       | right _ => right _
       end.
  Next Obligation. strong_subdec_tac. Qed.
  Next Obligation. strong_subdec_tac. Qed.

  Program Instance SRpair_strong_subdec_le `{Le _} `{!StrongSubDecision SR SR (≤)} : StrongSubDecision R R (≤)
    := λ x y, match decide_sub_strong (≤) (pos x + neg y) (pos y + neg x) with
       | left _ => left _
       | right _ => right _
       end.
  Next Obligation. strong_subdec_tac. Qed.
  Next Obligation. strong_subdec_tac. Qed.

  Instance SRpair_subdec_eq `{!SubDecision SR SR (=)}: SubDecision R R (=).
  Proof. intros [??][??][??][??]. unfold equiv, SRpair_equiv.
    exact (decide_sub (=) _ _).
  Defined.

  Instance SRpair_subdec_le `{Le _} `{!SubDecision SR SR (≤)}: SubDecision R R (≤).
  Proof. intros [??][??][??][??]. unfold le, SRpair_le.
    exact (decide_sub (≤) _ _).
  Defined.

End dec.

Section with_semiring_order.
  Context `{Le _} `{!SemiRingOrder SR}.

  Instance: Proper ((R,=) ==> (R,=) ==> impl) (≤).
  Proof.
    intros [xp1 xn1] [yp1 yn1] [[[??][??]]E1] [xp2 xn2] [yp2 yn2] [[[??][??]]E2] E. reduce.
    apply (order_reflecting (+ (xp2 + xn1)) _ _).
    assert (yp1 + yn2 + (xp2 + xn1) = (yp2 + yn1) + (xp1 + xn2)) as E'.
      subtransitivity ((xp1 + yn1) + (yp2 + xn2)). rewrite_on SR -> E1, <- E2. subring SR. subring SR.
    rewrite_on SR -> E'. exact (order_preserving _ _ _ E).
  Qed.

  Instance: SubTransitive R (≤).
  Proof.
    intros [xp xn][??] [yp yn][??] [zp zn][??] E1 E2. reduce.
    apply (order_reflecting (+ (yn + yp)) _ _).
    mc_replace (xp + zn + (yn + yp)) with (xp + yn + (yp + zn)) on SR by subring SR.
    mc_replace (zp + xn + (yn + yp)) with (yp + xn + (zp + yn)) on SR by subring SR.
    exact (plus_le_compat _ _ _ _ E1 E2).
  Qed.

  Instance: PartialOrder R.
  Proof. split; try apply _.
  + intros [??][??]. now reduce.
  + intros [??][??][??][??] ??. reduce. now apply (subantisymmetry (≤) _ _).
  Qed.

  Global Instance: OrderEmbedding SR R (').
  Proof. split; (split; [split;apply _ |]); intros x ? y ? E; reduce.
    now rewrite !(SR $ plus_0_r _).
    now rewrite !(SR $ plus_0_r _) in E.
  Qed.

  Instance: ∀ `{z ∊ R}, OrderPreserving R R (z +).
  Proof. split. split; apply _.
    destruct z as [zp zn]. match goal with H : _ ∊ R |- _ => destruct H as [??] end.
    intros [xp xn][??] [yp yn][??] E. reduce.
    mc_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) on SR by subring SR.
    mc_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) on SR by subring SR.
    now apply (order_preserving _ _ _).
  Qed.

  Instance: Closed (R⁺ ⇀ R⁺ ⇀ R⁺) (.*.).
  Proof. intros x [elx E1] y [ely E2]. split. apply _. unfold PropHolds in *.
    destruct x as [xp xn], y as [yp yn], elx as [??], ely as [??]. reduce.
    rewrite (SR $ plus_0_l _), (SR $ plus_0_r _) in E1.
    rewrite (SR $ plus_0_l _), (SR $ plus_0_r _) in E2.
    destruct (decompose_le E1) as [a [? Ea]], (decompose_le E2) as [b [? Eb]].
    rewrite_on SR -> Ea,Eb. apply (compose_le _ _ (a*b)). subring SR.
  Qed.

  Global Instance: SemiRingOrder R := from_ring_order _ _.
End with_semiring_order.

Section with_strict_semiring_order.
  Context `{Lt _} `{!StrictSemiRingOrder SR}.

  Instance: Proper ((R,=) ==> (R,=) ==> impl) (<).
  Proof.
    intros [xp1 xn1] [yp1 yn1] [[[??][??]]E1] [xp2 xn2] [yp2 yn2] [[[??][??]]E2] E. reduce.
    apply (strictly_order_reflecting (+ (xp2 + xn1)) _ _).
    assert (yp1 + yn2 + (xp2 + xn1) = (yp2 + yn1) + (xp1 + xn2)) as E'.
      subtransitivity ((xp1 + yn1) + (yp2 + xn2)). rewrite_on SR -> E1, <- E2. subring SR. subring SR.
    rewrite_on SR -> E'. exact (strictly_order_preserving _ _ _ E).
  Qed.

  Instance: SubTransitive R (<).
  Proof.
    intros [xp xn][??] [yp yn][??] [zp zn][??] E1 E2. reduce.
    apply (strictly_order_reflecting (+ (yn + yp)) _ _).
    mc_replace (xp + zn + (yn + yp)) with (xp + yn + (yp + zn)) on SR by subring SR.
    mc_replace (zp + xn + (yn + yp)) with (yp + xn + (zp + yn)) on SR by subring SR.
    exact (plus_lt_compat _ _ _ _ E1 E2).
  Qed.

  Instance: StrictSetoidOrder R.
  Proof. split; try apply _. intros [??][??] E. reduce. exact (subirreflexivity (<) _ E). Qed.

  Instance: ∀ `{z ∊ R}, StrictlyOrderPreserving R R (z +).
  Proof. split. split; apply _.
    destruct z as [zp zn]. match goal with H : _ ∊ R |- _ => destruct H as [??] end.
    intros [xp xn][??] [yp yn][??] E. reduce.
    mc_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) on SR by subring SR.
    mc_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) on SR by subring SR.
    now apply (strictly_order_preserving _ _ _).
  Qed.

  Instance: Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.).
  Proof. intros x [elx E1] y [ely E2]. split. apply _. unfold PropHolds in *.
    destruct x as [xp xn], y as [yp yn], elx as [??], ely as [??]. reduce.
    rewrite (SR $ plus_0_l _), (SR $ plus_0_r _) in E1.
    rewrite (SR $ plus_0_l _), (SR $ plus_0_r _) in E2.
    destruct (decompose_lt E1) as [a [? Ea]], (decompose_lt E2) as [b [? Eb]].
    rewrite_on SR -> Ea,Eb. apply (compose_lt _ _ (a*b)). subring SR.
  Qed.

  Global Instance: StrictSemiRingOrder R := from_strict_ring_order _ _.
End with_strict_semiring_order.

Section with_full_pseudo_semiring_order.
  Context `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder SR}.

  Instance: StrongSetoid SR := pseudo_order_setoid.

  Instance: StrongSetoid R.
  Proof. split. split.
  + intros [??][??] E. reduce. exact (subirreflexivity (≠) _ E).
  + intros [??][??][??][??] ?. reduce. subsymmetry.
  + intros [xp xn][??] [yp yn][??] E [zp zn][??]. reduce.
    apply (strong_left_cancellation (+) zn SR _ _) in E.
    destruct (subcotransitivity E (zp+xn+yn)); [left|right]; reduce.
    apply (strong_extensionality (+ yn)).
      now mc_replace (xp + zn + yn) with (zn + (xp + yn)) on SR by subring SR.
    apply (strong_extensionality (+ xn)).
      mc_replace (zp + yn + xn) with (zp + xn + yn) on SR by subring SR.
      now mc_replace (yp + zn + xn) with (zn + (yp + xn)) on SR by subring SR.
  + intros [??][??][??][??]. rapply tight_apart.
  Qed.

  Instance: FullPseudoOrder R.
  Proof. split. split. apply _.
  + intros [??][??][??][??] [E1 E2]. reduce. exact (pseudo_order_antisym _ _ (conj E1 E2)).
  + intros [xp xn][??] [yp yn][??] E [zp zn][??]. reduce.
    apply (strictly_order_preserving (zn +) _ _) in E.
    destruct (subcotransitivity E (zp+xn+yn)); [left|right]; reduce.
    apply (strictly_order_reflecting (+ yn) _ _).
      now mc_replace (xp + zn + yn) with (zn + (xp + yn)) on SR by subring SR.
    apply (strictly_order_reflecting (+ xn) _ _).
      mc_replace (zp + yn + xn) with (zp + xn + yn) on SR by subring SR.
      now mc_replace (yp + zn + xn) with (zn + (yp + xn)) on SR by subring SR.
  + intros [??][??][??][??]. rapply apart_iff_total_lt.
  + intros [??][??][??][??]. rapply le_iff_not_lt_flip.
  Qed.

  Instance: ∀ `{z ∊ R}, Strong_Morphism R R (z *.).
  Proof. intros z zel.
    split. apply _. rewrite strong_ext_equiv_1.
    destruct z as [zp zn], zel as [??]. intros [xp xn][??] [yp yn][??] E1. reduce.
    assert (zp * (xp + yn) + zn * (yp + xn) ≠ zp * (yp + xn) + zn * (xp + yn)) as E.
      mc_replace (zp * (xp + yn) + zn * (yp + xn)) with (zp * xp + zn * xn + (zp * yn + zn * yp)) on SR by subring SR.
      mc_replace (zp * (yp + xn) + zn * (xp + yn)) with (zp * yp + zn * yn + (zp * xn + zn * xp)) on SR by subring SR.
      assumption.
    destruct (strong_binary_extensionality (+) E).
    now apply (strong_extensionality (zp *.)).
    subsymmetry. now apply (strong_extensionality (zn *.)).
  Qed.

  Instance: Strong_Binary_Morphism R R R (.*.) := strong_binary_morphism_commutative _ _ _.

  Global Instance: FullPseudoSemiRingOrder R := from_full_pseudo_ring_order _ _ _.
End with_full_pseudo_semiring_order.
End contents.

Hint Extern 2 (StandardUnEq (SRpair _)) => eapply @SRpair_std_uneq : typeclass_instances.
Hint Extern 2 (Decision (@equiv _ SRpair_equiv _ _)) => eapply @SRpair_dec_eq : typeclass_instances.
Hint Extern 2 (Decision (@le _ SRpair_le _ _)) => eapply @SRpair_dec_le : typeclass_instances.
Hint Extern 2 (StrongSubDecision (SRpair _) (SRpair _) (=)) => eapply @SRpair_strong_subdec_eq : typeclass_instances.
Hint Extern 2 (StrongSubDecision (SRpair _) (SRpair _) (≤)) => eapply @SRpair_strong_subdec_le : typeclass_instances.
Hint Extern 2 (SubDecision (SRpair _) (SRpair _) (=)) => eapply @SRpair_subdec_eq : typeclass_instances.
Hint Extern 2 (SubDecision (SRpair _) (SRpair _) (≤)) => eapply @SRpair_subdec_le : typeclass_instances.

Typeclasses Opaque SRpair_equiv.
Typeclasses Opaque SRpair_le.
