Require Import Ring
  abstract_algebra interfaces.orders
  interfaces.rationals interfaces.affine_extension the_ae_rationals
  interfaces.archimedean_fields interfaces.reals
  interfaces.modules interfaces.complex_numbers
  theory.strong_setoids theory.jections theory.fields theory.rationals theory.reals
  theory.subrings
  orders.rings orders.fields
  theory.modules theory.associative_algebras
  stdlib_ring misc.quote.

Local Open Scope grp_scope. (* notation for inverse *)

Inductive ComplexPairT (A:Type) := cp { re : A ; im : A }.
Arguments cp {A} _ _.
Arguments re {A} _.
Arguments im {A} _.
Definition ComplexPair `(R:set) : set := λ z, re z ∊ R ∧ im z ∊ R .
Definition ComplexPairReals `(R:set) `{Equiv R} `{Zero R} : set := ComplexPair R ⊓ (λ z, im z = 0).

Hint Extern 2 (ComplexReals (ComplexPair ?R)) => eexact (ComplexPairReals R) : typeclass_instances.

Infix "[+i*]" := cp (at level 60, no associativity).

Lemma re_el `(R:set) z `{z ∊ ComplexPair R} : re z ∊ R . Proof. firstorder. Qed.
Lemma im_el `(R:set) z `{z ∊ ComplexPair R} : im z ∊ R . Proof. firstorder. Qed.

Hint Extern 10 (@set (ComplexPairT _)) => eapply @ComplexPair : typeclass_instances.
Hint Extern 5 (re _ ∊ _) => eapply @re_el : typeclass_instances.
Hint Extern 5 (im _ ∊ _) => eapply @im_el : typeclass_instances.

Section ops.
  Context `{Reals A (R:=R)}.

  Definition cp_equiv : Equiv (ComplexPairT A) := λ z w, re z = re w ∧ im z = im w .
  Definition cp_uneq  : UnEq  (ComplexPairT A) := λ z w, re z ≠ re w ∨ im z ≠ im w .
  Definition cp_le    : Le    (ComplexPairT A) := λ z w, re z ≤ re w .
  Definition cp_lt    : Lt    (ComplexPairT A) := λ z w, re z < re w .

  Instance cp_inject : Cast R (ComplexPair R) := λ x, x [+i*] 0.

  Definition cp_zero   : Zero   (ComplexPairT A) := 0 [+i*] 0.
  Definition cp_one    : One    (ComplexPairT A) := 1 [+i*] 0.
  Definition cp_unit: ImaginaryUnit (ComplexPairT A) := 0 [+i*] 1.
  Instance   cp_plus   : Plus   (ComplexPairT A) := λ z w, re z + re w [+i*] im z + im w.
  Definition cp_mult   : Mult   (ComplexPairT A) := λ z w, re z * re w - im z * im w
                                                     [+i*] re z * im w + im z * re w.
  Instance   cp_negate : Negate (ComplexPairT A) := λ z, - re z [+i*] - im z.
  Definition cp_mag_sqr z := re z * re z + im z * im z .
  Definition cp_inv    : Inv    (ComplexPairT A) := λ z,
    re z / cp_mag_sqr z [+i*] - im z / cp_mag_sqr z .

  Definition cp_dot    : Dot   A (ComplexPairT A) := λ r z, r * re z [+i*] r * im z.
End ops.

Hint Extern 2 (Equiv   (ComplexPairT _ )) => eapply @cp_equiv  : typeclass_instances.
Hint Extern 2 (UnEq    (ComplexPairT _ )) => eapply @cp_uneq   : typeclass_instances.
Hint Extern 2 (Le      (ComplexPairT _ )) => eapply @cp_le     : typeclass_instances.
Hint Extern 2 (Lt      (ComplexPairT _ )) => eapply @cp_lt     : typeclass_instances.
Hint Extern 2 (Cast ?R (ComplexPair ?R)) => eapply @cp_inject : typeclass_instances.
Hint Extern 2 (Zero    (ComplexPairT _ )) => eapply @cp_zero   : typeclass_instances.
Hint Extern 2 (One     (ComplexPairT _ )) => eapply @cp_one    : typeclass_instances.
Hint Extern 2 (Plus    (ComplexPairT _ )) => eapply @cp_plus   : typeclass_instances.
Hint Extern 2 (Mult    (ComplexPairT _ )) => eapply @cp_mult   : typeclass_instances.
Hint Extern 2 (Negate  (ComplexPairT _ )) => eapply @cp_negate : typeclass_instances.
Hint Extern 2 (Inv     (ComplexPairT _ )) => eapply @cp_inv    : typeclass_instances.
Hint Extern 2 (ImaginaryUnit (ComplexPairT _ )) => eapply @cp_unit : typeclass_instances.

Hint Extern 2 (Equiv   (elt_type (ComplexPair _ ))) => eapply @cp_equiv  : typeclass_instances.
Hint Extern 2 (UnEq    (elt_type (ComplexPair _ ))) => eapply @cp_uneq   : typeclass_instances.
Hint Extern 2 (Le      (elt_type (ComplexPair _ ))) => eapply @cp_le     : typeclass_instances.
Hint Extern 2 (Lt      (elt_type (ComplexPair _ ))) => eapply @cp_lt     : typeclass_instances.
Hint Extern 2 (Zero    (elt_type (ComplexPair _ ))) => eapply @cp_zero   : typeclass_instances.
Hint Extern 2 (One     (elt_type (ComplexPair _ ))) => eapply @cp_one    : typeclass_instances.
Hint Extern 2 (Plus    (elt_type (ComplexPair _ ))) => eapply @cp_plus   : typeclass_instances.
Hint Extern 2 (Mult    (elt_type (ComplexPair _ ))) => eapply @cp_mult   : typeclass_instances.
Hint Extern 2 (Negate  (elt_type (ComplexPair _ ))) => eapply @cp_negate : typeclass_instances.
Hint Extern 2 (Inv     (elt_type (ComplexPair _ ))) => eapply @cp_inv    : typeclass_instances.
Hint Extern 2 (ImaginaryUnit (elt_type (ComplexPair _ ))) => eapply @cp_unit : typeclass_instances.

Hint Extern 2 (Equiv   (elt_type (ComplexPairReals _ ))) => eapply @cp_equiv  : typeclass_instances.
Hint Extern 2 (UnEq    (elt_type (ComplexPairReals _ ))) => eapply @cp_uneq   : typeclass_instances.
Hint Extern 2 (Le      (elt_type (ComplexPairReals _ ))) => eapply @cp_le     : typeclass_instances.
Hint Extern 2 (Lt      (elt_type (ComplexPairReals _ ))) => eapply @cp_lt     : typeclass_instances.
Hint Extern 2 (Zero    (elt_type (ComplexPairReals _ ))) => eapply @cp_zero   : typeclass_instances.
Hint Extern 2 (One     (elt_type (ComplexPairReals _ ))) => eapply @cp_one    : typeclass_instances.
Hint Extern 2 (Plus    (elt_type (ComplexPairReals _ ))) => eapply @cp_plus   : typeclass_instances.
Hint Extern 2 (Mult    (elt_type (ComplexPairReals _ ))) => eapply @cp_mult   : typeclass_instances.
Hint Extern 2 (Negate  (elt_type (ComplexPairReals _ ))) => eapply @cp_negate : typeclass_instances.
Hint Extern 2 (Inv     (elt_type (ComplexPairReals _ ))) => eapply @cp_inv    : typeclass_instances.

Hint Extern 2 (Dot ?A (ComplexPairT ?A)) => eapply @cp_dot : typeclass_instances.
Hint Extern 2 (Dot _ (elt_type (ComplexPair _))) => eapply @cp_dot : typeclass_instances.

Section contents.
  Context `{Reals (R:=R)}.
  Add Ring R : (stdlib_ring_theory R).

  Notation C := (ComplexPair R).
  Notation CR := (ComplexPairReals R).

  Instance: StrongSetoid C.
  Proof. split; [split|]; unfold uneq, cp_uneq.
  + intros [a b][??][E|E]; simpl in *; revert E; exact (irreflexivity (≠) _).
  + intros [a b][??][c d][??][E|E]; simpl in *; [left|right]; subsymmetry.
  + intros [a b][??][c d][??][E|E][x y][??]; simpl in *;
      [destruct (cotransitivity E x)|destruct (cotransitivity E y)]; tauto.
  + intros [a b][??][c d][??]. change ( ¬(a ≠ c ∨ b ≠ d) ↔ a = c ∧ b = d).
    rewrite <-2!(tight_apart _ _). tauto.
  Qed.

  Instance: Strong_Binary_Morphism C C C (+).
  Proof. split.
  + intros [a b][??][c d][??]; split; simpl in *; apply _.
  + rewrite strong_ext_equiv_2.
    intros [a1 b1][??][a2 b2][??][c1 d1][??][c2 d2][??] E.
    unfold plus, cp_plus, uneq, cp_uneq in *. simpl in *.
    destruct E as [E|E]; destruct (strong_binary_extensionality (+) E); tauto.
  Qed.

  Instance: Strong_Binary_Morphism C C C (.*.).
  Proof. split.
  + intros [a b][??][c d][??]; split; simpl in *; apply _.
  + rewrite strong_ext_equiv_2.
    intros [a1 b1][??][a2 b2][??][c1 d1][??][c2 d2][??] E.
    unfold mult, cp_mult, uneq, cp_uneq in *. simpl in *.
    destruct E as [E|E]; destruct (strong_binary_extensionality (+) E) as [E'|E'];
    try (destruct (strong_binary_extensionality (.*.) E'); tauto).
    pose proof (strong_extensionality (-) E') as E''.
    destruct (strong_binary_extensionality (.*.) E''); tauto.
  Qed.

  Local Ltac reduce := unfold equiv, cp_equiv; simpl in *.
  Local Ltac reduce_sig := split; [ split; split; simpl; apply _ | reduce ].
  Local Ltac dispatch1 E := change E; intros [a b] [??]; reduce; split; setring R.
  Local Ltac dispatch2 E := change E; intros [a b] [??] [c d] [??]; reduce; split; setring R.
  Local Ltac dispatch3 E := change E; intros [a b] [??] [c d] [??] [e f] [??]; reduce; split; setring R.

  Instance: Morphism (C ⇒ C) (-).
  Proof.
    intros [a1 b1] [a2 b2] [[[??][??]][E1 E2]]. reduce_sig.
    split. now rewrite (_ $ E1). now rewrite (_ $ E2).
  Qed.

  Instance: CommutativeRing C.
  Proof. split. split; try apply _. split. split. split; try apply _.
  + dispatch3 (Associative (+) C).
  + dispatch2 (Commutative (+) C).
  + change (0 ∊ C). split; simpl; apply _.
  + dispatch1 (LeftIdentity (+) 0 C).
  + dispatch1 (LeftInverse (+) (-) 0 C).
  + split. split. split; try apply _.
  - dispatch3 (Associative (.*.) C).
  - dispatch2 (Commutative (.*.) C).
  - change (1 ∊ C). split; simpl; apply _.
  - dispatch1 (LeftIdentity (.*.) 1 C).
  + dispatch3 (LeftDistribute (.*.) (+) C).
  Qed.

  Instance: ∀ z `{z ∊ C ₀}, re z * re z + im z * im z ∊ R₊ .
  Proof.
    intros [??][[??][?|?]]; red; apply (sum_of_squares_pos_iff _ _); [left|right]; now split.
  Qed.

  Instance: ∀ z `{z ∊ C ₀}, z⁻¹ ∊ C ₀ .
  Proof. intros z ?. destruct (_ : z ∊ C) as [??].
    pose proof (_ : re z * re z + im z * im z ∊ R₊ ).
    unfold inv, cp_inv, cp_mag_sqr. split. split; simpl; apply _.
    destruct (_ : z ∊ C ₀) as [_ [?|?]]; [left|right]; simpl.
      assert (re z ∊ R ₀). now split. now destruct ( _ : re z / (re z * re z + im z * im z) ∊ R ₀ ).
      assert (im z ∊ R ₀). now split. now destruct ( _ :-im z / (re z * re z + im z * im z) ∊ R ₀ ).
  Qed.      

  Instance: Field C.
  Proof. split; try apply _. split; try apply _.
  + split. apply _. red. left. now destruct (_ : 1 ∊ R ₀).
  + intros [a b][c d] [[el0 el1] [E1 E2]]. red_sig.
    pose proof _ : re (a[+i*]b) * re (a[+i*]b) + im (a[+i*]b) * im (a[+i*]b) ∊ R₊ .
    pose proof _ : re (c[+i*]d) * re (c[+i*]d) + im (c[+i*]d) * im (c[+i*]d) ∊ R₊ .
    destruct el0 as [[??]_], el1 as [[??]_].
    split; simpl in *; unfold cp_mag_sqr; simpl;
    apply (mult_inv_cancel_both _ _ _ _);
    rewrite (_ $ E1), (_ $ E2); setring R.
  + intros [a b] el.
    pose proof _ : re (a[+i*]b) * re (a[+i*]b) + im (a[+i*]b) * im (a[+i*]b) ∊ R₊ .
    destruct el as [[??]_].
    split; simpl in *; unfold cp_mag_sqr; simpl.
    2: setring R.
    subtransitivity ((a*a + b*b)/(a*a+b*b)). setring R. exact (field_inv_r _).
  Qed.

  Instance: ComplexRing C.
  Proof. split. apply _.
  + split; simpl; apply _.
  + split; simpl; setring R.
  Qed.

  Global Instance: Strong_Morphism R C (').
  Proof. split.
  + intros x ?. split; simpl; apply _.
  + intros x ? y ? [E|E]. exact E. simpl in E. now destruct (irreflexivity (≠) 0).
  Qed.

  Global Instance: SemiRing_Morphism R C (').
  Proof. apply (ring_morphism_alt (cast R C)). apply _.
  + intros x ? y ?. unfold cast, cp_inject. reduce. split; setring R.
  + intros x ? y ?. unfold cast, cp_inject. reduce. split; setring R.
  + subreflexivity.
  Qed.

  Global Instance: StrongInjective R C (').
  Proof. apply strong_injective_preserves_0.
    intros x ?. split.  apply _. left. simpl. now destruct (_ : x ∊ R ₀).
  Qed.

  Global Instance: Strong_Morphism C R re.
  Proof. split. now intros [??][??]. intros [a b][??][c d][??]?. now left. Qed.

  Global Instance: Strong_Morphism C R im.
  Proof. split. now intros [??][??]. intros [a b][??][c d][??]?. now right. Qed.

  Global Instance: UnitalCommutativeAlgebra R C.
  Proof. apply (unital_comm_alg_from_ring (cast R C)).
  + unfold dot, cp_dot. apply (binary_morphism_proper_back).
    intros r s [[??]E1] [a b] [c d] [[[??][??]][E2 E3]]. simpl in *.
    split. split; split; simpl; apply _. split; simpl.
    now rewrite (_ $ E1), (_ $ E2).
    now rewrite (_ $ E1), (_ $ E3).
  + intros r ? [a b][??]. split; simpl in *; setring R.
  Qed.

  Global Instance: Module_Morphism R C R re.
  Proof. apply (module_morphism_alt _ _).
  + intros [a b][??][c d][??]. now simpl in *.
  + intros r ? [a b][??]. now simpl in *.
  Qed.

  Global Instance: Module_Morphism R C R im.
  Proof. apply (module_morphism_alt _ _).
  + intros [a b][??][c d][??]. now simpl in *.
  + intros r ? [a b][??]. now simpl in *.
  Qed.

  Lemma CR_is_image : CR = (cast R C)⁺¹(R).
  Proof. intros [a b]. split.
  + intros [[??] E]. red in E. simpl in *. split. now split. exists_sub a.
    split; simpl. easy. subsymmetry.
  + intros [[??][x[?[??]]]]. simpl in *. split. now split. red. simpl. subsymmetry.
  Qed.

  Instance: CR ⊆ C.    Proof. rewrite CR_is_image. apply _. Qed.
  Instance: Field CR.  Proof. rewrite CR_is_image. apply _. Qed.

  Let to_CR := (cast R C : R ⇀ CR).

  Instance : Strong_Morphism R CR to_CR.
  Proof. split. intros x ?. split. exact (_ : ' x ∊ C). now change (0=0).
    intros x ? y ?. exact (strong_extensionality (cast R C)).
  Qed.

  Instance : StrongInjective R CR to_CR.
  Proof. split. 2: apply _. exact (strong_injective (cast R C)). Qed.

  Instance : SemiRing_Morphism R CR to_CR.
  Proof. apply (ring_morphism_alt _ _).
    exact (preserves_plus (f:=cast R C)).
    exact (preserves_mult (f:=cast R C)).
    exact (preserves_1 (f:=cast R C)).
  Qed.

  Instance: Inverse to_CR := re.

  Instance: Bijective R CR to_CR.
  Proof. split. apply _. split.
  + intros [a b][c d][[[[??] Eb][[??] Ed]] [E1 E2]]. red in Eb,Ed. simpl in *.
    change ((CR,=)%signature (a[+i*]0) (c[+i*]d)).
    split. repeat (split; trivial; try apply _). simpl. apply _. red. now simpl.
    split; simpl; trivial; subsymmetry.
  + apply _.
  + change (Closed (CR ⇀ R) re).
    cut (Morphism (CR ⇒ R) re). intro. apply _.
    rewrite <-(_ : Subset (C ⇒ R) (CR ⇒ R)). apply _.
  Qed.

  Instance: SemiRing_Morphism CR R re.
  Proof _ : SemiRing_Morphism CR R (inverse to_CR) . 

  Instance: StrongInjective CR R re.
  Proof. split.
  + intros [a b][[??]Eb][c d][[??]Ed]; red in Eb, Ed. simpl in *.
    intros [E|E]. tauto. contradict E. apply (tight_apart _ _). simpl.
    subtransitivity (0:R). subsymmetry.
  + split. apply _. intros z [??] w [??]. exact (strong_extensionality re).
  Qed.

  Instance: FullPseudoSemiRingOrder CR.
  Proof. apply (projected_full_pseudo_ring_order (re : CR ⇀ R)) ; tauto. Qed.

  Instance: ArchimedeanField CR.
  Proof. split; try apply _.
    apply rationals_dense_archimedean.
    intros [a b][[??]Eb][c d][[??]Ed] E; red in Eb, Ed. do 2 red in E. simpl in *.
    destruct (archimedean_rationals_dense _ _ E) as [q[??]].
    exists_sub q.
    pose proof ( rationals_to_field_unique the_ae_rationals (F:=CR)
      (to_CR ∘ rationals_to_field the_ae_rationals R) _ _ (_ : Proper (the_ae_rationals,=) q) ) as E2.
    split; do 2 red; rewrite <-E2; simpl; intuition.
  Qed.

  Instance: StrictOrderEmbedding R CR to_CR .
  Proof. split; (  split; [ split; apply _ | tauto ] ). Qed.

  Instance cp_to_reals : ToReals CR := image_to_reals to_CR.
  Instance : Reals CR := image_is_reals to_CR.

  Instance cp_to_ring : ComplexToRing C :=
    λ _ S _ _ _ f z, f (to_CR (re z)) + i * f (to_CR (im z)).

  Section another_ring.
    Context `{S:set} `{ComplexRing _ (C:=S)} (f:CR ⇀ S) `{!SemiRing_Morphism CR S f}.
    Add Ring S : (stdlib_ring_theory S).

    Notation g := (complex_to_ring C f).

    Instance: Morphism (C ⇒ S) g.
    Proof. intros [a b][c d][[[??][??]] [E1 E2]]. simpl in *.
      unfold complex_to_ring, cp_to_ring. simpl. red_sig.
      now rewrite (R $ E1), (R $ E2).
    Qed.

    Instance: SemiRing_Morphism C S g.
    Proof. apply (ring_morphism_alt _ _); unfold complex_to_ring, cp_to_ring.
    + intros [a b][??][c d][??]. simpl in *.
      setoid_rewrite (_ $ preserves_plus (f:=f ∘ to_CR) a c).
      setoid_rewrite (_ $ preserves_plus (f:=f ∘ to_CR) b d).
      unfold compose. setring S.
    + intros [a b][??][c d][??]. simpl in *.
      set (a' := f (to_CR a) ). assert (a' ∊ S). unfold a'. apply _.
      set (b' := f (to_CR b) ). assert (b' ∊ S). unfold b'. apply _.
      set (c' := f (to_CR c) ). assert (c' ∊ S). unfold c'. apply _.
      set (d' := f (to_CR d) ). assert (d' ∊ S). unfold d'. apply _.
      assert ( (f ∘ to_CR) (a * c - b * d) = a'*c'-b'*d' ) as E1.
        preserves_simplify (f ∘ to_CR). unfold compose. subreflexivity.
      assert ( (f ∘ to_CR) (a * d + b * c) = a'*d'+b'*c' ) as E2.
        preserves_simplify (f ∘ to_CR). unfold compose. subreflexivity.
      unfold compose in E1,E2. rewrite (S $ E1), (S $ E2). clear E1 E2.
      mc_replace ((a' + i * b') * (c' + i * d')) with
        ( a' * c' - b' * d' + i * (a' * d' + b' * c') + (i*i+1)*(b'*d') ) on S by setring S.
      rewrite (_ $ imaginary_unit_def). setring S.
    + simpl in *.
      setoid_rewrite (_ $ preserves_0 (f:=f ∘ to_CR)).
      rewrite (_ $ mult_0_r _), (_ $ plus_0_r _).
      exact (preserves_1 (f:=f ∘ to_CR)).
    Qed.

    Instance cp_to_ring_mor: ComplexRing_Morphism C S g.
    Proof. split; try apply _.  unfold complex_to_ring, cp_to_ring. simpl in *.
      setoid_rewrite (_ $ preserves_0 (f:=f ∘ to_CR)).
      setoid_rewrite (_ $ preserves_1 (f:=f ∘ to_CR)).
      setring S.
    Qed.

    Hint Extern 5 (_ ∊ C) => apply (_ : CR ⊆ C) : typeclass_instances.

    Lemma cp_to_ring_extends: f = (g:CR ⇀ S).
    Proof. intros x y E. unfold_sigs. red_sig. rewrite <-(_ $ E). clear dependent y.
      unfold complex_to_ring, cp_to_ring.
      rewrite (CR $ (surjective_applied to_CR x : to_CR (re x) = x)).
      assert (im x = 0) as E by now destruct el. rewrite (_ $ E).
      setoid_rewrite (_ $ preserves_0 (f:=f ∘ to_CR)).
      setring S.
    Qed.

    Context (h : C ⇀ S) `{!ComplexRing_Morphism C S h}.

    Lemma cp_to_ring_unique: f = (h : CR ⇀ S) → h = g .
    Proof. intro Eh. intros z w E. unfold_sigs. red_sig. rewrite <-(C $ E). clear dependent w.
      assert (z = to_CR (re z) + i * to_CR (im z)) as E.
        destruct (_ : z ∊ C) as [??], z as [a b]. split; simpl in *; setring R.
      rewrite (C $ E) at 1.
      rewrite (_ $ preserves_plus _ _), (_ $ preserves_mult _ _), (_ $ preserves_i).
      rewrite <-(Eh _ _ (_ : Proper (CR,=) (to_CR (re z)))).
      rewrite <-(Eh _ _ (_ : Proper (CR,=) (to_CR (im z)))).
      subreflexivity.
    Qed.
  End another_ring.
 
  Instance cp_complex_numbers: ComplexNumbers C.
  Proof. split; try apply _. intros ? S ???????? f ?. split.
    * apply cp_to_ring_mor; trivial.
    * apply cp_to_ring_extends; trivial.
    * apply cp_to_ring_unique; trivial.
  Qed.

End contents.

Hint Extern 2 (ToReals (complex_reals (ComplexPair ?R))) => eexact (cp_to_reals (R:=R)) : typeclass_instances.
Hint Extern 2 (ComplexToRing (ComplexPair ?R)) => eexact (cp_to_ring (R:=R)) : typeclass_instances.
Hint Extern 2 (ComplexNumbers (ComplexPair ?R)) => eexact (cp_complex_numbers (R:=R)) : typeclass_instances.


(*
  Section another_ring.
    Context `{CommutativeRing (R:=P)}
      `{!ToPolynomialRing CR P} `{!PolynomialVar P} `{!PolynomialEval CR P}
      `{!Dot CR P} `{!Polynomial_Ring CR P}.

    Add Ring P : (stdlib_ring_theory P).

    Notation x := polynomial_var.
    Notation φ := (to_polynomial_ring (R:=CR) P).
    Notation π := (polynomial_eval (R:=CR) (P:=P) (id:CR⇀C) i).

    Instance: x ∊ P := poly_ring_var_el (R:=CR).
    Instance: Polynomial_Evaluable (id:CR⇀C) i := _.
    Instance: SemiRing_Morphism P C π := _.

    Context `{S:set} `{Ring _ (R:=S)} (f:P ⇀ S) `{!SemiRing_Morphism P S f} .
    Context (Ef : f (x*x+1) = 0 ) .

    Notation g := (complex_to_ring CR C P f).

    Instance: Morphism (C ⇒ S) g.
    Proof. intros [a b][c d][[[??][??]] [E1 E2]]. simpl in *.
      unfold complex_to_ring, cp_to_ring. simpl. red_sig.
      now rewrite (R $ E1), (R $ E2).
    Qed.

    Instance cp_to_ring_mor: SemiRing_Morphism C S g.
    Proof. apply (ring_morphism_alt _ _).
    + intros [a b][??][c d][??].
      unfold complex_to_ring, cp_to_ring. simpl in *.
      cut ( φ (to_CR (a + c)) + x * φ (to_CR (b + d))
           = (φ (to_CR a) + x * φ (to_CR b)) + (φ (to_CR c) + x * φ (to_CR d)) ).
        intro E. rewrite (P $ E). exact (preserves_plus _ _).
      setoid_rewrite (_ $ preserves_plus (f:=φ ∘ to_CR) a c).
      setoid_rewrite (_ $ preserves_plus (f:=φ ∘ to_CR) b d).
      unfold compose. setring P.
    + intros [a b][??][c d][??].
      unfold complex_to_ring, cp_to_ring. simpl in *.
      set (a' := φ (to_CR a) ). assert (a' ∊ P). unfold a'. apply _.
      set (b' := φ (to_CR b) ). assert (b' ∊ P). unfold b'. apply _.
      set (c' := φ (to_CR c) ). assert (c' ∊ P). unfold c'. apply _.
      set (d' := φ (to_CR d) ). assert (d' ∊ P). unfold d'. apply _.
      assert ( (φ ∘ to_CR) (a * c - b * d) = a'*c'-b'*d' ) as E1.
        preserves_simplify (φ ∘ to_CR). unfold compose. subreflexivity.
      assert ( (φ ∘ to_CR) (a * d + b * c) = a'*d'+b'*c' ) as E2.
        preserves_simplify (φ ∘ to_CR). unfold compose. subreflexivity.
      unfold compose in E1,E2. rewrite (P $ E1), (P $ E2). clear E1 E2.
      rewrite <-(_ $ preserves_mult _ _).
      mc_replace ((a' + x * b') * (c' + x * d')) with
        ( a' * c' - b' * d' + x * (a' * d' + b' * c') + (x*x+1)*(b'*d') ) on P by setring P.
      rewrite (_ $ preserves_plus _ ((x*x+1)*(b'*d'))).
      now rewrite (_ $ preserves_mult _ (b'*d')), (_ $ Ef), (_ $ mult_0_l _), (_ $ plus_0_r _).
    + unfold complex_to_ring, cp_to_ring. simpl in *.
      setoid_rewrite (_ $ preserves_0 (f:=φ ∘ to_CR)).
      rewrite (_ $ mult_0_r _), (_ $ plus_0_r _).
      exact (preserves_1 (f:=f ∘ φ ∘ to_CR)).
    Qed.

    Lemma cp_to_ring_factors : f = g ∘ π .
    Proof. intros q p E. unfold_sigs. red_sig. rewrite (_ $ E). clear dependent q.
      destruct (poly_div_monic (R:=CR) (P:=P) p (x*x+1) _ x_sqr_plus_1_monic)
        as [q[elq[r[elr[E Er]]]]].
      eq_replace (2-1:ZA) with (1:ZA) in Er by reflexivity.
      rewrite (deg_le_linear _) in Er.
      destruct Er as [a[ela[b[elb Er]]]].
      assert ( dot a x ∊ P ). apply (modules.dot_closed (R:=CR)); apply _.
      rewrite (_ $ poly_ring_dot_def _ _) in Er.
      rewrite (_ $ Er) in E. rewrite (_ $ E). clear dependent p. clear dependent r.
      subtransitivity (f (φ a * x + φ b) ).
        rewrite (_ $ preserves_plus (f:=f) _ _).
        rewrite (_ $ preserves_mult (f:=f) _ _).
        now rewrite (_ $ Ef), (_ $ mult_0_r _), (_ $ plus_0_l _).
      unfold compose.
      assert (a ∊ C) by now apply (_ : Subset CR C).
      assert (b ∊ C) by now apply (_ : Subset CR C).
      assert (π (q * (x * x + 1) + (φ a * x + φ b)) = a * i + b ) as E.
        preserves_simplify (π).
        change (π q * ( π x * π x + 1) + ( π (φ a) * π x + π (φ b) ) = a*i+b).
        rewrite (C $ polynomial_eval_var (R:=CR) (P:=P) (id:CR⇀C) i).
        rewrite (C $ i_sqr_plus_1), (_ $ mult_0_r _), (_ $ plus_0_l _).
        setoid_rewrite (polynomial_eval_const (R:=CR) (P:=P) (id:CR⇀C) i _ _ (_ : Proper (CR,=) a)).
        setoid_rewrite (polynomial_eval_const (R:=CR) (P:=P) (id:CR⇀C) i _ _ (_ : Proper (CR,=) b)).
        now unfold id.
      rewrite (_ $ E). unfold complex_to_ring, cp_to_ring.
      cut (to_CR (re (a*i+b)) = b ∧ to_CR (im (a*i+b)) = a).
        intros [E1 E2]. rewrite (CR $ E1), (CR $ E2).
        rewrite (_ $ commutativity (+) (φ b) _).
        now rewrite (_ $ commutativity (.*.) x _).
      destruct a as [ar ai]. destruct ela as [[??]Eai]. red in Eai.
      destruct b as [br bi]. destruct elb as [[??]Ebi]. red in Ebi.
      simpl in *. split; split; simpl; subsymmetry.
      rewrite (_ $ Eai). setring R.
      rewrite (_ $ Ebi). setring R.
    Qed.

    Context (h : C ⇀ S) `{!SemiRing_Morphism C S h}.

    Lemma cp_to_ring_unique : f = h ∘ π → h = g.
    Proof. intros Efh z w E. unfold_sigs. red_sig. rewrite <-(_ $ E). clear dependent w.
      unfold complex_to_ring, cp_to_ring.
      set (p := φ (to_CR (re z)) + x * φ (to_CR (im z)) ).
      assert (p ∊ P). unfold p. apply _.
      rewrite (Efh _ _ (_ : Proper (P,=) p)).
      cut (π p = z). intro E. unfold compose. now rewrite (_ $ E).
      subst p. preserves_simplify (π).
      change (π (φ (to_CR (re z))) + π x * π (φ (to_CR (im z))) = z ).
      rewrite (C $ polynomial_eval_var (R:=CR) (P:=P) (id:CR⇀C) i).
      setoid_rewrite (polynomial_eval_const (R:=CR) (P:=P) (id:CR⇀C) i _ _ (_ : Proper (CR,=) (to_CR (re z)))).
      setoid_rewrite (polynomial_eval_const (R:=CR) (P:=P) (id:CR⇀C) i _ _ (_ : Proper (CR,=) (to_CR (im z)))).
      destruct z as [a b], el as [??]. split; simpl in *; setring R.
    Qed.

  End another_ring.      

  Instance cp_complex_numbers: ComplexNumbers CR C.
  Proof. split; try apply _.
  + split; simpl; setring R.
  + intros ??????? P ? ????? ? S ??????? f ? E. split.
    * apply cp_to_ring_mor; trivial.
    * apply cp_to_ring_factors; trivial.
    * apply cp_to_ring_unique; trivial.
  Qed.
*)
