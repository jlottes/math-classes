Require Import
  stdlib_binary_integers
  abstract_algebra interfaces.additional_operations interfaces.orders
  interfaces.modules interfaces.polynomial_rings
  interfaces.integers theory.integers orders.integers
  interfaces.naturals theory.naturals orders.naturals nonneg_integers_naturals peano_naturals
  theory.setoids theory.rings orders.rings
  orders.lattices orders.minmax lattice_ordered_rings
  theory.modules theory.associative_algebras
  stdlib_ring misc.quote
  bigops_int kronecker_delta
  theory.nonneg_int_pow.

Local Notation ZA := BinNums.Z.
Local Notation Z  := (every BinNums.Z).

Local Notation δ := kronecker_delta.

Inductive PolyT `(R:set) := mk_poly { coef : Z ⇀ R ; len : ZA }.
Arguments mk_poly {A R} _ _.
Arguments coef {A R} _ _.
Arguments len {A R} _.

Local Notation "[ p ]_ i" := (coef p i) (at level 1, format "[ p ]_ i").

Section def.
  Context `{Ae:Equiv A} {Azero:Zero A} {R:@set A}.

  Record PolySet (p : PolyT R) : Prop :=
  { polyset_len_nonneg : len p ∊ Z⁺
  ; polyset_coef_el i : [p]_i ∊ R
  ; polyset_coef_neg i `{i ∊ Z₋} : [p]_i = 0
  ; polyset_coef_after i : len p ≤ i → [p]_i = 0
  }.

  Definition Poly : set := PolySet.

  Lemma poly_len_nonneg p {el:p ∊ Poly} : len p ∊ Z⁺ .
  Proof polyset_len_nonneg p el.

  Lemma poly_coef_bigopand p {el:p ∊ Poly} : Big_Operand R (coef p).
  Proof polyset_coef_el p el.

  Instance: ∀ `{p ∊ Poly} i, [p]_i ∊ R.
  Proof polyset_coef_el.

  Lemma poly_coef_mor_1 `{!Setoid R} p {el:p ∊ Poly} : Morphism (Z ⇒ R) (coef p).
  Proof. intros ?? [_ E]. red_sig. now rewrite (to_eq E). Qed.

  Lemma poly_coef_neg     p {el:p ∊ Poly} i `{i ∊ Z₋} : [p]_i = 0.
  Proof polyset_coef_neg p el i.

  Lemma poly_coef_after   p {el:p ∊ Poly} i : len p ≤ i → [p]_i = 0.
  Proof polyset_coef_after p el i.
End def.

Arguments Poly {A Ae Azero} R _.

Hint Extern 10 (@set (PolyT ?R)) => exact (Poly R) : typeclass_instances.

Hint Extern 2 (len _ ∊ Z⁺) => eapply @poly_len_nonneg : typeclass_instances.
Hint Extern 2 (len _ ∊ Z) => apply (_ : Subset Z⁺ Z) : typeclass_instances.
Hint Extern 2 (Big_Operand _ (coef _)) => eapply @poly_coef_bigopand : typeclass_instances.
Hint Extern 2 (Morphism _ (coef _)) => eapply @poly_coef_mor_1 : typeclass_instances.

Section ops.
  Context `{Ring A (R:=R)}.

  Definition poly_equiv          : Equiv (PolyT R) := λ p q, ∀ i, [p]_i = [q]_i .
  Definition poly_uneq `{UnEq A} : UnEq  (PolyT R) := λ p q, ∃ i, [p]_i ≠ [q]_i .

  Instance poly_inject : Cast R (Poly R) := λ x, mk_poly (λ i, δ i 0 * x) 1 .

  Definition poly_monomial n := mk_poly (λ i, δ i n) (1+n) .
  Definition poly_var := poly_monomial 1.

  Definition poly_zero   : Zero   (PolyT R) := mk_poly (λ _, 0) 0.
  Definition poly_one    : One    (PolyT R) := poly_monomial 0 .
  Definition poly_negate : Negate (PolyT R) := λ p, mk_poly (λ i, -[p]_i) (len p) .
  Definition poly_plus   : Plus   (PolyT R) := λ p q, mk_poly (λ i, [p]_i + [q]_i) (len p ⊔ len q) .
  Definition poly_mult   : Mult   (PolyT R) := λ p q,
    mk_poly (λ i,  ∑_(k < 1+i) [p]_k * [q]_(i - k)) (0 ⊔ (len p + len q - 1)).
  Definition poly_dot    : Dot A (PolyT R) := λ r p, mk_poly (λ i, r*[p]_i) (len p) .
End ops.

Local Notation x := poly_var.

Hint Extern 2 (Equiv   (PolyT _ )) => eapply @poly_equiv  : typeclass_instances.
Hint Extern 2 (UnEq    (PolyT _ )) => eapply @poly_uneq   : typeclass_instances.
Hint Extern 2 (Cast ?R (Poly ?R )) => eapply @poly_inject : typeclass_instances.
Hint Extern 2 (Zero    (PolyT _ )) => eapply @poly_zero   : typeclass_instances.
Hint Extern 2 (One     (PolyT _ )) => eapply @poly_one    : typeclass_instances.
Hint Extern 2 (Plus    (PolyT _ )) => eapply @poly_plus   : typeclass_instances.
Hint Extern 2 (Mult    (PolyT _ )) => eapply @poly_mult   : typeclass_instances.
Hint Extern 2 (Dot   _ (PolyT _ )) => eapply @poly_dot    : typeclass_instances.
Hint Extern 2 (Negate  (PolyT _ )) => eapply @poly_negate : typeclass_instances.

Hint Extern 2 (Equiv   (elt_type (Poly _ ))) => eapply @poly_equiv  : typeclass_instances.
Hint Extern 2 (UnEq    (elt_type (Poly _ ))) => eapply @poly_uneq  : typeclass_instances.
Hint Extern 2 (Zero    (elt_type (Poly _ ))) => eapply @poly_zero   : typeclass_instances.
Hint Extern 2 (One     (elt_type (Poly _ ))) => eapply @poly_one    : typeclass_instances.
Hint Extern 2 (Plus    (elt_type (Poly _ ))) => eapply @poly_plus   : typeclass_instances.
Hint Extern 2 (Mult    (elt_type (Poly _ ))) => eapply @poly_mult   : typeclass_instances.
Hint Extern 2 (Dot   _ (elt_type (Poly _ ))) => eapply @poly_dot    : typeclass_instances.
Hint Extern 2 (Negate  (elt_type (Poly _ ))) => eapply @poly_negate : typeclass_instances.


Lemma poly_len_0 `{Setoid (S:=R)} `{Zero _} p `{p ∊ Poly R} : len p = 0 → p = 0 .
Proof. intros E i. destruct (nonneg_or_neg i).
  apply poly_coef_after. apply _. rewrite (to_eq E). firstorder.
  exact (poly_coef_neg _ _).
Qed.

Section ring.
  
  Context `{CommutativeRing (R:=R)}.

  Instance: Setoid (Poly R).
  Proof. red. unfold equiv, poly_equiv. split.
  + now intros ?? i.
  + intros p ? q ? E i. subsymmetry.
  + intros p ? q ? r ? E1 E2 i. subtransitivity [q]_i.
  Qed.
  
  Instance poly_strong_setoid `{UnEq A} `{!StrongSetoid R} : StrongSetoid (Poly R).
  Proof. split. split.
  + intros p ? [i ?]. now destruct (irreflexivity (≠) [p]_i).
  + intros p ? q ? [i ?]. exists i. subsymmetry.
  + intros p ? q ? [i E] r ?.
    destruct (cotransitivity E [r]_i) as [?|?]; [left|right]; now exists i.
  + intros p ? q ?. split.
    * intros E i. rewrite <-(tight_apart _ _). contradict E. now exists i.
    * intros E [i E']. contradict E'. rewrite (tight_apart _ _). exact (E i).
  Qed.

  Instance: ∀ a `{a ∊ R}, cast R (Poly R) a ∊ Poly R.
  Proof. unfold cast, poly_inject. intros x ?. split; simpl; try apply _.
  + intros i [_ E]. red in E. rewrite (_ $ kronecker_delta_lt _ _ E). exact (mult_0_l _).
  + intros i E. mc_replace (δ i 0) with 0 on R. exact (mult_0_l _).
    apply (kronecker_delta_gt _ _). apply (lt_le_trans _ 1 _); trivial. exact (lt_0_1).
  Qed.

  Instance poly_monomial_el n `{n ∊ Z⁺} : poly_monomial n ∊ Poly R.
  Proof. unfold poly_monomial. split; simpl; try apply _.
  + intros i [_ E]. red in E. apply (kronecker_delta_lt _ _).
    apply (lt_le_trans _ 0 _); firstorder.
  + intros i E. apply (kronecker_delta_gt _ _). now apply (lt_iff_S_le _ _).
  Qed.

  Instance poly_var_el : x ∊ Poly R.
  Proof poly_monomial_el 1.

  Instance: 0 ∊ Poly R.
  Proof. unfold "0", poly_zero. split; simpl. apply _. apply _. now intros. now intros. Qed.

  Instance: 1 ∊ Poly R.
  Proof poly_monomial_el 0.

  Instance: ∀ p `{p ∊ Poly R}, -p ∊ Poly R.
  Proof. intros p ?. unfold negate, poly_negate. split; simpl; try apply _.
  + intros ?? . rewrite (_ $ poly_coef_neg p _). exact negate_0.
  + intros ? E . rewrite (_ $ poly_coef_after p _ E). exact negate_0.
  Qed.

  Instance: ∀ p `{p ∊ Poly R} q `{q ∊ Poly R}, p + q ∊ Poly R.
  Proof. intros p ? q ?. unfold plus, poly_plus. split; simpl; try apply _.
  + intros ?? . rewrite 2!(_ $ poly_coef_neg _ _). exact (plus_0_r _).
  + intros i E . mc_replace [p]_i with 0 on R; [ mc_replace [q]_i with 0 on R; try exact (plus_0_r _) |];
      apply (poly_coef_after _ _); transitivity (len p ⊔ len q); trivial; lattice_order_tac.
  Qed.

  Instance: ∀ p `{p ∊ Poly R} q `{q ∊ Poly R}, p * q ∊ Poly R.
  Proof. intros p ? q ?. unfold mult, poly_mult. split; simpl; try apply _.
  + intros ? el . apply (sum_empty_le _ _ _). apply (lt_iff_S_le _ _). apply el.
  + intros i ?. apply (sum_of_zero_alt _ _). intros k ??.
    destruct (le_or_lt (len p) k) as [Ep|Ep].
      rewrite (_ $ poly_coef_after p _ Ep). exact (mult_0_l _).
    mc_replace [q]_(i-k) with 0 on R. exact (mult_0_r _).
    apply (poly_coef_after q _).
    eq_replace (len q) with (len p + len q - 1 + (1 - len p)) by setring (Z).
    apply (plus_le_compat _ _ _ _). subtransitivity (0 ⊔ (len p + len q - 1)). lattice_order_tac.
    apply (flip_le_minus_l _ _ _). rewrite (_ $ commutativity (+) _ _). apply (flip_le_minus_r _ _ _).
    now apply (lt_iff_S_le _ _).
  Qed.

  Instance: ∀ r `{r ∊ R} p `{p ∊ Poly R}, r · p ∊ Poly R.
  Proof. intros r ? p ?. unfold dot, poly_dot. split; simpl; try apply _.
  + intros ??. rewrite (_ $ poly_coef_neg _ _). exact (mult_0_r _).
  + intros ? E. rewrite (_ $ poly_coef_after p _ E). exact (mult_0_r _).
  Qed.

  Instance: Morphism (Poly R ⇒ Poly R) (-).
  Proof. intros p1 p2 Ep. unfold_sigs. red_sig. intros i.
    change ( - [p1]_i = - [p2]_i ). now rewrite (_ $ Ep i).
  Qed.

  Instance: Morphism (Poly R ⇒ Poly R ⇒ Poly R) (+).
  Proof. apply binary_morphism_proper_back.
    intros p1 p2 Ep q1 q2 Eq. unfold_sigs. red_sig. intros i.
    change ( [p1]_i + [q1]_i = [p2]_i + [q2]_i ). now rewrite (_ $ Ep i), (_ $ Eq i).
  Qed.

  Instance: Morphism (Poly R ⇒ Poly R ⇒ Poly R) (.*.).
  Proof. apply binary_morphism_proper_back.
    intros p1 p2 Ep q1 q2 Eq. unfold_sigs. red_sig. intros i. unfold mult, poly_mult. simpl.
    apply (sum_range_proper_alt _ _ _ _). intros k ?.
    now rewrite (_ $ Ep k), (_ $ Eq (i-k)).
  Qed.

  Instance: Morphism (R ⇒ Poly R ⇒ Poly R) (·).
  Proof. apply binary_morphism_proper_back.
    intros r s Er p1 p2 Ep. unfold_sigs. red_sig. intros i.
    change ( r * [p1]_i = s * [p2]_i ). now rewrite (_ $ Ep i), (_ $ Er).
  Qed.

  Instance: AdditiveGroup (Poly R).
  Proof. repeat (split; try apply _).
  + intros p ? q ? r ? i. exact (associativity (+) _ _ _).
  + intros p ? q ? i. exact (commutativity (+) _ _).
  + intros p ? i. exact (plus_0_l _).
  + intros p ? i. exact (plus_negate_l _).
  Qed.

  Instance: Commutative (.*.) (Poly R).
  Proof. intros p ? q ? i. unfold mult, poly_mult. simpl.
    destruct (nonneg_or_neg (1+i)).
    + rewrite (_ $ sum_reverse _ _).
      apply (sum_range_proper_alt _ _ _ _). intros k ?.
      eq_replace (1+i-1-k) with (i-k) by setring (Z).
      eq_replace (i-(i-k)) with k by setring (Z).
      exact (commutativity (.*.) _ _).
    + destruct (_ : 1 + i ∊ Z⁻) as [_ E]. red in E.
      now rewrite 2!(_ $ sum_empty_le _ _ _ E).
  Qed.

  Instance: Associative (.*.) (Poly R).
  Proof. intros p ? q ? r ? i. unfold mult,poly_mult. simpl.
    subtransitivity ( ∑_(k < 1 + i) ∑_(j < (1 + i) - k) [p]_k * ([q]_j * [r]_(i - k - j)) ).
      apply (sum_range_proper_alt _ _ _ _). intros k ?.
      rewrite (_ $ sum_mult_distr_l _ _ _ _).
      now eq_replace (1+(i-k)) with (1+i-k) by setring (Z).
    rewrite (_ $ sum_tri_shuffle _ _).
    apply (sum_range_proper_alt _ _ _ _). intros k ?.
    rewrite (_ $ sum_mult_distr_r _ _ _ _).
    apply (sum_range_proper_alt _ _ _ _). intros j ?.
    eq_replace (i-j-(k-j)) with (i-k) by setring (Z).
    exact (associativity (.*.) _ _ _).
  Qed.

  Instance: LeftIdentity (.*.) 1 (Poly R) .
  Proof. intros p ? i. change (∑_(k < 1 + i) [1]_k * [p]_(i - k) = [p]_i).
    destruct (nonneg_or_neg i).
    + simpl. destruct (_ : 1+i ∊ Z₊) as [_ E]. red in E.
      rewrite (R $ sum_delta_l_0 (λ k, [p]_(i-k)) _ _ E).
      now eq_replace (i-0) with i by setring (Z).
    + rewrite (_ $ poly_coef_neg _ _). apply (sum_empty_le _ _ _).
      apply (lt_iff_S_le _ _). apply (_ :  i ∊ Z₋).
  Qed.

  Instance: LeftDistribute (.*.) (+) (Poly R).
  Proof. intros p ? q ? r ? i. unfold plus,poly_plus,mult,poly_mult. simpl.
    rewrite (_ $ sum_combine _ _ _ _). apply (sum_range_proper_alt _ _ _ _). intros k ?.
    exact (plus_mult_distr_l _ _ _).
  Qed.

  Global Instance: CommutativeRing (Poly R).
  Proof. repeat (split; try apply _). Qed.

  Global Instance poly_inject_mor: SemiRing_Morphism R (Poly R) (').
  Proof. apply (ring_morphism_alt (cast R (Poly R))).
  + intros a b E. unfold_sigs. red_sig. intro i. simpl. now rewrite (_ $ E).
  + intros a ? b ? i. simpl. exact (plus_mult_distr_l _ _ _).
  + intros a ? b ? i. simpl. destruct (nonneg_or_neg i).
    * subsymmetry. subtransitivity (∑_(k < 1 + i) δ k 0 * (a * (δ (i - k) 0 * b))).
        apply (sum_range_proper_0 _ _ _). intros k ??. subsymmetry. exact (associativity (.*.) _ _ _).
      destruct (_ : 1+i ∊ Z₊) as [_ E]. red in E.
      rewrite (R $ sum_delta_l_0 (λ k, a * (δ (i - k) 0 * b)) _ _ E).
      eq_replace (i-0) with i by setring (Z).
      rewrite 2!(_ $ commutativity (.*.) (δ i 0) _).
      exact (associativity (.*.) _ _ _).
    * mc_replace (δ i 0) with 0 on R by (apply (kronecker_delta_lt _ _); firstorder).
      rewrite (_ $ mult_0_l _). subsymmetry.
      apply (sum_empty_le _ _ _). apply (lt_iff_S_le _ _). apply (_ :  i ∊ Z₋).
  + intros i. simpl. exact (mult_1_r _).
  Qed.

  Instance poly_inject_injective: Injective R (Poly R) (').
  Proof. split; [| apply _]. intros a ? b ? P.
    rewrite <-(_ $ mult_1_l a), <-(_ $ mult_1_l b), <-(R $ kronecker_delta_diag (0:ZA)).
    exact (P 0).
  Qed.

  Instance poly_module: Module R (Poly R).
  Proof. split; try apply _; [ split; try apply _ |]; unfold dot, poly_dot.
  + intros r ? p ? q ? i. simpl. exact (plus_mult_distr_l _ _ _).
  + intros r ? s ? p ? i. simpl. exact (plus_mult_distr_r _ _ _).
  + intros r ? s ? p ? i. simpl. exact (associativity (.*.) _ _ _).
  + intros p ? i. simpl. exact (mult_1_l _).
  Qed.

  Instance poly_coef_mor : Morphism (Poly R ⇒ Z ⇒ R) coef.
  Proof. apply binary_morphism_proper_back. intros p q E ? i E2. unfold_sigs. red_sig.
    rewrite (to_eq E2). exact (E i).
  Qed.

  Lemma poly_coef_modmor i : Module_Morphism R (Poly R) R (λ p, [p]_i).
  Proof. repeat (split; try apply _).
  + now intros p ? q ?.
  + now intros r ? p ?.
  Qed.

  Lemma poly_dot_inject r `{r ∊ R} p `{p ∊ Poly R} : r · p = cast R (Poly R) r * p.
  Proof. intros i. simpl. destruct (nonneg_or_neg i).
  + replace ([p]_i) with ([p]_(i-0)) by now eq_replace (i-0) with i by setring (Z).
    destruct (_ : 1+i ∊ Z₊) as [_ E]. red in E.
    subsymmetry. subtransitivity (∑_(k < 1 + i) δ k 0 * (r * [p]_(i - k)) ).
      apply (sum_range_proper_0 _ _ _). intros k ??. subsymmetry. exact (associativity (.*.) _ _ _).
    apply (sum_delta_l_0 (λ k, r * [p]_(i-k)) _ _ E).
  + rewrite (_ $ poly_coef_neg _ _), (_ $ mult_0_r _).
    subsymmetry. apply (sum_empty_le _ _). apply (lt_iff_S_le _ _). firstorder.
  Qed.

  Instance poly_alg: UnitalCommutativeAlgebra R (Poly R).
  Proof. apply (unital_comm_alg_from_ring (R:=R) (A:=Poly R) (')).
    apply _. exact poly_dot_inject.
  Qed.

End ring.

Hint Extern 2 (poly_monomial _ ∊ Poly _) => eapply @poly_monomial_el : typeclass_instances.
Hint Extern 2 (x ∊ Poly _) => eapply @poly_var_el : typeclass_instances.
Hint Extern 2 (Module_Morphism _ _ _ (λ p, coef p _)) => eapply @poly_coef_modmor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (λ p, coef p _)) => eapply @modmor_plus_mor : typeclass_instances.
Hint Extern 2 (Morphism _ coef) => eapply @poly_coef_mor : typeclass_instances.
Hint Extern 2 (Module ?R (Poly ?R)) => eapply @poly_module : typeclass_instances.

Instance poly_pow `{Equiv A} `{Plus A} `{Mult A} `{One A} `{Zero A} (R:@set A)
  : Pow (PolyT R) ZA := nonneg_int_pow_default Z.
Instance: ∀ `{CommutativeRing (R:=R)}, NonnegIntPowSpec (Poly R) Z (poly_pow R).
Proof. intros. unfold poly_pow. apply _. Qed.

Lemma poly_var_pow `{CommutativeRing (R:=R)} n `{n ∊ Z⁺} : x^n = poly_monomial n.
Proof. ZPlus_induction n.
+ exact (nat_pow_0 (N:=Z⁺) _).
+ rewrite (_ $ nonneg_int_pow_S _ _), (_ $ IH). intros i. simpl.
  destruct (pos_or_nonpos i).
  * assert (1<1+i) as E by now apply pos_plus_lt_compat_r.
    rewrite (_ $ sum_delta_l_0 (λ k, δ (i - k) n) _ _ E).
    apply (kronecker_delta_shift _ _ _ _).
    split; intro E'; [ rewrite <-(to_eq E') | rewrite ->(to_eq E') ]; setring (Z).
  * subtransitivity 0. apply (sum_of_zero_alt _). intros k Ek1 Ek2.
      mc_replace (δ k 1) with 0 on R. exact (mult_0_l _).
      apply (kronecker_delta_lt _ _).
      apply (le_lt_trans _ i _). now apply (le_iff_lt_S _ _).
      apply (le_lt_trans _ 0 _). apply (_ : i ∊ Z⁻). exact (lt_0_1).
    subsymmetry. apply (kronecker_delta_lt _ _).
    apply (le_lt_trans _ 0 _). apply (_ : i ∊ Z⁻). apply (_ : 1+n ∊ Z₊).
Qed.

Lemma poly_var_pow_coef `{CommutativeRing (R:=R)} n `{n ∊ Z⁺} i : [x^n]_i = δ i n.
Proof. now rewrite (_ $ poly_var_pow _). Qed.

Lemma poly_expand `{CommutativeRing (R:=R)} p `{p ∊ Poly R}
  : p = ∑_(n < len p) [p]_n · x^n .
Proof. intros i.
  subsymmetry. subtransitivity (∑_(n < len p) [[p]_n · x ^ n]_i).
  apply ( preserves_sum_range (λ q, [q]_i) (λ n, [p]_n · x ^ n) _ _).
  destruct (nonneg_or_neg i).
  2: rewrite_on R ->(poly_coef_neg p i); apply (sum_of_zero_alt _);
     intros j ??; exact (poly_coef_neg _ i).
  simpl. subtransitivity (∑_(j < len p) δ j i * [p]_j). 
  + apply (sum_range_proper_0 _ _ _). intros j ??.
    rewrite (_ $ poly_var_pow_coef _ _), (_ $ kronecker_delta_sym j _).
    exact (commutativity (.*.) _ _).
  + destruct (le_or_lt (len p) i) as [E|E].
    * rewrite_on R ->(poly_coef_after _ _ E).
      now apply (sum_delta_l_zero_r _).
    * now apply (sum_delta_l_0 _ _ _).
Qed.

Section another_ring.
  Context `{CommutativeRing (R:=R)}.
  Context `{S:@set B} `{SemiRing B (R:=S)} (φ:R⇀S) `{!SemiRing_Morphism R S φ}.

  Instance: Pow B ZA := nonneg_int_pow_default Z.
  Instance: NonnegIntPowSpec S Z _ := nonneg_int_pow_default_spec.

  Definition poly_eval : S ⇀ Poly R ⇀ S := λ a p, ∑_(i < len p) φ [p]_i * a^i .

  Instance: ∀ `{a ∊ S} `{p ∊ Poly R}, poly_eval a p ∊ S.
  Proof. intros. unfold poly_eval. apply _. Qed.

  Let unfold_eval `{a ∊ S} p `{p ∊ Poly R} j
    : poly_eval a p = ∑_(i < len p ⊔ j) φ [p]_i * a^i .
  Proof. unfold poly_eval.
    destruct (total le j (len p)) as [E|E]. now rewrite (to_eq (join_l _ _ E)).
    destruct (decompose_le E) as [n[? E']]. rewrite (to_eq E'). clear dependent j.
    eq_replace (len p ⊔ (len p + n)) with (len p + n).
    2: apply (join_r _ _); apply (nonneg_plus_le_compat_r _ _).
    rewrite (_ $ sum_split_0 _ _ _).
    mc_replace (∑_(len p ≤ i < len p + n) φ [p]_i * a^i) with 0 on S.
      subsymmetry. exact (plus_0_r _).
    apply (sum_of_zero _ _ _). intros i [Ei ?].
    rewrite_on R ->(poly_coef_after _ _ Ei).
    mc_replace (φ 0) with 0 on S by exact preserves_0.
    exact (mult_0_l _).
  Qed.

  Instance poly_eval_mor: Morphism (S ⇒ Poly R ⇒ S) poly_eval.
  Proof. apply binary_morphism_proper_back. intros ?? Ea p q Ep. unfold_sigs. red_sig.
    rewrite (_ $ unfold_eval p (len q)), (_ $ unfold_eval q (len p)).
    rewrite (to_eq (commutativity join (len q) (len p))).
    apply (sum_range_proper_alt _ _ _ _). intros i ?.
    now rewrite (_ $ Ea), (_ $ Ep i).
  Qed.

  Section preservation.
    Context a `{a ∊ S} (com: ∀ `{r ∊ R}, a * φ r = φ r * a).

    Let com_power r `{r ∊ R} i `{i ∊ Z⁺} : a^i * φ r = φ r * a^i .
    Proof. ZPlus_induction i.
    + mc_replace (a^(0:ZA)) with (1:S) on S by exact (nat_pow_0 (N:=Z⁺) a).
      now rewrite (_ $ mult_1_l _), (_ $ mult_1_r _).
    + rewrite (_ $ nonneg_int_pow_S _ _), <-(_ $ associativity (.*.) a _ _), (_ $ IH).
      now rewrite 2!(_ $ associativity (.*.) _ _ _), (S $ com _ _).
    Qed.

    Let preserves_zero : poly_eval a 0 = 0.
    Proof (sum_empty_0 _).

    Let preserves_one : poly_eval a 1 = 1.
    Proof. unfold poly_eval. change (∑_(i < 1) φ [1]_i * a^i = 1).
      rewrite (_ $ sum_split_l_0 _ _), (_ $ sum_empty_eq _ _), (_ $ plus_0_r _).
      mc_replace (a^(0:ZA)) with 1 on S by exact (nat_pow_0 (N:=Z⁺) a).
      simpl.  rewrite_on R ->(kronecker_delta_diag (Y:=R) (0:ZA)) . rewrite (_ $ mult_1_r _).
      exact preserves_1.
    Qed.

    Let preserves_plus' p `{p ∊ Poly R} q `{q ∊ Poly R}
    : poly_eval a (p+q) = poly_eval a p + poly_eval a q .
    Proof.
      rewrite (_ $ unfold_eval p (len q)), (_ $ unfold_eval q (len p)).
      unfold plus at 1, poly_plus, poly_eval. simpl.
      rewrite (to_eq (commutativity join (len q) (len p))).
      rewrite (_ $ sum_combine _ _ _ _).
      apply (sum_range_proper_alt _ _ _ _). intros i ?.
      rewrite (_ $ preserves_plus _ _).
      exact (plus_mult_distr_r _ _ _).
    Qed.

    Let preserves_mult' p `{p ∊ Poly R} q `{q ∊ Poly R}
    : poly_eval a (p*q) = poly_eval a p * poly_eval a q .
    Proof.
      destruct (nat_0_or_ge_1 (N:=Z⁺) (len q)) as [Eq|Eq].
        now rewrite (_ $ poly_len_0 _ Eq), (_ $ mult_0_r _), !(_ $ preserves_zero), (_ $ mult_0_r _).
      apply (flip_nonneg_minus _ _) in Eq.
      replace (p*q) with (poly_mult p q) by reflexivity. unfold poly_mult, poly_eval. simpl.
      eq_replace (0 ⊔ (len p + len q - 1)) with (len p + len q - 1) by
        (apply join_0_nonneg; rewrite <-(_ $ associativity (+) _ _ _); apply _).
      subsymmetry. rewrite (_ $ sum_prod_distr _ _ _ _ _ _).
      subtransitivity (∑_(i < len p + len q - 1) ∑_(j < len p + len q - 1 - i) φ [p]_i * φ [q]_j * a^(i+j)).
        rewrite <-(_ $ associativity (+) (len p) _ _).
        rewrite (_ $ sum_split_0 _ _ _).
        mc_replace (∑_(len p ≤ i < len p + (len q - 1))
                    ∑_(j < len p + len q - 1 - i) φ [p]_i * φ [q]_j * a^(i+j)) with 0 on S.
          rewrite (_ $ plus_0_r _). apply (sum_range_proper_0 _ _ _). intros i ??.
          eq_replace (len p+len q-1-i) with (len q+(len p-1-i)) by setring (Z).
          assert (len p-1-i ∊ Z⁺). apply (flip_nonneg_minus _ _).
            apply (flip_le_minus_r _ _ _). rewrite (_ $ commutativity (+) i 1).
            apply (lt_iff_S_le _ _). intuition.
          rewrite (_ $ sum_split_0 _ _ _).
          mc_replace (∑_(len q ≤ j < len q + (len p - 1 - i)) φ [p]_i * φ [q]_j * a^(i+j)) with 0 on S.
            rewrite (_ $ plus_0_r _). apply (sum_range_proper_0 _ _ _). intros j ??.
            rewrite   (_ $ associativity (.*.) _ _ _).
            rewrite <-(_ $ associativity (.*.) _ _ (φ [q]_j)).
            rewrite   (_ $ com_power _ _).
            rewrite   (_ $ associativity (.*.) _ _ _).
            rewrite <-(_ $ associativity (.*.) _ _ (a^j)).
            now rewrite (_ $ nonneg_int_pow_exp_plus a i j).
          apply (sum_of_zero _). intros j [E ?].
          rewrite_on R ->(poly_coef_after q j E).
          mc_replace (φ 0) with 0 on S by exact preserves_0.
          rewrite (_ $ mult_0_r _). exact (mult_0_l _).
        apply (sum_of_zero _). intros i [E ?]. apply (sum_of_zero _). intros ??.
        rewrite_on R ->(poly_coef_after p i E).
        mc_replace (φ 0) with 0 on S by exact preserves_0.
        rewrite (_ $ mult_0_l _). exact (mult_0_l _).
      rewrite (_ $ sum_tri_shuffle _ _). apply (sum_range_proper_0 _ _ _). intros j ??.
      rewrite (_ $ preserves_sum_range φ _ _ _), (_ $ sum_mult_distr_r _ _ _ _).
      apply (sum_range_proper_0 _ _ _). intros i ??.
      eq_replace (i+(j-i)) with j by setring (Z).
      now rewrite (_ $ preserves_mult _ _).
    Qed.

    Instance poly_eval_srmor : SemiRing_Morphism (Poly R) S (poly_eval a).
    Proof. apply semiring_morphism_alt; try apply _.
    + exact preserves_plus'.
    + exact preserves_mult'.
    + exact preserves_zero.
    + exact preserves_one.
    Qed.

    Lemma poly_eval_const_applied r `{r ∊ R} : poly_eval a ('r) = φ r.
    Proof. unfold poly_eval. simpl.
      rewrite (_ $ sum_split_l_0 _ _), (_ $ sum_empty_eq _ _), (_ $ plus_0_r _).
      rewrite_on S ->(nonneg_int_pow_0 (Z:=Z) a).
      now rewrite (_ $ mult_1_r _), (_ $ kronecker_delta_diag _), (_ $ mult_1_l _).
    Qed.

    Lemma poly_eval_const : poly_eval a ∘ (') = φ.
    Proof. intros r1 r2 E. unfold_sigs. unfold compose. red_sig.
      rewrite <-(_ $ E). exact (poly_eval_const_applied _).
    Qed.

    Lemma poly_eval_var : poly_eval a x = a.
    Proof. unfold poly_eval. simpl. subtransitivity (∑_(i < 2) δ i 1 * a^i).
        apply (sum_range_proper_0 _ _ _). intros i ??.
        now rewrite_on S ->(preserves_kronecker_delta φ i 1).
      rewrite_on S <-(nonneg_int_pow_1 (Z:=Z) a).
      apply (sum_delta_l (a^)). split. exact le_0_1. exact lt_1_2.
    Qed.

    Context (g : Poly R ⇀ S) `{!SemiRing_Morphism (Poly R) S g}.

    Lemma poly_eval_unique : g ∘ (') = φ → g x = a → g = poly_eval a.
    Proof. intros Er Ea p q Eq. unfold_sigs. red_sig.
      rewrite (Poly R $ poly_expand p). rewrite <-(_ $ Eq). clear dependent q.
      rewrite (_ $ preserves_sum_range g _ _ _).
      apply (sum_range_proper_0 _ _ _). intros n ??.
      rewrite (_ $ poly_dot_inject _ _).
      rewrite (_ $ preserves_mult _ _).
      setoid_rewrite (Er _ _ (_:Proper (R,=) [p]_n)).
      rewrite (_ $ preserves_nat_pow (N:=Z⁺) _ _).
      now rewrite (_ $ Ea).
    Qed.

  End preservation.

End another_ring.

Hint Extern 2 (Morphism _ (poly_eval _)) => eapply @poly_eval_mor : typeclass_instances.

Instance poly_to_polynomial_ring `{Mult A} `{Zero A} `{One A} `{Equiv A} (R:@set A)
  : ToPolynomialRing R (Poly R) := (').

Instance poly_polynomial_ring_var `{Zero A} `{One A} `{Equiv A} (R:@set A)
  : PolynomialVar (Poly R) := x.

Instance poly_polynomial_ring_eval `{Zero A} `{Equiv A} (R:@set A)
  : PolynomialEval R (Poly R) := @poly_eval A _ _ R.

Instance poly_polynomial_ring `{CommutativeRing (R:=R)} : Polynomial_Ring R (Poly R).
Proof. split; try apply _.
* exact poly_alg.
* exact poly_dot_inject.
* exact (_ : x ∊ Poly R).
* intros ? S ?????? φ ? a ? P. split.
+ apply (poly_eval_srmor _ _ P).
+ apply (poly_eval_const _ _).
+ apply (poly_eval_var _ _).
+ apply (poly_eval_unique _ _).
Qed.
