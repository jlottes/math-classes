Require Import
  stdlib_binary_integers
  abstract_algebra interfaces.additional_operations interfaces.orders
  interfaces.integers theory.integers orders.integers
  interfaces.naturals theory.naturals orders.naturals nonneg_integers_naturals peano_naturals
  theory.setoids theory.rings orders.rings
  orders.lattices orders.minmax lattice_ordered_rings
  theory.kronecker_delta
  stdlib_ring misc.quote.

Local Notation ZA := BinNums.Z.
Local Notation Z  := (every BinNums.Z).

Local Notation nat := (every nat).
Local Notation "#" := (naturals_to_semiring Z⁺ nat).

Ltac ZPlus_induction n :=
    let P := fresh "P" in
    pattern n; match goal with H : n ∊ Z⁺ |- ?P' n => set (P:=P'); revert n H end;
    apply (naturals.induction (N:=Z⁺));
    [ let E:=fresh "E" in intros ?? [_ E]; now rewrite (to_eq E) |..];
    subst P; [ simpl | intros n ?; simpl; let IH:=fresh "IH" in intro IH ].

Local Notation e := mon_unit.

Section def.
  Context `{Monoid (M:=M)} (f:ZA → M).

  Fixpoint bigop_nat (i:ZA) (n:nat) := match n with
  | O => e
  | S m => f i & bigop_nat (1+i) m
  end.

  Definition bigop_range : Z ⇀ Z ⇀ M := λ ib ie, bigop_nat ib (# (0 ⊔ (ie-ib))).
End def.

Notation "⦿_ ( a ≤ i < b ) f" := (bigop_range (fun i => f) a b)
  (at level 41, f at level 41, a, i, b at level 50,
   right associativity, format "⦿_ ( a  ≤  i  <  b )  f") : mc_scope.

Notation "⦿_ ( i < n ) f" := (bigop_range (fun i => f) 0 n)
  (at level 41, f at level 41, i, n at level 50,
   right associativity, format "⦿_ ( i  <  n )  f") : mc_scope.

Class Big_Operand `(M:set) f : Prop := big_operand_el (i:ZA) : f i ∊ M .
Ltac solve_big_operand := intro; apply _ .
Hint Extern 5 (Big_Operand _ _) => solve_big_operand : typeclass_instances.
Hint Extern 2 (?f _ ∊ ?M) =>
   match goal with H : Big_Operand M f |- _ => eapply (big_operand_el (Big_Operand := H))
   end : typeclass_instances.

Class Big_Operand_Binary `(M:set) f : Prop := big_operand_bin_el (i:ZA) (j:ZA) : f i j ∊ M .
Ltac solve_big_operand_bin := intros ??; apply _ .
Hint Extern 5 (Big_Operand_Binary _ _) => solve_big_operand_bin : typeclass_instances.
Hint Extern 2 (?f _ _ ∊ ?M) =>
   match goal with H : Big_Operand_Binary M f |- _ =>
     eapply (big_operand_bin_el (Big_Operand_Binary := H))
   end : typeclass_instances.


Local Ltac range_tac a b :=
  let Ea := fresh "Ea" in destruct (total le b a) as [Ea|Ea]; [|
    let n := fresh "n" in let En := fresh "En" in
    destruct (decompose_le Ea) as [n[? En]]; rewrite (to_eq En); clear dependent b;
    ZPlus_induction n
  ].

Section contents.
  Context `{Monoid (M:=M)} (f:ZA → M).

  Lemma bigop_empty_le a b : b ≤ a → ⦿_(a ≤ i < b) f i = e.
  Proof. intro E. unfold bigop_range.
    apply (flip_nonpos_minus _ _) in E.
    now rewrite (to_eq (join_0_nonpos (b-a))), (to_eq (preserves_0 (f:=#))).
  Qed.

  Lemma bigop_empty_plus_0 a : ⦿_(a ≤ i < a+0) f i = e.
  Proof. apply (bigop_empty_le _ _). rewrite (plus_0_r _). reflexivity. Qed.

  Lemma bigop_empty_eq a : ⦿_(a ≤ i < a) f i = e.
  Proof. apply (bigop_empty_le _ _). reflexivity. Qed.

  Lemma bigop_empty_0 : ⦿_(i < 0) f i = e.
  Proof bigop_empty_eq 0.

  Context `{!Big_Operand M f}.

  Instance: ∀ n i, bigop_nat f i n ∊ M.
  Proof. intros n. induction n; simpl; intros; apply _. Qed.

  Instance bigop_range_el a b : bigop_range f a b ∊ M.
  Proof. intros. unfold bigop_range. apply _. Qed.

  Instance bigop_range_mor: Morphism (Z ⇒ Z ⇒ M) (bigop_range f).
  Proof. apply binary_morphism_proper_back. intros a1 a2 Ea b1 b2 Eb. unfold_sigs.
    red_sig. now rewrite (to_eq Ea), (to_eq Eb).
  Qed.

  Lemma bigop_split_l a n {eln: n ∊ Z₊} 
    : ⦿_(a ≤ i < a+n) f i = f a & ⦿_(1+a ≤ i < a+n) f i.
  Proof. destruct (int_pos_decompose n) as [m [? Em]]. rewrite (to_eq Em). clear dependent n.
    unfold bigop_range.
    cut (# (0 ⊔ (a + (1+m) - a)) = 1 + (# (0 ⊔ (a + (1 + m) - (1 + a)))) ).
      intro E. now rewrite (to_eq E).
    rewrite <-(to_eq (preserves_1 (f:=#))), <-(to_eq (preserves_plus _ _)).
    match goal with |- # ?x = # ?y => cut (x=y) end. intro E. now rewrite (to_eq E).
    eq_replace (a+(1+m)-a) with (1+m) by setring (Z).
    eq_replace (a+(1+m)-(1+a)) with m by setring (Z).
    pose proof ( to_eq (join_0_nonneg m) ) as E. rewrite E.
    now rewrite (to_eq (join_0_nonneg _)).
  Qed.

  Lemma bigop_split_l_0 n {eln: n ∊ Z₊} 
    :  ⦿_(i < n) f i = f 0 & ⦿_(1 ≤ i < n) f i.
  Proof. rewrite <-(_ $ plus_0_l n), <-(_ $ plus_0_l 1). exact (bigop_split_l 0 n). Qed.

  Lemma bigop_split_r a n {eln: n ∊ Z⁺} 
    :  ⦿_(a ≤ i < a+(1+n)) f i = ⦿_(a ≤ i < a+n) f i & f (a+n) .
  Proof. revert a. ZPlus_induction n.
  + intros a. rewrite (to_eq (plus_0_r a)), (to_eq (plus_0_r 1)).
    rewrite (_ $ bigop_empty_eq _). rewrite (_ $ left_identity _ _).
    unfold bigop_range. eq_replace (# (0 ⊔ (a + 1 - a))) with (1:nat).
      simpl. exact (right_identity _ _).
    eq_replace (a+1-a) with 1 by setring (Z).
    rewrite (to_eq (join_0_nonneg _)). exact preserves_1.
  + intros a. rewrite 2!(_ $ bigop_split_l a _).
    eq_replace (a+(1+(1+n))) with (1+a+(1+n)) by setring (Z).
    rewrite (_ $ IH (1+a)).
    eq_replace (1+a+n) with (a+(1+n)) by setring (Z).
    exact (associativity _ _ _ _).
  Qed.

  Lemma bigop_split_r_0 n {eln: n ∊ Z⁺} : ⦿_(i < 1+n) f i = ⦿_(i < n) f i & f n .
  Proof. rewrite <-(_ $ plus_0_l (1+n)). rewrite <-(to_eq (plus_0_l n)) at 2 3.
    exact (bigop_split_r 0 _).
  Qed.

  Lemma bigop_split a n `{n ∊ Z⁺} m `{m ∊ Z⁺}
  : ⦿_(a ≤ i < a+n+m) f i = ⦿_(a ≤ i < a+n) f i & ⦿_(a+n ≤ i < a+n+m) f i .
  Proof. ZPlus_induction m.
  + now rewrite (to_eq (plus_0_r _)), (_ $ bigop_empty_eq _), (_ $ right_identity _ _).
  + rewrite (_ $ bigop_split_r _ _), (M $ associativity (&) _ _ _), <-(_ $ IH).
    eq_replace (a+n+(1+m)) with (a+(1+(n+m))) by setring (Z). rewrite (_ $ bigop_split_r _ _).
    now eq_replace (a+(n+m)) with (a+n+m) by setring (Z).
  Qed.

  Lemma bigop_split_0 n `{n ∊ Z⁺} m `{m ∊ Z⁺}
  : ⦿_(i < n+m) f i = ⦿_(i < n) f i & ⦿_(n ≤ i < n+m) f i .
  Proof bigop_split 0 n m.

  Lemma bigop_of_unit a b : (∀ i, a ≤ i < b → f i = e) → ⦿_(a ≤ i < b) f i = e .
  Proof. range_tac a b; intro P.
  + exact (bigop_empty_le _ _ Ea).
  + exact (bigop_empty_plus_0 _).
  + assert (a + n < a + (1 + n)).
      apply (strictly_order_preserving (a +) _ _).
      apply (pos_plus_lt_compat_l _ _).
    cut (⦿_(a ≤ i < a + n) f i = e). intro E.
      rewrite (_ $ bigop_split_r _ _), (_ $ E), (_ $ left_identity _ _).
      apply P. split; trivial. now apply nonneg_plus_le_compat_r.
    apply IH. intros i [E1 E2]. apply P. split; trivial. subtransitivity (a+n).
  Qed.

  Lemma bigop_of_unit_alt n : (∀ i `{i ∊ Z⁺}, i < n → f i = e) → ⦿_(i < n) f i = e.
  Proof. intro P. apply bigop_of_unit. intros i [E1 E2]. apply (P i); trivial. now split. Qed.
End contents.

Hint Extern 2 (bigop_range _ _ _ ∊ _) => eapply @bigop_range_el : typeclass_instances.
Hint Extern 2 (Morphism _ (bigop_range _)) => eapply @bigop_range_mor : typeclass_instances.

Instance bigop_range_proper `{Monoid (M:=M)} :
  Proper ((@equiv (Z ⇀ M) _)==>eq==>eq==>(M,=)) bigop_range | 10.
Proof. intros f g Ef a' a E1 b' b E2. rewrite E1,E2. clear a' b' E1 E2.
  assert (Morphism (Z ⇒ M) f) by ( change (f=f); transitivity g; trivial; now symmetry ).
  assert (Morphism (Z ⇒ M) g) by ( change (g=g); transitivity f; trivial; now symmetry ).
  red_sig. range_tac a b.
+ now rewrite 2!(_ $ bigop_empty_le _ _ _ Ea).
+ now rewrite 2!(_ $ bigop_empty_plus_0 _ _).
+ now rewrite 2!(_ $ bigop_split_r _ _ _), (_ $ IH), ( Ef _ _ (_ : Proper (Z,=) (a+n)) ) .
Qed.

Lemma bigop_range_proper_alt `{Monoid (M:=M)} a b f g `{!Big_Operand M f} `{!Big_Operand M g}
  : (∀ i, a ≤ i < b → f i = g i) → bigop_range f a b = bigop_range g a b.
Proof. range_tac a b; intro P.
+ now rewrite 2!(_ $ bigop_empty_le _ _ _ Ea).
+ now rewrite 2!(_ $ bigop_empty_plus_0 _ _).
+ rewrite 2!(_ $ bigop_split_r _ _ _).
  assert (a + n < a + (1 + n)).
    apply (flip_pos_minus _ _). eq_replace (a+(1+n)-(a+n)) with (1:Z) by setring (Z). apply _.
  mc_replace (f (a+n)) with (g (a+n)) on M.
    mc_replace (⦿_(a ≤ i < a + n) f i) with (⦿_(a ≤ i < a + n) g i) on M. easy.
    apply IH. intros i E. apply P. intuition. subtransitivity (a+n).
  apply P. split; trivial. apply (nonneg_plus_le_compat_r _ _).
Qed.

Lemma bigop_range_proper_0 `{Monoid (M:=M)} n f g `{!Big_Operand M f} `{!Big_Operand M g}
  : (∀ `{i ∊ Z⁺}, i < n → f i = g i) → bigop_range f 0 n = bigop_range g 0 n.
Proof. intro P. apply (bigop_range_proper_alt _ _ _ _). intros i [??]. apply P; firstorder. Qed.


Lemma preserves_bigop_range `{Monoid (M:=M)} `{Monoid (M:=M')} (g:M ⇀ M') `{!Monoid_Morphism M M' g}
  f `{!Big_Operand M f} a b : g (⦿_(a ≤ i < b) f i) = ⦿_(a ≤ i < b) g (f i) .
Proof. range_tac a b.
+ rewrite 2!(_ $ bigop_empty_le _ _ _ Ea). exact preserves_mon_unit.
+ rewrite 2!(_ $ bigop_empty_plus_0 _ _). exact preserves_mon_unit.
+ rewrite 2!(_ $ bigop_split_r _ _ _), <-(_ $ IH). exact (preserves_sg_op _ _).
Qed.

Lemma bigop_shift `{Monoid (M:=M)} f `{!Big_Operand M f}
  a b k : ⦿_(a ≤ i < b) f i = ⦿_(a-k ≤ i < b-k) f (i+k).
Proof. range_tac a b.
+ rewrite (_ $ bigop_empty_le _ _ _ Ea).
  apply (order_preserving (+ -k) _ _) in Ea.
  now rewrite (_ $ bigop_empty_le _ _ _ Ea).
+ eq_replace (a+0) with a by setring (Z). now rewrite 2!(_ $ bigop_empty_eq _ _).
+ eq_replace (a+n-k) with (a-k+n) in IH by setring (Z).
  eq_replace (a+(1+n)-k) with (a-k+(1+n)) by setring (Z).
  rewrite 2!(_ $ bigop_split_r _ _ _), <-(_ $ IH).
  now eq_replace (a-k+n+k) with (a+n) by setring (Z).
Qed.

Lemma bigop_reverse `{CommutativeMonoid (M:=M)} f `{!Big_Operand M f}
  m : ⦿_(i < m) f i = ⦿_(i < m) f (m-1-i) .
Proof. range_tac 0 m; repeat rewrite (to_eq (plus_0_l _)).
+ now rewrite 2!(_ $ bigop_empty_le _ _ _ Ea).
+ now rewrite 2!(_ $ bigop_empty_0 _).
+ rewrite (to_eq (plus_0_l _)) in IH.
  rewrite (_ $ bigop_split_r_0 _ _) at 1.
  rewrite (_ $ IH), (_ $ commutativity (&) _ _).
  rewrite (_ $ bigop_split_l_0 _ (1+n)).
  rewrite (_ $ bigop_shift _ 1 _ 1).
  rewrite (to_eq (plus_negate_r 1)).
  eq_replace (1+n-1) with n by setring (Z).
  eq_replace (n-0) with n by setring (Z).
  mc_replace (⦿_(i < n) f (n - (i + 1))) with
             (⦿_(i < n) f (n - 1 - i)) on M. subreflexivity.
  apply (bigop_range_proper_alt _ _ _ _). intros i ?.
  now eq_replace (n-(i+1)) with (n-1-i) by setring (Z).
Qed.

Lemma bigop_reverse_alt `{CommutativeMonoid (M:=M)} f `{!Big_Operand M f}
  n : ⦿_(i < 1+n) f i = ⦿_(i < 1+n) f (n-i) .
Proof. cut (⦿_(i < 1+n) f (n-i) = ⦿_(i < 1+n) f ((1+n)-1-i)).
    intro E. rewrite (_ $ E). exact (bigop_reverse f _).
  apply (bigop_range_proper_alt _ _ _ _). intros i ?.
  now eq_replace (1+n-1-i) with (n-i) by setring (Z).
Qed.

Lemma bigop_combine `{CommutativeMonoid (M:=M)}
  f g `{!Big_Operand M f} `{!Big_Operand M g}
  a b : ⦿_(a ≤ i < b) f i & ⦿_(a ≤ i < b) g i = ⦿_(a ≤ i < b) (f i & g i).
Proof. range_tac a b.
+ rewrite 3!(_ $ bigop_empty_le _ _ _ Ea). exact (left_identity _ _).
+ rewrite 3!(_ $ bigop_empty_plus_0 _ _). exact (left_identity _ _).
+ rewrite 3!(_ $ bigop_split_r _ _ _).
  rewrite  (_ $ associativity (&) _ _ _),
         <-(_ $ associativity (&) _ (f (a+n)) _),
           (_ $ commutativity (&) (f (a+n)) _),
           (_ $ associativity (&) _ _ (f (a+n))).
  rewrite (_ $ IH). subsymmetry. exact (associativity (&) _ _ _).
Qed.

Lemma bigop_reorder `{CommutativeMonoid (M:=M)} f `{!Big_Operand_Binary M f}
  i₁ i₂ j₁ j₂ : ⦿_(i₁ ≤ i < i₂) ⦿_(j₁ ≤ j < j₂) f i j
              = ⦿_(j₁ ≤ j < j₂) ⦿_(i₁ ≤ i < i₂) f i j .
Proof. range_tac i₁ i₂.
+ rewrite (_ $ bigop_empty_le _ _ _ Ea). subsymmetry.
  apply (bigop_of_unit _ _ _). intros i ?. exact (bigop_empty_le _ _ _ Ea).
+ rewrite (_ $ bigop_empty_plus_0 _ _). subsymmetry.
  apply (bigop_of_unit _ _ _). intros i ?. exact (bigop_empty_plus_0 _ _).
+ rewrite (_ $ bigop_split_r _ _ _), (_ $ IH), (_ $ bigop_combine _ _ _ _).
  apply (bigop_range_proper_alt _ _ _ _). intros i ?.
  now rewrite (_ $ bigop_split_r _ _ _).
Qed.

Lemma bigop_tri_shuffle `{CommutativeMonoid (M:=M)} f `{!Big_Operand_Binary M f}
  n : ⦿_(i < n) ⦿_(j < n - i) f i j = ⦿_(k < n) ⦿_(i < 1+k) f i (k-i) .
Proof. revert n. intro m. range_tac 0 m; repeat rewrite (to_eq (plus_0_l _)).
+ now rewrite 2!(_ $ bigop_empty_le _ _ _ Ea).
+ now rewrite 2!(_ $ bigop_empty_0 _).
+ rewrite (to_eq (plus_0_l _)) in IH.
  rewrite (_ $ bigop_split_r_0 (fun k => ⦿_(i < 1 + k) f i (k - i)) _).
  rewrite <-(_ $ IH).
  subtransitivity (⦿_(i < 1 + n) (⦿_(j < n - i) f i j & f i (n - i))).
    apply (bigop_range_proper_alt _ _ _ _). intros i [? E].
    apply (le_iff_lt_S _ _), (flip_nonneg_minus _ _) in E.
    eq_replace (1+n-i) with (1+(n-i)) by setring (Z).
    exact (bigop_split_r_0 _ _).
  rewrite <-(_ $ bigop_combine _ _ _ _).
  rewrite (_ $ bigop_split_r_0 _ _).
  now rewrite (_ $ plus_negate_r n), (_ $ bigop_empty_0 _), (_ $ plus_0_r _).
Qed.

Definition sum_range {A} {Aplus:Plus A} {Azero:Zero A} {R:@set A}
  := @bigop_range A plus_is_sg_op zero_is_mon_unit R.

Notation "∑_ ( a ≤ i < b ) f" := (sum_range (fun i => f) a b)
  (at level 41, f at level 41, a, i, b at level 50,
   right associativity, format "∑_ ( a  ≤  i  <  b )  f") : mc_scope.

Notation "∑_ ( i < n ) f" := (sum_range (fun i => f) 0 n)
  (at level 41, f at level 41, i, n at level 50,
   right associativity, format "∑_ ( i  <  n )  f") : mc_scope.

Section sum.
  Context {A} {Aequiv:Equiv A} {Aplus:Plus A} {Azero:Zero A} {R:@set A} `{!AdditiveMonoid R}.

  Lemma sum_empty_le f a b : b ≤ a → ∑_(a ≤ i < b) f i = 0.
  Proof bigop_empty_le f a b.

  Lemma sum_empty_plus_0 f a : ∑_(a ≤ i < a+0) f i = 0.
  Proof bigop_empty_plus_0 f a.

  Lemma sum_empty_eq f a : ∑_(a ≤ i < a) f i = 0.
  Proof bigop_empty_eq f a.

  Lemma sum_empty_0 f : ∑_(i < 0) f i = 0.
  Proof bigop_empty_0 f.

  Global Instance sum_range_proper :
    Proper ((@equiv (Z ⇀ R) _)==>eq==>eq==>(R,=)) sum_range | 10.
  Proof bigop_range_proper.

  Section operand.
    Context f `{!Big_Operand R f}.
    Context g `{!Big_Operand R g}.

    Instance sum_range_el a b : sum_range f a b ∊ R.
    Proof bigop_range_el f a b.

    Instance sum_range_mor: Morphism (Z ⇒ Z ⇒ R) (sum_range f).
    Proof bigop_range_mor f.

    Lemma sum_split_l a n {eln: n ∊ Z₊} 
      : ∑_(a ≤ i < a+n) f i = f a + ∑_(1+a ≤ i < a+n) f i.
    Proof bigop_split_l f a n.

    Lemma sum_split_l_0 n {eln: n ∊ Z₊} 
      :  ∑_(i < n) f i = f 0 + ∑_(1 ≤ i < n) f i.
    Proof bigop_split_l_0 f n.

    Lemma sum_split_r a n {eln: n ∊ Z⁺} 
      :  ∑_(a ≤ i < a+(1+n)) f i = ∑_(a ≤ i < a+n) f i + f (a+n) .
    Proof bigop_split_r f a n.

    Lemma sum_split_r_0 n {eln: n ∊ Z⁺} : ∑_(i < 1+n) f i = ∑_(i < n) f i + f n .
    Proof bigop_split_r_0 f n.

    Lemma sum_split a n `{n ∊ Z⁺} m `{m ∊ Z⁺}
    : ∑_(a ≤ i < a+n+m) f i = ∑_(a ≤ i < a+n) f i + ∑_(a+n ≤ i < a+n+m) f i .
    Proof bigop_split f a n m.

    Lemma sum_split_0 n `{n ∊ Z⁺} m `{m ∊ Z⁺}
    : ∑_(i < n+m) f i = ∑_(i < n) f i + ∑_(n ≤ i < n+m) f i .
    Proof bigop_split_0 f n m.

    Lemma sum_of_zero a b : (∀ i, a ≤ i < b → f i = 0) → ∑_(a ≤ i < b) f i = 0 .
    Proof bigop_of_unit f a b.

    Lemma sum_of_zero_alt n : (∀ i `{i ∊ Z⁺}, i < n → f i = 0) → ∑_(i < n) f i = 0.
    Proof bigop_of_unit_alt f n.

    Lemma sum_range_proper_alt a b
    : (∀ i, a ≤ i < b → f i = g i) → sum_range f a b = sum_range g a b.
    Proof bigop_range_proper_alt a b f g.

    Lemma sum_range_proper_0 n
    : (∀ `{i ∊ Z⁺}, i < n → f i = g i) → sum_range f 0 n = sum_range g 0 n.
    Proof bigop_range_proper_0 n f g.

    Lemma sum_shift a b k : ∑_(a ≤ i < b) f i = ∑_(a-k ≤ i < b-k) f (i+k).
    Proof bigop_shift f a b k.

    Lemma sum_reverse n : ∑_(i < n) f i = ∑_(i < n) f (n-1-i) .
    Proof bigop_reverse f n.

    Lemma sum_reverse_alt n : ∑_(i < 1+n) f i = ∑_(i < 1+n) f (n-i) .
    Proof bigop_reverse_alt f n.

    Lemma sum_combine a b : ∑_(a ≤ i < b) f i + ∑_(a ≤ i < b) g i 
                          = ∑_(a ≤ i < b) (f i + g i).
    Proof bigop_combine f g a b.

  End operand.

  Section preservation.
    Context {B} {Bequiv:Equiv B} {Bplus:Plus B} {Bzero:Zero B} {R':@set B} `{!AdditiveMonoid R'}.
    Context (g:R ⇀ R') `{!AdditiveMonoid_Morphism R R' g}.
    Context f `{!Big_Operand R f}.

    Lemma preserves_sum_range a b : g (∑_(a ≤ i < b) f i) = ∑_(a ≤ i < b) g (f i) .
    Proof preserves_bigop_range g f a b.
  End preservation.

  Context f `{!Big_Operand_Binary R f}.

  Lemma sum_reorder i₁ i₂ j₁ j₂ : ∑_(i₁ ≤ i < i₂) ∑_(j₁ ≤ j < j₂) f i j
                                = ∑_(j₁ ≤ j < j₂) ∑_(i₁ ≤ i < i₂) f i j .
  Proof bigop_reorder f i₁ i₂ j₁ j₂.

  Lemma sum_tri_shuffle n : ∑_(i < n) ∑_(j < n - i) f i j 
                          = ∑_(k < n) ∑_(i < 1+k) f i (k-i) .
  Proof bigop_tri_shuffle f n.
End sum.

Hint Extern 2 (sum_range _ _ _ ∊ _) => eapply @sum_range_el : typeclass_instances.
Hint Extern 2 (Morphism _ (sum_range _)) => eapply @sum_range_mor : typeclass_instances.

Section sum_mult_distr.
  Context `{SemiRng (R:=R)} .

  Lemma sum_mult_distr_l f `{!Big_Operand R f} a b x `{x ∊ R}
    : x * sum_range f a b = ∑_(a ≤ i < b) x * f i .
  Proof. range_tac a b.
  + rewrite 2!(_ $ sum_empty_le _ _ _ Ea). exact (mult_0_r _).
  + rewrite 2!(_ $ sum_empty_plus_0 _ _). exact (mult_0_r _).
  + now rewrite 2!(_ $ sum_split_r _ _ _), (_ $ plus_mult_distr_l _ _ _), (_ $ IH).
  Qed.

  Lemma sum_mult_distr_r f `{!Big_Operand R f} a b x `{x ∊ R}
    : sum_range f a b * x = ∑_(a ≤ i < b) f i * x.
  Proof. range_tac a b.
  + rewrite 2!(_ $ sum_empty_le _ _ _ Ea). exact (mult_0_l _).
  + rewrite 2!(_ $ sum_empty_plus_0 _ _). exact (mult_0_l _).
  + now rewrite 2!(_ $ sum_split_r _ _ _), (_ $ plus_mult_distr_r _ _ _), (_ $ IH).
  Qed.

  Lemma sum_prod_distr f `{!Big_Operand R f} g `{!Big_Operand R g} i₁ i₂ j₁ j₂
    : sum_range f i₁ i₂ * sum_range g j₁ j₂
    = ∑_(i₁ ≤ i < i₂) ∑_(j₁ ≤ j < j₂) f i * g j .
  Proof. range_tac i₁ i₂.
  + rewrite 2!(_ $ sum_empty_le _ _ _ Ea). exact (mult_0_l _).
  + rewrite 2!(_ $ sum_empty_plus_0 _ _). exact (mult_0_l _).
  + rewrite 2!(_ $ sum_split_r _ _ _).
    now rewrite (_ $ plus_mult_distr_r _ _ _), (_ $ IH), (_ $ sum_mult_distr_l _ _ _ _).
  Qed.

End sum_mult_distr.

Local Notation δ := kronecker_delta.

Section sum_delta.
  Context `{SemiRing (R:=R)}.
  Context f `{!Big_Operand R f}.

  Lemma sum_delta_l_zero_l a b j : j < a → ∑_(a ≤ i < b) δ i j * f i = 0.
  Proof. intro. apply (sum_of_zero _). intros i ?.
    cut (j<i). intro E. rewrite (_ $ kronecker_delta_gt _ _ E). exact (mult_0_l _).
    apply (lt_le_trans _ a _); intuition.
  Qed.

  Lemma sum_delta_l_zero_r a b j : b ≤ j → ∑_(a ≤ i < b) δ i j * f i = 0.
  Proof. intro. apply (sum_of_zero _). intros i ?.
    cut (i<j). intro E. rewrite (_ $ kronecker_delta_lt _ _ E). exact (mult_0_l _).
    apply (lt_le_trans _ b _); intuition.
  Qed.

  Lemma sum_delta_l a b j : a ≤ j < b → ∑_(a ≤ i < b) δ i j * f i = f j .
  Proof. revert j. range_tac a b; intro j.
  + intro. apply (le_iff_not_lt_flip _ _) in Ea. destruct Ea. apply (le_lt_trans _ j _); intuition.
  + intro. destruct (irreflexivity (<) a). rewrite <-(_ $ plus_0_r a) at 2. apply (le_lt_trans _ j _); intuition.
  + intro. rewrite (_ $ sum_split_r _ _ _). destruct (le_or_lt (a+n) j) as [Ej|Ej].
    * rewrite (_ $ sum_delta_l_zero_r _ _ _ Ej).
      eq_replace (a+n) with j.
        now rewrite (_ $ plus_0_l _), (_ $ kronecker_delta_diag _), (_ $ mult_1_l _).
      apply (antisymmetry le _ _); trivial. apply (le_iff_lt_plus_1 _ _).
      now eq_replace (a+n+1) with (a+(1+n)) by setring (Z).
    * rewrite (_ $ kronecker_delta_gt _ _ Ej), (_ $ mult_0_l _), (_ $ plus_0_r _).
      apply IH. intuition.
  Qed.

  Lemma sum_delta_r_zero_l a b j : j < a → ∑_(a ≤ i < b) f i * δ i j = 0.
  Proof. intro. apply (sum_of_zero _). intros i ?.
    cut (j<i). intro E. rewrite (_ $ kronecker_delta_gt _ _ E). exact (mult_0_r _).
    apply (lt_le_trans _ a _); intuition.
  Qed.

  Lemma sum_delta_r_zero_r a b j : b ≤ j → ∑_(a ≤ i < b) f i * δ i j = 0.
  Proof. intro. apply (sum_of_zero _). intros i ?.
    cut (i<j). intro E. rewrite (_ $ kronecker_delta_lt _ _ E). exact (mult_0_r _).
    apply (lt_le_trans _ b _); intuition.
  Qed.

  Lemma sum_delta_r a b j : a ≤ j < b → ∑_(a ≤ i < b) f i * δ i j  = f j .
  Proof. revert j. range_tac a b; intro j.
  + intro. apply (le_iff_not_lt_flip _ _) in Ea. destruct Ea. apply (le_lt_trans _ j _); intuition.
  + intro. destruct (irreflexivity (<) a). rewrite <-(_ $ plus_0_r a) at 2. apply (le_lt_trans _ j _); intuition.
  + intro. rewrite (_ $ sum_split_r _ _ _). destruct (le_or_lt (a+n) j) as [Ej|Ej].
    * rewrite (_ $ sum_delta_r_zero_r _ _ _ Ej).
      eq_replace (a+n) with j.
        now rewrite (_ $ plus_0_l _), (_ $ kronecker_delta_diag _), (_ $ mult_1_r _).
      apply (antisymmetry le _ _); trivial. apply (le_iff_lt_plus_1 _ _).
      now eq_replace (a+n+1) with (a+(1+n)) by setring (Z).
    * rewrite (_ $ kronecker_delta_gt _ _ Ej), (_ $ mult_0_r _), (_ $ plus_0_r _).
      apply IH. intuition.
  Qed.

  Lemma sum_delta_l_0 n j `{j ∊ Z⁺} : j < n → ∑_(i < n) δ i j * f i = f j .
  Proof. intro. apply (sum_delta_l 0 n j). firstorder. Qed.

  Lemma sum_delta_r_0 n j `{j ∊ Z⁺} : j < n → ∑_(i < n) f i * δ i j = f j .
  Proof. intro. apply (sum_delta_r 0 n j). firstorder. Qed.

End sum_delta.

Lemma sum_delta `{SemiRing (R:=R)} a b j : a ≤ j < b → ∑_(a ≤ i < b) δ i j  = 1 .
Proof. mc_replace (∑_(a ≤ i < b) δ i j) with (∑_(a ≤ i < b) δ i j * (fun i => 1) i) on R.
  exact (sum_delta_l (λ _, 1) a b j).
  apply (sum_range_proper_alt _ _ _ _). intros i ?. subsymmetry. exact (mult_1_r _).
Qed.

Lemma sum_delta_0 `{SemiRing (R:=R)} n j `{j ∊ Z⁺} : j < n → ∑_(i < n) δ i j = 1 .
Proof. intro. apply (sum_delta 0 n j). firstorder. Qed.
