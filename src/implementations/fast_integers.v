Require Import
  BigZ
  interfaces.abstract_algebra interfaces.integers
  interfaces.additional_operations fast_naturals
  theory.setoids.
Require Export
  ZType_integers.

Module BigZ_Integers := ZType_Integers BigZ.

Hint Extern 10 (@Subset bigZ) => eexact (every bigZ) : typeclass_instances.

Local Notation bigN := (every bigN).
Local Notation bigZ := (every bigZ).

Instance inject_fastN_fastZ: Cast bigN bigZ := BigZ.Pos.

Instance: SemiRing_Morphism bigN bigZ (').
Proof. repeat (split; try apply _); unfold_sigs; intuition. Qed.

Instance bigZ_pow: Pow BigZ.t BigZ.t := BigZ.pow.

Require Import misc.quote.

Instance: NatPowSpec bigZ bigZ⁺ _.
Proof. split; unfold pow, bigZ_pow.
+ apply binary_morphism_proper_back. intros ?? [_ E1] n m [_ E2]. red_sig. now rewrite E1, E2.
+ intros x _. apply BigZ.pow_0_r.
+ intros x _ n ?. rewrite BigZ.add_1_l. apply BigZ.pow_succ_r. now destruct (_ : n ∊ bigZ⁺).
Qed.

Instance bigZ_powN: Pow BigZ.t BigN.t := λ x n, x ^ ('n).

Instance: NatPowSpec bigZ bigN _.
Proof. pose proof nat_int.to_semiring_nonneg_mor : SemiRing_Morphism bigN bigZ⁺ (').
  split; unfold pow, bigZ_powN.
+ apply binary_morphism_proper_back. intros x y [_ E] m n E2. red_sig.
  rewrite E. now rewrite (bigN $ E2).
+ exact (nat_pow_0 (N:=bigZ⁺)).
+ intros x _ n _.
  replace (cast bigN bigZ (1+n)) with (1 + (cast bigN bigZ n))
    by now preserves_simplify (cast bigN bigZ).
  exact (nat_pow_S (N:=bigZ⁺) _ _).
Qed.

Instance fastZ_shiftl: ShiftL BigZ.t BigN.t := λ x n, BigZ.shiftl x ('n).

Instance: ShiftLSpec bigZ bigN _.
Proof.
  apply shiftl.shiftl_spec_from_nat_pow. intros ? _ ? _; exact _.
  intros. rewrite (commutativity (.*.) _ _). apply BigZ.shiftl_mul_pow2.
  change (0 ≤ cast bigN bigZ n).
  now apply nat_int.to_semiring_nonneg.
Qed.
