Require Import
  abstract_algebra interfaces.naturals interfaces.orders interfaces.additional_operations
  theory.setoids theory.strong_setoids theory.rings orders.semirings theory.naturals.
Require Import
  stdlib_ring.

Lemma nat_pow_closed `{SemiRing (R:=R)} `{Naturals (N:=N)} {pw} {spec:NatPowSpec R N pw} :
  Closed (R ⇀ N ⇀ R) (^).
Proof _.

(* choose subsets R and N by looking for a NatPowSpec instance *)
Hint Extern 5 (@pow ?A ?B ?pw _ _ ∊ _) =>
  let X := fresh "X" in let Y := fresh "Y" in
  evar (X:@Subset A); evar (Y:@Subset B);
  let X' := eval unfold X in X in clear X;
  let Y' := eval unfold Y in Y in clear Y;
  let spec := constr:(_ : NatPowSpec X' Y' pw) in
  instantiate; eapply (@nat_pow_closed _ _ _ _ _ _ X' _ _ _ _ _ _ _ Y')
: typeclass_instances.

(* * Properties of Nat Pow *)
Section nat_pow_properties.
Context `{SemiRing (R:=R)} `{Naturals (N:=N)} `{UnEq _} `{!DenialInequality N} `{!NatPowSpec R N pw}.

(*
Global Instance: Proper ((=) ==> (=) ==> (=)) (^) | 0.
Proof nat_pow_proper.

Global Instance nat_pow_mor_1: ∀ x : A, Setoid_Morphism (x^) | 0.
Proof. split; try apply _. Qed.

Global Instance nat_pow_mor_2: ∀ n : B, Setoid_Morphism (^n) | 0.
Proof. split; try apply _. solve_proper. Qed.
*)

Lemma nat_pow_base_0 n `{n ∊ N ₀} : 0 ^ n = 0.
Proof.
  match goal with H : n ∊ N ₀ |- _ => destruct H as [? nz]; red in nz; revert nz end.
  nat_induction n E.
  + rewrite (denial_inequality _ _). intros E. now destruct E.
  + intros. rewrite (R $ nat_pow_S _ _). exact (mult_0_l _).
Qed.

Instance nat_pow_1: RightIdentity (^) 1 R.
Proof.
  intros ??. rewrite_on N <- (plus_0_r 1).
  rewrite (R $ nat_pow_S _ _), (R $ nat_pow_0 _). exact (mult_1_r _).
Qed.

Lemma nat_pow_2 x `{x ∊ R} : x ^ 2 = x * x.
Proof. now rewrite (R $ nat_pow_S _ _), (R $ nat_pow_1 x _). Qed.

Lemma nat_pow_3 x `{x ∊ R} : x ^ 3 = x * (x * x).
Proof. now rewrite (R $ nat_pow_S _ _), (R $ nat_pow_2 x). Qed.

Lemma nat_pow_4 x `{x ∊ R} : x ^ 4 = x * (x * (x * x)).
Proof. now rewrite (R $ nat_pow_S _ _), (R $ nat_pow_3 x). Qed.

Instance nat_pow_base_1: LeftAbsorb (^) 1 N.
Proof. intros n ?. nat_induction n E.
+ exact (nat_pow_0 1).
+ rewrite (R $ nat_pow_S _ _), (R $ E). exact (mult_1_l _).
Qed.

Lemma nat_pow_exp_plus x `{x ∊ R} n `{n ∊ N} m `{m ∊ N} :
  x ^ (n + m) = x ^ n * x ^ m.
Proof. nat_induction n E.
+ now rewrite (R $ nat_pow_0 _), (R $ mult_1_l _), (N $ plus_0_l _).
+ rewrite <- (N $ associativity (+) _ _ _), 2!(R $ nat_pow_S _ _), (R $ E).
  exact (associativity (.*.) _ _ _).
Qed.

Lemma nat_pow_exp_mult x `{x ∊ R} n `{n ∊ N} m `{m ∊ N} :
  x ^ (n * m) = (x ^ n) ^ m.
Proof. nat_induction m E.
+ now rewrite (N $ mult_0_r _), ?(R $ nat_pow_0 _).
+ rewrite (R $ nat_pow_S _ _), <- (R $ E).
  rewrite (N $ plus_mult_distr_l _ _ _), (N $ mult_1_r _).
  exact (nat_pow_exp_plus _ _ _).
Qed.

Ltac prove_closed := let E := fresh "E" in intros x ? n ?; nat_induction n E;
  [ rewrite (R $ nat_pow_0 _)
  | rewrite (R $ nat_pow_S _ _)
  ]; apply _.

Existing Instance closed_binary.

Instance nat_pow_nonzero `{UnEq A} `{!InequalitySetoid R} `{!Closed (R ₀ ⇀ R ₀ ⇀ R ₀) (.*.)} `{1 ∊ R ₀} :
  Closed (R ₀ ⇀ N ⇀ R ₀) (^).
Proof. prove_closed. Qed.

Lemma nat_pow_strong `{UnEq _} `{!StrongSetoid R} `{UnEq _} `{!DenialInequality N} `{!Strong_Binary_Morphism R R R (.*.)} :
  Strong_Binary_Morphism R N R (^).
Proof. split; try apply _.
 rewrite strong_ext_equiv_2.
 intros x ? y ? n nel m mel. destruct (decide_sub (=) n m) as [E|?].
  * intro IE. left. rewrite <- (N $ E) in IE. revert IE. nat_induction n IH.
    - rewrite ?(R $ nat_pow_0 _). intro Q. contradict Q. now rewrite (tight_apart 1 1).
    - rewrite ?(R $ nat_pow_S _ n). intro IE. destruct (strong_binary_extensionality (.*.) IE); intuition.
  * right. now rewrite (denial_inequality n m).
Qed.

(*
Instance nat_pow_ne_0 `{UnEq A} `{!StandardUnEq R} `{!NoZeroDivisors R} `{!PropHolds ((1:A) ≠ 0)} :
  Closed (R ₀ ==> N ==> R ₀) (^).
Proof. prove_closed. Qed.
*)

Context `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R} `{1 ∊ R ₀}.

Instance: StrongSetoid R := pseudo_order_setoid.

(*Instance nat_pow_apart_0 : Closed (R ₀ ==> N ==> R ₀) (^). Proof. prove_closed. Qed.*)
Instance nat_pow_nonneg  : Closed (R⁺  ⇀ N ⇀ R⁺ ) (^). Proof. prove_closed. Qed.
Instance nat_pow_pos     : Closed (R₊  ⇀ N ⇀ R₊ ) (^). Proof. prove_closed. Qed.

Lemma nat_pow_ge_1 x `{x ∊ R} n `{n ∊ N} : 1 ≤ x → 1 ≤ x ^ n.
Proof. intro E. nat_induction n F.
+ now rewrite (R $ nat_pow_0 _).
+ rewrite (R $ nat_pow_S _ _). exact (ge_1_mult_compat _ _ E F).
Qed.

End nat_pow_properties.

Arguments nat_pow_1 {_ _ _ _ _ _ R _ _ _ _ _ _ _ N _ _ _ _} _ {_}.
Arguments nat_pow_base_1 {_ _ _ _ _ _ R _ _ _ _ _ _ _ N _ _ _ _} _ {_}.
Hint Extern 5 (RightIdentity (^) _ _) => class_apply @nat_pow_1 : typeclass_instances.
Hint Extern 5 (LeftAbsorb (^) _ _) => class_apply @nat_pow_base_1 : typeclass_instances.
Hint Extern 8 (_ ^ _ ∊ _ ₀) => eapply @nat_pow_nonzero : typeclass_instances.
Hint Extern 8 (_ ^ _ ∊ _⁺) => eapply @nat_pow_nonneg : typeclass_instances.
Hint Extern 8 (_ ^ _ ∊ _₊) => eapply @nat_pow_pos : typeclass_instances.

Section nat_pow_properties_comm.
Context `{CommutativeSemiRing (R:=R)} `{Naturals (N:=N)} `{!NatPowSpec R N pw}.

Add Ring R : (stdlib_semiring_theory R).

Lemma nat_pow_base_mult x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} :
  (x * y) ^ n = x ^ n * y ^ n.
Proof. nat_induction n E.
+ now rewrite ?(R $ nat_pow_0 _), (R $ mult_1_l _).
+ rewrite ?(R $ nat_pow_S _ _), (R $ E). subring R.
Qed.

End nat_pow_properties_comm.

Section preservation.
  Context `{Naturals (N:=N)} `{SemiRing (R:=R1)} `{!NatPowSpec R1 N pw1}
                             `{SemiRing (R:=R2)} `{!NatPowSpec R2 N pw2}.
  Context {f : R1 ⇀ R2} `{!SemiRing_Morphism R1 R2 f}.

  Lemma preserves_nat_pow x `{x ∊ R1} n `{n ∊ N} :  f (x ^ n) = (f x) ^ n.
  Proof. nat_induction n E.
  + rewrite (R1 $ nat_pow_0 _), (R2 $ nat_pow_0 _). exact preserves_1.
  + rewrite (R1 $ nat_pow_S _ _), (R2 $ nat_pow_S _ _), <- (R2 $ E). exact (preserves_mult _ _).
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing (R:=R)} `{Naturals (N:=N1)} `{!NatPowSpec R N1 pw1}
                             `{Naturals (N:=N2)} `{!NatPowSpec R N2 pw2}.
  Context {f : N1 ⇀ N2} `{!SemiRing_Morphism N1 N2 f}.

  Lemma preserves_nat_pow_exp x `{x ∊ R} n `{n ∊ N1} : x ^ (f n) = x ^ n.
  Proof. nat_induction n E.
  + now rewrite (N2 $ preserves_0), !(R $ nat_pow_0 _).
  + rewrite (N2 $ preserves_plus _ _), (N2 $ preserves_1).
    rewrite !(R $ nat_pow_S _ _). now rewrite_on R -> E.
  Qed.
End exp_preservation.

Instance nat_pow_peano {A} `{One A} `{Mult A} : Pow A nat :=
  fix nat_pow_rec (x: A) (n : nat) : A := match n with
  | 0 => 1
  | S n => x * nat_pow_rec x n
  end.

Instance: ∀ `{SemiRing (R:=R)}, NatPowSpec R (every nat) nat_pow_peano.
Proof. intros. assert (Morphism (R ⇒ every nat ⇒ R) (^)).
+ apply binary_morphism_proper_back.
  intros ?? E1 n m [_ E2]. lazy in E2. rewrite <- E2. clear dependent m.
  induction n.
  - change ( (R,=)%signature 1 1 ). now red_sig.
  - change ( (R,=)%signature (x * x ^ n) (y * y ^ n) ).
    now apply (_ : Proper ((R,=) ==> (R,=) ==> (R,=)) (.*.)).
+ pose proof (binary_morphism_closed (^)). pose proof @closed_binary. now split.
Qed.

(* Very slow default implementation by translation into Peano *)

Section nat_pow_default.
  Context `{SemiRing A (R:=R)} `{Naturals B (N:=N)}.

  Instance nat_pow_default: Pow A B := λ x n, x ^ (naturals_to_semiring N (every nat) n).
  Global Instance nat_pow_default_spec: NatPowSpec R N nat_pow_default.
  Proof. split; unfold pow, nat_pow_default.
  + apply binary_morphism_proper_back.
    intros ?? E1 ?? E2. unfold_sigs. red_sig. now rewrite (R $ E1), (N $ E2).
  + intros x ?. now rewrite (every nat $ preserves_0).
  + intros x ? n ?. now rewrite (every nat $ preserves_plus _ _), (every nat $ preserves_1).
  Qed.
End nat_pow_default.

Typeclasses Opaque nat_pow_default.
