Require Import
  abstract_algebra interfaces.additional_operations interfaces.orders
  theory.setoids theory.rings orders.orders.

Local Notation δ := kronecker_delta.

Lemma kronecker_delta_el {A B} {X:@set A} {Y:@set B} {Ae:Equiv A} `{!StrongSubDecision X X (=)} `{Zero B} `{One B}
  `{0 ∊ Y} `{1 ∊ Y} i j : δ i j ∊ Y .
Proof. unfold δ. match goal with |- context [ if ?x then _ else _ ] => case x end; intro; apply _. Qed.
Hint Extern 1 (kronecker_delta (Y:=?Y) _ _ ∊ ?Y) => eapply @kronecker_delta_el : typeclass_instances.

Lemma kronecker_delta_shift
  `{Setoid (S:=X₁)} `{!StrongSubDecision X₁ X₁ (=)}
  `{Setoid (S:=X₂)} `{!StrongSubDecision X₂ X₂ (=)}
  `{Setoid (S:=Y)} `{Zero _} `{One _} `{0 ∊ Y} `{1 ∊ Y}
  i₁ `{i₁ ∊ X₁} j₁ `{j₁ ∊ X₁} i₂ `{i₂ ∊ X₂} j₂ `{j₂ ∊ X₂}
  : (i₁ = j₁ ↔ i₂ = j₂) → δ i₁ j₁ = δ i₂ j₂.
Proof. intro P. unfold δ. destruct_dec_sub_strong E1; destruct_dec_sub_strong E2; try easy;
  [ destruct E2 | destruct E1 ]; now apply P.
Qed.

Lemma kronecker_delta_mor `{Setoid (S:=X)} `{Setoid (S:=Y)}
  `{!StrongSubDecision X X (=)} `{Zero _} `{One _} `{0 ∊ Y} `{1 ∊ Y}
  : Morphism (X ⇒ X ⇒ Y) δ .
Proof. apply binary_morphism_proper_back. intros i1 i2 Ei j1 j2 Ej. unfold_sigs. red_sig.
  apply (kronecker_delta_shift _ _ _ _). now rewrite (_ $ Ei), (_ $ Ej).
Qed.
Hint Extern 2 (Morphism _ kronecker_delta) => eapply @kronecker_delta_mor : typeclass_instances.

Lemma kronecker_delta_sym `{Setoid (S:=X)} `{!StrongSubDecision X X (=)} `{Setoid (S:=Y)} `{Zero _} `{One _} `{0 ∊ Y} `{1 ∊ Y}
  i `{i ∊ X} j `{j ∊ X} : δ i j = δ j i.
Proof. apply (kronecker_delta_shift _ _ _ _). split; intro; subsymmetry. Qed.

Lemma kronecker_delta_eq {A B} {X:@set A} {Ae:Equiv A} `{!StrongSubDecision X X (=)} `{Setoid B (S:=Y)} `{Zero B} `{One B} `{1 ∊ Y}
  i `{i ∊ X} j `{j ∊ X} : i = j → δ i j = 1.
Proof. intro. unfold δ.
  match goal with |- context [ if ?x then _ else _ ] => case x end.
  now intro. intuition.
Qed.

Lemma kronecker_delta_diag `{Setoid (S:=X)} `{!StrongSubDecision X X (=)} `{Setoid (S:=Y)} `{Zero _} `{One _} `{1 ∊ Y}
  i `{i ∊ X} : δ i i = 1.
Proof. now apply (kronecker_delta_eq _ _). Qed.

Lemma kronecker_delta_lt `{StrictSetoidOrder (S:=X)} `{Setoid (S:=Y)}
  `{!StrongSubDecision X X (=)} `{Zero _} `{One _} `{0 ∊ Y}
  i `{i ∊ X} j `{j ∊ X} : i < j → δ i j = 0.
Proof. intro E1. unfold δ. destruct_dec_sub_strong E2; [| easy].
  pose proof so_setoid. rewrite (_ $ E2) in E1. now destruct (irreflexivity (<) j).
Qed.

Lemma kronecker_delta_gt `{StrictSetoidOrder (S:=X)} `{Setoid (S:=Y)}
  `{!StrongSubDecision X X (=)} `{Zero _} `{One _} `{0 ∊ Y}
  i `{i ∊ X} j `{j ∊ X} : j < i → δ i j = 0.
Proof. intro E1. unfold δ. destruct_dec_sub_strong E2; [| easy].
  pose proof so_setoid. rewrite (_ $ E2) in E1. now destruct (irreflexivity (<) j).
Qed.

Lemma kronecker_delta_uneq `{InequalitySetoid (S:=X)} `{Setoid (S:=Y)}
  `{!StrongSubDecision X X (=)} `{Zero _} `{One _} `{0 ∊ Y}
  i `{i ∊ X} j `{j ∊ X} : i ≠ j → δ i j = 0.
Proof. intro E1.  unfold δ. destruct_dec_sub_strong E2; [| easy].
  contradict E2. now apply (uneq_ne).
Qed.

Lemma preserves_kronecker_delta
  `{Setoid (S:=X)} `{!StrongSubDecision X X (=)}
  `{R1:set} `{R2:set} (f:R1 ⇀ R2)
  `{SemiRing_Morphism _ _ (R:=R1) (S:=R2) (f:=f)}
  i `{i ∊ X} j `{j ∊ X} : f (δ i j) = δ i j .
Proof. pose proof sringmor_a . pose proof sringmor_b .
  unfold δ. destruct_dec_sub_strong E.
  exact preserves_1. exact preserves_0.
Qed.
