Require Import
  abstract_algebra theory.setoids.

Local Existing Instance injective_mor.
Local Existing Instance surjective_mor.
Local Existing Instance surjective_closed.

Local Open Scope mc_fun_scope.

(*
Lemma injective_compose_cancel `{Equiv A} `{Equiv B} `{Equiv C} (f : B → C)
    `{!Injective f} `{!Setoid_Morphism (g : A → B)} `{!Setoid_Morphism (h : A → B)} :
  f ∘ g = f ∘ h → g = h.
Proof.
  pose proof (setoidmor_a g).
  intros E. apply setoids.ext_equiv_applied_iff. intros x.
  apply (injective f). now apply E.
Qed.
*)

Section contents.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} (f: X ⇀ Y) `{!Inverse f}.

  Lemma surjective_applied `{!Surjective X Y f} x `{x ∊ Y} : f (f⁻¹ x) = x.
  Proof. apply (surjective f x). now red_sig. Qed.

  Context `{!Bijective X Y f}.

  Instance inverse_mor : Morphism (Y ⇒ X) f⁻¹.
  Proof.
    intros x y E. unfold_sigs. red_sig. apply (injective f _ _).
    now rewrite !(Y $ surjective_applied _).
  Qed.

  Lemma bijective_cancel_left x `{x ∊ X} y `{y ∊ Y} : f x = y → x = f⁻¹ y.
  Proof. intros E. apply (injective f _ _). now rewrite (Y $ surjective_applied _). Qed.

  Lemma bijective_cancel_inverse_left x `{x ∊ Y} y `{y ∊ X} : f⁻¹ x = y → x = f y.
  Proof. intros E. rewrite_on X <- E. subsymmetry. exact (surjective_applied _). Qed.

  Lemma bijective_applied x `{x ∊ X} : f⁻¹ (f x) = x.
  Proof. subsymmetry. now apply (bijective_cancel_left _ _). Qed.

  Lemma bijective : f⁻¹ ∘ f = id. (* a.k.a. "split-mono" *)
  Proof. intros x y E. unfold_sigs. red_sig. subtransitivity x. exact (bijective_applied x). Qed.
End contents.

Hint Extern 5 (Morphism _ (_⁻¹)) => eapply @inverse_mor : typeclass_instances.

(*

Lemma injective_ne `{Equiv A} `{Equiv B} `(f : A → B) `{!Injective f} x y :
  x ≠ y → f x ≠ f y.
Proof. intros E1 E2. apply E1. now apply (injective f). Qed.
*)

Instance id_inverse `{X:Subset} {Y} : Inverse (id : X ⇀ Y) := (id : Y ⇀ X).

Instance id_injective `{Equiv} `{!Setoid X} `{!Setoid Y} `{!SubsetOf X Y} : Injective X Y id.
Proof. split; try apply _. easy. Qed.
Instance id_surjective `{Equiv} `{!Setoid X} : Surjective X X id.
Proof. split; try apply _. change (Morphism (X ⇒ X) id). apply _. Qed.
Instance id_bijective `{Equiv} `{!Setoid X} : Bijective X X id := {}.

Section compositions.
  Context `{X:Subset} `{Y:Subset} `{Z:Subset}.
  Context (g: X ⇀ Y) (f: Y ⇀ Z) `{!Inverse f} `{!Inverse g}.

  Instance compose_inverse: Inverse (f ∘ g) := g⁻¹ ∘ f⁻¹.

  Context `{Setoid _ (S:=X)} `{Setoid _ (S:=Y)} `{Setoid _ (S:=Z)}.
  Instance compose_injective: Injective Y Z f → Injective X Y g → Injective X Z (f ∘ g).
  Proof. split; try apply _. intros ?? ?? ?. apply (injective g _ _). now apply (injective f _ _). Qed.

  Instance compose_surjective: Surjective Y Z f → Surjective X Y g → Surjective X Z (f ∘ g).
  Proof. intros.
    split; try apply _.
    intros x y E. unfold_sigs. change ((Z,=)%signature (f (g (g⁻¹ (f⁻¹ x))))  y).
    red_sig. rewrite_on Z <- E. rewrite (Y $ surjective_applied g _). exact (surjective_applied _ _).
    intros x ?. change (g⁻¹ (f⁻¹ x) ∊ X). apply _.
  Qed.
  Instance compose_bijective: Bijective Y Z f → Bijective X Y g → Bijective X Z (f ∘ g) := {}.
End compositions.

Hint Extern 4 (Inverse        (_ ∘ _)) => class_apply @compose_inverse    : typeclass_instances.
Hint Extern 4 (Injective  _ _ (_ ∘ _)) => class_apply @compose_injective  : typeclass_instances.
Hint Extern 4 (Surjective _ _ (_ ∘ _)) => class_apply @compose_surjective : typeclass_instances.
Hint Extern 4 (Bijective  _ _ (_ ∘ _)) => class_apply @compose_bijective  : typeclass_instances.

Lemma alt_Build_Injective `{Setoid (S:=X)} `{Setoid (S:=Y)} (f: X ⇀ Y) `{!Inverse f} :
  Morphism (X ⇒ Y) f → Morphism (Y ⇒ X) f⁻¹ → f⁻¹ ∘ f = id → Injective X Y f.
Proof.
  intros ?? E. split; try apply _. intros x ? y ? F.
  rewrite <- (E _ _ (X $ subreflexivity x)).
  rewrite <- (E _ _ (X $ subreflexivity y)).
  unfold compose. now rewrite_on Y -> F.
Qed.

Lemma alt_Build_Bijective `{Setoid (S:=X)} `{Setoid (S:=Y)} (f: X ⇀ Y) `{!Inverse f} :
  Morphism (X ⇒ Y) f → Morphism (Y ⇒ X) f⁻¹ → f⁻¹ ∘ f = id → f ∘ f⁻¹ = id → Bijective X Y f.
Proof.
  intros. split.
   now apply (alt_Build_Injective f).
  split; auto. apply _.
Qed.

Definition inverse_inverse `{Inverse (f:=f)} : Inverse f⁻¹ := f.
Hint Extern 4 (Inverse (_ ⁻¹)) => eapply @inverse_inverse : typeclass_instances.

Lemma flip_bijection `{Setoid (S:=X)} `{Setoid (S:=Y)} (f: X ⇀ Y) `{!Inverse f} `{!Bijective X Y f} : Bijective Y X f⁻¹.
Proof. apply alt_Build_Bijective; try apply _. apply (surjective f). apply (bijective f). Qed.
Hint Extern 4 (Bijective _ _ _⁻¹) => eapply @flip_bijection : typeclass_instances.

Lemma inverse_involutive `{X:Subset} `{Y:Subset} (f : X ⇀ Y) `{!Inverse f} : (f⁻¹)⁻¹ ≡ f.
Proof. reflexivity. Qed.

(* This second version is strictly for manual application. *)
Lemma flip_bijection_back `{Setoid (S:=X)} `{Setoid (S:=Y)} (f: X ⇀ Y) `{!Inverse f} :
  Bijective Y X (f⁻¹) → Bijective X Y f.
Proof. intro. apply (_: Bijective X Y (f⁻¹⁻¹)). Qed.

Lemma injective_proper : Find_Proper_Signature (@Injective) 0
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)}, Proper ((@equiv (X ⇀ Y) _) ==> impl) (Injective X Y)).
Proof. red. intros. intros f g E ?. assert (Morphism (X ⇒ Y) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros x ? y ? E2. apply (injective f _ _).
  subtransitivity (g x). now apply extensionally_equal.
  subtransitivity (g y). apply extensionally_equal; try easy. now symmetry.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Injective) 0 _) => eexact injective_proper : typeclass_instances.

(*
Instance injective_proper `{Equiv A} `{Equiv B} : Proper ((=) ==> (=)) (@Injective A B _ _).
Proof.
  assert (∀ f g : A → B, f = g → Injective f → Injective g) as aux.
   intros f g E ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f). split.
    intros x y ?. apply (injective f).
    now rewrite (ext_equiv_applied E x), (ext_equiv_applied E y).
   rewrite <-E; apply _.
  intros f g; split; intros; eapply aux; eauto.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g). now symmetry.
Qed.

Lemma surjective_proper `{Equiv A} `{Equiv B} (f g : A → B) `{!Inverse f} `{!Inverse g} `{!Surjective g} :
  f = g → f⁻¹ = g⁻¹  → Surjective f.
Proof.
  intros E1 E2.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g).
  split.
   intros ? ? E3. change (f  (f⁻¹ x) = y).
   rewrite <-E3, (ext_equiv_applied E1 _), (ext_equiv_applied E2 _).
   now apply surjective_applied.
  rewrite E1; apply _.
Qed.

Ltac setoid_inject :=
  match goal with
  | E : _ = ?f _ |- _ => apply (injective f _ _) in E
  | E : ?f _ = _ |- _ => apply (injective f _ _) in E
  | E : _ ≡ _ |-  ?G => change (id G); injection E; clear E; intros; unfold id at 1 
  end.
*)
