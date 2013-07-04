Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.fields theory.rationals
  orders.affinely_extended_field stdlib_field
  orders.minmax orders.lattices
  metric.metric_spaces metric.maps prelength
  theory.products metric.products.
Require Export
  cauchy_completion uniform_continuity.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).


(** A complete metric space is the completion of any of its
    dense subsets, including itself. *)

Hint Extern 10 (ToCompletion ?X ?Y) => eexact (id : X ⇀ Y) : typeclass_instances.

Section complete_dense_completion.
  Context `(X:Subset) (Y:Subset) `{CompleteMetricSpace _ (X:=Y)} `{!Dense (X:=Y) X}.

  Let sub := _ : X ⊆ Y.
  Instance: MetricSpace X := sub_metric_space.
  Instance: Morphism (X ⇒ Y) (id:X ⇀ Y) := _.

  Instance complete_dense_subset_completion: Completion X Y.
  Proof. split; unfold to_completion; try apply _.
    split; try apply _. rewrite (image_id X). exact dense_def.
  Qed.
End complete_dense_completion.

Hint Extern 10 (Completion _ _) => eapply @complete_dense_subset_completion : typeclass_instances.



(** The universal property of the completion of a metric space. *)

Section ufm_lift_to_completion.
  Context `{Completion (X:=X) (X':=Y)} `{CompleteMetricSpace (X:=Z)}.
  Notation "#" := (to_completion X Y).

  Definition ufm_lift_to_completion : (X ==> Z) ⇀ (Y ==> Z)
    := ufm_cont_extension # (id:Z ⇀ Z) (id:(X ==> Z) ⇀ (X ==> Z)).

  Hint Unfold ufm_lift_to_completion : typeclass_instances.

  Instance ufm_lift_to_completion_isometry:
    Isometry (X ==> Z) (Y ==> Z) ufm_lift_to_completion
  := _.

  Context (f:X ⇀ Z).
  Notation f' := (ufm_lift_to_completion f).

  Section ufm.
    Context `{!UniformlyContinuous X Z f}.

    Instance ufm_lift_to_completion_mor : Morphism (Y ⇒ Z) f' := _.
    Instance ufm_lift_to_completion_cont : UniformlyContinuous Y Z f' := _.

    Lemma ufm_lift_to_completion_extends : f' ∘ # = f.
    Proof ufm_cont_ext_extends_2 _ id (id:(X ==> Z) ⇀ (X ==> Z)) _.

    Lemma ufm_lift_to_completion_unique (g:Y ⇀ Z) `{!UniformlyContinuous Y Z g}
    : g ∘ # = f → g = f'.
    Proof ufm_cont_ext_unique_2 (to_completion X Y) id (id:(X ==> Z) ⇀ (X ==> Z)) _ _.
  End ufm.

  Instance ufm_lift_to_completion_cont_strong `{!StronglyUniformlyContinuous X Z f}
    : StronglyUniformlyContinuous Y Z f'.
  Proof. unfold ufm_lift_to_completion.
    now apply (ufm_cont_ext_strong # id (id:(X ==> Z) ⇀ (X ==> Z)) 0 f f).
  Qed.

  Instance ufm_lift_to_completion_iso `{!Isometry X Z f} : Isometry Y Z f'.
  Proof. apply ( extend_isometry f' #⁺¹(X) ).
    split. exact (sub_metric_space (X:=Y)). apply _.
      rewrite <-(_:SubsetOf (Y ⇒ Z) (#⁺¹(X) ⇒ Z)). apply _.
    intros ε ? x' [?[x[? Ex]]] y' [?[y[? Ey]]].
    rewrite <-(Y $ Ex), <-(Y $ Ey), <-(isometric # _ _ _).
    setoid_rewrite (ufm_lift_to_completion_extends _ _ (_:Proper (X,=) x)).
    setoid_rewrite (ufm_lift_to_completion_extends _ _ (_:Proper (X,=) y)).
    exact (isometric f _ _ _).
  Qed.

End ufm_lift_to_completion.

Hint Extern 2 (Morphism _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_lift_to_completion) => eapply @ufm_lift_to_completion_isometry : typeclass_instances.
Hint Extern 2 (StronglyUniformlyContinuous _ _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_cont_strong : typeclass_instances.
Hint Extern 2 (Isometry _ _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_iso : typeclass_instances.

(** The map function of the completion monad. *)

Section ufm_completion_map.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.

  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).

  Definition ufm_completion_map : (X ==> Y) ⇀ (CX ==> CY)
    := ufm_lift_to_completion ∘ (h ∘).

  Hint Unfold ufm_completion_map : typeclass_instances.

  Instance ufm_completion_map_isometry:
    Isometry (X ==> Y) (CX ==> CY) ufm_completion_map := _.

  Context (f:X ⇀ Y).
  Notation f' := (ufm_completion_map f).

  Lemma ufm_completion_map_cont_strong `{!StronglyUniformlyContinuous X Y f}
  : StronglyUniformlyContinuous CX CY f'.
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Lemma ufm_completion_map_iso `{!Isometry X Y f} : Isometry CX CY f'.
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Context `{!UniformlyContinuous X Y f}.

  Instance ufm_completion_map_mor : Morphism (CX ⇒ CY) f'.
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Instance ufm_completion_map_cont : UniformlyContinuous CX CY f'.
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Lemma ufm_completion_map_extends : f' ∘ g = h ∘ f.
  Proof ufm_lift_to_completion_extends _.

  Lemma ufm_completion_map_unique (cf:CX ⇀ CY) `{!UniformlyContinuous CX CY cf}
  : cf ∘ g = h ∘ f → cf = f'.
  Proof ufm_lift_to_completion_unique _ _.

End ufm_completion_map.

Hint Extern 2 (Morphism _ (ufm_completion_map _)) => eapply @ufm_completion_map_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_completion_map _)) => eapply @ufm_completion_map_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_completion_map) => eapply @ufm_completion_map_isometry : typeclass_instances.
Hint Extern 2 (StronglyUniformlyContinuous _ _ (ufm_completion_map _)) => eapply @ufm_completion_map_cont_strong : typeclass_instances.
Hint Extern 2 (Isometry _ _ (ufm_completion_map _)) => eapply @ufm_completion_map_iso : typeclass_instances.

Local Hint Extern 5 (?x ∊ ?X) => match goal with
  H : x ∊ ?S ?q |- _ => eapply (_: SubsetOf (S q) X)
end : typeclass_instances.
Local Hint Extern 5 (Cauchy ?S) => eexact (_ : S ∊ (CauchyFamilies _)) : typeclass_instances.

(** The space of uniformly continuous functions into a complete space
    is itself compelte. *)

Section complete_ufm_fun_space.
  Context `{MetricSpace (X:=X)} `{CompleteMetricSpace (X:=Y)}.

  Notation C := (CauchyFamilies (X==>Y)).
  Notation m := (to_completion (X==>Y) C).

  Instance ufm_fun_space_limit : Limit (X==>Y)
    := ufm_cont_extension (id:X ⇀ X) (id:Y ⇀ Y) m.

  Instance ufm_fun_space_complete : CompleteMetricSpace (X==>Y).
  Proof. split; unfold limit, ufm_fun_space_limit; try apply _.
    intros S ? p ? f ?. pose proof _ : f ∊ X==>Y as Cf. red in Cf.
    setoid_rewrite <-(ufm_cont_ext_extends id id m p S f).
    subsymmetry. exact (family_const_dist _ _ _).
  Qed.
End complete_ufm_fun_space.
Hint Extern 2 (Limit (_ ==> _)) => eapply @ufm_fun_space_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (_ ==> _)) => eapply @ufm_fun_space_complete : typeclass_instances.

(** The product of complete spaces is complete. *)

Section complete_prod_space.
  Context `{CompleteMetricSpace (X:=X)} `{CompleteMetricSpace (X:=Y)}.

  Notation C := (CauchyFamilies (X * Y)).

  Notation fst' := (ufm_lift_to_completion (X:=X*Y) (Y:=C) fst).
  Notation snd' := (ufm_lift_to_completion (X:=X*Y) (Y:=C) snd).

  Instance prod_space_limit : Limit (X * Y) := λ S, (fst' S, snd' S).

  Notation g := (to_completion (X * Y) C).

  Instance prod_space_complete : CompleteMetricSpace (X*Y).
  Proof. split; unfold limit, prod_space_limit; try apply _.
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros S ?. intros ?? x ?.
    apply (ball_closed (X:=X*Y) _ _ _). intros ε ?.
    destruct (uniform_continuity fst' (ε/2)) as [a[el C1]].
    destruct (uniform_continuity snd' (ε/2)) as [b[el' C2]].
    ae_rat_set_min c a b Ea Eb. ae_rat_set_min δ c (ε/2) Ec E.
    pose proof (ae_pos_finite_bound δ _ E).
    destruct (cauchy_family_inhabited (S:=S) δ) as [y ?].
    assert (p+ε/2+ε/2 ≤ p+ε) as Ep by (apply (eq_le _ _); subfield Q).
    apply (ball_weaken_le (X:=X*Y) (p+ε/2+ε/2) _ _); trivial; try apply _.
    apply (ball_triangle (X:=X*Y) _ _ _ (fst' (g y), snd' (g y)) _).
    * setoid_rewrite (ufm_lift_to_completion_extends (X:=X*Y) (Y:=C) fst y y (_:Proper (X*Y,=) y)).
      setoid_rewrite (ufm_lift_to_completion_extends (X:=X*Y) (Y:=C) snd y y (_:Proper (X*Y,=) y)).
      apply (ball_weaken_le (X:=X*Y) (p+δ) _ _); trivial; try apply _.
      apply (cauchy_family_def (X:=X*Y) _ _ _). now destruct y.
      now apply (order_preserving (p+) _ _).
    * split; simpl.
      - apply (C1 _ _ _ _). apply (ball_weaken_le δ _ _); try apply _.
        subsymmetry. apply (family_const_dist _ _ _).
        apply (subtransitivity (S:=Q∞)) with c; trivial; apply _.
      - apply (C2 _ _ _ _). apply (ball_weaken_le δ _ _); try apply _.
        subsymmetry. apply (family_const_dist _ _ _).
        apply (subtransitivity (S:=Q∞)) with c; trivial; apply _.
  Qed.
End complete_prod_space.
Hint Extern 2 (Limit (prod_subset _ _)) => eapply @prod_space_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (prod_subset _ _)) => eapply @prod_space_complete : typeclass_instances.

(** The product of completions is a completion. *)

Section prod_space_completion.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.
  Hint Extern 0 AmbientSpace => eexact CX : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact CY  : typeclass_instances.
  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).

  Instance to_prod_space_completion : ToCompletion (X*Y) (CX*CY)
    := prod_map g h.

  Instance prod_space_completion : Completion (X*Y) (CX*CY).
  Proof. split; unfold to_completion, to_prod_space_completion; try apply _.
    split; try apply _.
    intros ??????. split; intros [??].
      split; simpl. now rewrite <-(isometric g _ _ _). now rewrite <-(isometric h _ _ _).
      split. now rewrite (isometric g _ _ _). now rewrite (isometric h _ _ _).
  Qed.

End prod_space_completion.
Hint Extern 2 (ToCompletion (_ * _) (_ * _)) => eapply @to_prod_space_completion : typeclass_instances.
Hint Extern 2 (Completion (_ * _) (_ * _)) => eapply @prod_space_completion : typeclass_instances.

(** A map for lifting binary functions to the completed domains and range.
    Not actually that useful: the space (X==>Y==>Z) denotes functions
    with a modulus of continuity for the second argument that may depend on the first.
    Hence currying/uncurrying is a better approach.  *)

Section ufm_completion_map_2.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.
  Context `{Completion (X:=Z) (X':=CZ)}.

  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).
  Notation k := (to_completion Z CZ).

  Definition ufm_completion_map_2 : (X==>Y==>Z) ⇀ (CX==>CY==>CZ)
    := ufm_cont_extension g ufm_completion_map id.

  Hint Unfold ufm_completion_map_2 : typeclass_instances.

  Instance ufm_completion_map_2_isometry:
    Isometry (X==>Y==>Z) (CX==>CY==>CZ) ufm_completion_map_2 := _.

  Context (f:X ⇀ Y ⇀ Z) `{!(X==>Y==>Z)%subset f}.

  Instance: Morphism (X ⇒ Y ⇒ Z) f.
  Proof. rewrite <-(_ : SubsetOf (X ⇒ Y ==> Z) (X ⇒ Y ⇒ Z)). apply _. Qed.

  Instance ufm_completion_map_2_mor : Morphism (CX ⇒ CY ⇒ CZ) (ufm_completion_map_2 f).
  Proof. rewrite <-(_ : SubsetOf (CX ⇒ CY ==> CZ) (CX ⇒ CY ⇒ CZ)). apply _. Qed.

  Instance ufm_completion_map_2_cont : (CX==>CY==>CZ)%subset (ufm_completion_map_2 f) := _.

  Lemma ufm_completion_map_2_extends x `{x ∊ X} y `{y ∊ Y}
    : (ufm_completion_map_2 f) (g x) (h y) = k (f x y).
  Proof. 
    pose proof _ : (f x) ∊ (Y ==> Z) as Cfx. red in Cfx.
    subtransitivity (ufm_completion_map (f x) (h y)).
    + pose proof (ufm_cont_ext_extends_2 g ufm_completion_map id f x x (_:Proper (X,=) x)) as E.
      unfold_sigs. apply (E (h y) (h y)). now red_sig.
    + change ((ufm_completion_map (f x) ∘ h) y = (k ∘ (f x)) y).
      apply (ufm_completion_map_extends _). now red_sig.
  Qed.

(*  Lemma completion_map_unique (cf:CX ⇀ CY) `{!UniformlyContinuous CX CY cf}
  : cf ∘ g = h ∘ f → cf = (completion_map f).
  Proof lift_to_completion_unique _ _. *)

End ufm_completion_map_2.
Hint Extern 2 (Morphism _ (ufm_completion_map_2 _)) => eapply @ufm_completion_map_2_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_completion_map_2 _)) => eapply @ufm_completion_map_2_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_completion_map_2) => eapply @ufm_completion_map_2_isometry : typeclass_instances.

