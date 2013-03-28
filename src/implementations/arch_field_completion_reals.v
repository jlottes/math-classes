Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.fields theory.rationals orders.rationals
  metric.metric_spaces metric.prelength metric.rationals metric.product cauchy_completion
  metric.archimedean_ordered_field uniformly_continuous_extension
  orders.affinely_extended_field stdlib_field misc.quote
  the_integers nonneg_integers_naturals theory.naturals
  the_ae_rationals.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Local Infix "==>" := UniformlyContinuous (at level 55, right associativity) : mc_scope.

(*
Section ufm_cont_binary.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}.

  Lemma ufm_cont_const y `{y ∊ Y} : (X ==> Y) (λ _, y).
  Proof. split; try apply _. intros ???. now red_sig.
    intros. exists_sub infty. now intros.
  Qed.

  Context (f:X ⇀ Y ⇀ Z).

  Instance: (X==>Y==>Z) f → Morphism (X ⇒ Y ⇒ Z) f.
  Proof. rewrite <-(_ : SubsetOf (X ⇒ Y ==> Z) (X ⇒ Y ⇒ Z)). apply _. Qed.

  Lemma ufm_cont_1 `{!(X==>Y==>Z) f} x `{x ∊ X} : (Y==>Z) (f x).
  Proof _ : (f x) ∊ (Y==>Z).

  Lemma ufm_cont_1_alt `{!(X==>Y==>Z) f} x `{x ∊ X} : (Y==>Z) (λ y, f x y).
  Proof _ : (f x) ∊ (Y==>Z).

  Lemma ufm_cont_2 `{!(X==>Y==>Z) f} y `{y ∊ Y} : (X==>Z) (λ x, f x y).
  Proof. split; try apply _. intros ε ?.
    destruct (uniform_continuity (Y:=Y==>Z) f ε) as [δ[? Cf]].
    exists_sub δ. intros x₁ ? x₂ ? E.
    destruct (Cf x₁ _ x₂ _ E) as [_ P]. now apply P.
  Qed.

(*
  Context `{MetricSpace (X:=W)}.

  Lemma ufm_cont_compose_2 (g:W ⇀ X) (h:W ⇀ Y) {cf:(X-->Y-->Z) f} {cg:(W-->X) g} {ch:(W-->Y) h}
    : (W-->Z) (λ x, f (g x) (h x)).
  Proof. split; try apply _.
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros ε ?.
    destruct (uniform_continuity (Y:=Y-->Z) f ε) as [δ[? Cf]].
*)

End ufm_cont_binary.

Hint Extern 4 ((_ --> _) (λ x, _)) => eapply ufm_cont_const : typeclass_instances.
Hint Extern 8 ((_ --> _) (?f _)) => eapply ufm_cont_1 : typeclass_instances.
Hint Extern 4 ((_ --> _) (λ x, ?f _ x)) => eapply ufm_cont_1 : typeclass_instances.
Hint Extern 4 ((_ --> _) (λ x, ?f x _)) => eapply ufm_cont_2 : typeclass_instances.
*)

Section contents.
  Context `{ArchimedeanOrderedField (F:=F)}.
  Context `{R:Subset} {Re:Equiv R} {Rball:Ball R} {Rlimit:Limit R}.
  Context `{!ToCompletion F R} `{!Completion F R}.

  Notation "#" := (to_completion F R).

  Existing Instance arch_ord_field_negate_isometry.
  Existing Instance arch_ord_field_plus_ufm_cont.

  (* C for Cauchy / completion *)
  Instance Creals_zero   : Zero   R := # 0.
  Instance Creals_one    : One    R := # 1.
  Instance Creals_negate : Negate R := ufm_completion_map (-).
  Instance Creals_plus   : Plus   R := curry (ufm_completion_map (uncurry (+))).

  Instance: Morphism (R ⇒ R) (-) := _ : Morphism (R ⇒ R) (ufm_completion_map (-)).
  Instance: (R==>R) (-) := _ : (R==>R) (ufm_completion_map (-)).
  Instance: Closed (R ⇀ R) (-) := morphism_closed _.
  Hint Extern 5 (- _ ∊ _) => eapply (_ : Closed (R ⇀ R) (-)) : typeclass_instances.

  Instance: Morphism (R ⇒ R ⇒ R) (+). Proof. unfold plus, Creals_plus. apply _. Qed.
  Instance: Closed (R ⇀ R ⇀ R) (+) := binary_morphism_closed _.
  Hint Extern 5 (_ + _ ∊ _) => eapply (_ : Closed (R ⇀ R ⇀ R) (+)) : typeclass_instances.

  Ltac funs_equal z := pattern z; match goal with |- (fun x => (@?a x) = (@?b x)) z => 
      change (a z = b z); cut (a = b); [intro E; apply E; now red_sig|]; clear dependent z
  end.

  Let preserves_negate x `{x ∊ F} : # (-x) = - # x.
  Proof. subsymmetry. funs_equal x. exact (ufm_completion_map_extends (-)). Qed.

  Let preserves_plus x `{x ∊ F} y `{y ∊ F} : # (x+y) = # x + # y.
  Proof.
    destruct ( ufm_completion_map_extends (CX:=R*R) (uncurry (+) : F*F ⇀ F ) (x,y) (x,y)
      (_:Proper (F*F,=) (x,y)) ).
    subsymmetry.
  Qed.

  (*
  Instance: Commutative (+) R.
  Proof. intros x ? y ?.
    funs_equal x. apply (ufm_cont_equal_on_dense_image_applied # _ _). intros x ?.
    funs_equal y. apply (ufm_cont_equal_on_dense_image_applied # _ _). intros y ?.
    now rewrite <-2!(_ $ preserves_plus _ _), (_ $ commutativity (+) _ _).
  Qed.
  *)

  (*
  Ltac build_ufm_cont f :=
    match f with
    | (fun x => x) => constr:(id_uniformly_cont : (_ --> _) f)
    | (fun x => ?g (@?a x) (@?b x)) =>
        let ac := build_ufm_cont a in
        let bc := build_ufm_cont b in
    | (fun x => ?g (@?a x)) =>
        let ac := build_ufm_cont a in
        constr:(compose_uniformly_cont g a (cg:=ac) : (_ --> _) f)
    | _ => constr:(_ : (_ --> _) f)
    end.

  Instance: Associative (+) R.
  Proof. intros x ? y ? z ?. funs_equal z.
    let p := build_ufm_cont (λ y:R, --x) in
      let t := type of p in idtac p; idtac t.
idtac p.
    match goal with |- ?f = _ => idtac f; build_ufm_cont f end.
      match f with (fun x => ?g (@?a x) (@?b x)) => idtac a end
    end.
(fun x => (@?a x) = (@?b x)) z => 
    pattern z; match goal with |- (fun x => (@?a x) = (@?b x)) z => 
      change (a z = b z); cut (a = b); [intro E; apply E; now red_sig|]; clear dependent z
    end.
    match constr:(fun x => x + x) with (fun x => (@?a x)) => idtac a end.
    match goal with |- ?f = ?g =>
      match f with (fun x => (@?a x)) z => idtac z end
    end.
 idtac f end.
 pattern z.
  *)

End contents.
