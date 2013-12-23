Require Import
  List
  abstract_algebra interfaces.orders interfaces.rationals.
Require Export
  interfaces.affine_extension the_ae_rationals.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Class Ball A := ball : AQ → A → @set A.

Section contents.
  Context `{X:@set A} {Ae:Equiv X} {Aball:Ball X}.

  Class MetricSpace : Prop :=
  { msp_setoid :>> Setoid X
  ; msp_ball_proper : Proper ((Qfull,=)==>(X,=)==>(X,=)==>impl) ball
  ; msp_nonneg ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X} : ball ε x y → ε ∊ Q∞⁺
  ; msp_ball_inf x `{x ∊ X} y `{y ∊ X} : ball ∞ x y
  ; msp_refl ε `{ε ∊ Q⁺} : Reflexive X (ball ε)
  ; msp_sym  ε `{ε ∊ Q⁺} : Symmetric X (ball ε)
  ; msp_eq x `{x ∊ X} y `{y ∊ X} : ball 0 x y → x = y
  ; msp_triangle ε₁ `{ε₁ ∊ Q⁺} ε₂ `{ε₂ ∊ Q⁺} x `{x ∊ X} y `{y ∊ X} z `{z ∊ X}
      : ball ε₁ x y → ball ε₂ y z → ball (ε₁ + ε₂) x z
  ; msp_closed ε `{ε ∊ Q⁺} x `{x ∊ X} y `{y ∊ X}
      : (∀ `{δ ∊ Q₊}, ball (ε+δ) x y) → ball ε x y
  }.

  Class FinitePoints : Prop :=
    finite_points x `{x ∊ X} y `{y ∊ X} : ∃ `{q ∊ Q⁺}, ball q x y.

  Class LocatedPoints : Prop :=
    located_points_def x `{x ∊ X} y `{y ∊ X} p `{p ∊ Q⁺} q `{q ∊ Q₊} :
      p < q → ball q x y ∨ ¬ ball p x y.

  Class PrelengthSpace : Prop :=
    prelength_msp x `{x ∊ X} y `{y ∊ X} ε `{ε ∊ Q₊} δ₁ `{δ₁ ∊ Q₊} δ₂ `{δ₂ ∊ Q₊}
      : ε < δ₁ + δ₂ → ball ε x y → ∃ `{z ∊ X}, ball δ₁ x z ∧ ball δ₂ z y.

  Class MetricInequality {Aue:UnEq X} : Prop :=
    metric_inequality x `{x ∊ X} y `{y ∊ X} : x ≠ y ↔ ∃ `{q ∊ Q₊}, ¬ ball q x y.

End contents.

Arguments MetricSpace {A} X {_ _}.
Arguments FinitePoints {A} X {_}.
Arguments LocatedPoints {A} X {_}.
Arguments PrelengthSpace {A} X {_}.
Arguments MetricInequality {A} X {_ _}.

(** Operations like closure and interior implicitly refer to some ambient metric space.
    The following typeclass enables this implicit parameter to be resolved predictably. *)
Class AmbientSpace {A} := ambient_space : @set A.
Identity Coercion Id_AmbientSpace_Subset : AmbientSpace >-> set.

Definition B `{X:AmbientSpace} `{Ball X} : Qfull ⇀ X ⇀ every set := λ q x, ball q x ⊓ X .

Definition closure `{X:AmbientSpace} `{Ball X} : set → set := λ S x, x ∊ X ∧
    ∀ `{ε ∊ Q∞₊}, ∃ `{s ∊ S}, ball ε x s.

Definition interior `{X:AmbientSpace} `{Ball X} : set → set := λ S x, x ∊ S ∧
    ∃ `{q ∊ Q∞₊}, Subset (B q x) S.
Notation "S °" := (interior S) (at level 1, format "S °") : mc_metric_scope.
Open Scope mc_metric_scope.

Class Dense `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ dense_msp : MetricSpace X
; dense_subsetoid :>> S ⊆ X
; dense_def  : closure S = X
}.

Class Closed `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ closed_msp : MetricSpace X
; closed_subsetoid :>> S ⊆ X
; closed_def  : closure S = S
}.
Notation ClosedFun := canonical_names.Closed.

Class Open `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ open_msp : MetricSpace X
; open_subsetoid :>> S ⊆ X
; open_def : S° = S
}.

Class Bounded `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ bounded_msp : MetricSpace X
; bounded_subsetoid :>> S ⊆ X
; bounded : ∃ `{d ∊ Q⁺}, ∀ `{x ∊ S} `{y ∊ S}, ball d x y
}.
Arguments bounded {_ X _ _} S {Bounded}.

Definition complement `{X:AmbientSpace} `{Ball X} : Tilde set
  := λ S x, x ∊ X ∧ ∀ `{s ∊ S}, ∃ q `{q ∊ Q₊}, ¬ ball q x s.
Hint Extern 5 (Tilde set) => eapply @complement : typeclass_instances.

Definition metric_complement `{X:AmbientSpace} `{Ball X} : Negate set
  := λ S x, x ∊ X ∧ ∃ q `{q ∊ Q∞₊}, ∀ `{s ∊ S}, ¬ ball q x s.
Hint Extern 5 (Negate set) => eapply @metric_complement : typeclass_instances.

Class MetricComplementStable `{X:AmbientSpace} `{Ball X} (S:set) : Prop :=
  metric_complement_stable : -∼S = S.
Arguments metric_complement_stable {_ X _} S {_} _.

Definition set_separated `{X:AmbientSpace} `{Ball X} q U V
  := ∀ u `{u ∊ U} v `{v ∊ V}, ¬ ball q u v.

Class SetApart `{X:AmbientSpace} `{Ball X} (U V:set) :=
  set_apart : ∃ q `{q ∊ Q∞₊}, set_separated q U V.
Arguments set_apart { _ X _} U V {_}.

Section maps.
  Context `(X:set) `(Y:set) `{MetricSpace _ (X:=X)} `{MetricSpace _ (X:=Y)}.

  Class UniformlyContinuous (f:X ⇀ Y) :=
  { uniform_cont_X : MetricSpace X
  ; uniform_cont_Y : MetricSpace Y
  ; uniform_cont_mor :>> Morphism (X ⇒ Y) f
  ; uniform_continuity_def ε `{ε ∊ Q₊} :  ∃ `{δ ∊ Q∞₊},
    ∀ `{x ∊ X} `{y ∊ X}, ball δ x y → ball ε (f x) (f y)
  }.

  Class Isometry (f:X ⇀ Y) :=
  { isometry_X : MetricSpace X
  ; isometry_Y : MetricSpace Y
  ; isometry_mor :>> Morphism (X ⇒ Y) f
  ; isometric_def ε `{ε ∊ Q₊} x `{x ∊ X} y `{y ∊ X} : ball ε x y ↔ ball ε (f x) (f y)
  }.
End maps.

Class Located `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ located_msp : MetricSpace X
; located_subsetoid :>> S ⊆ X
; located_def x `{x ∊ X} p `{p ∊ Q⁺} q `{q ∊ Q₊} :
    p < q → (∃ `{y ∊ S}, ball q x y) ∨ (∀ `{y ∊ S}, ¬ ball p x y)
}.

Definition union_of_balls `{X:AmbientSpace} `{Ball X} {S:set} ε (l : list { x | x ∊ S }) :=
  fold_right (λ (a:{ x | x ∊ S }) (b:set), b ⊔ B ε (` a)) ⊥ l .

Class TotallyBounded `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:set) :=
{ totally_bounded_msp : MetricSpace X
; totally_bounded_subsetoid :>> S ⊆ X
; totally_bounded_def ε `{ε ∊ Q₊} : ∃ (l : list { x | x ∊ S }), S ⊆ union_of_balls ε l
}.
Arguments totally_bounded_def {_ X _ _} S {TotallyBounded} ε {_}.

Class LocallyTotallyBounded `(X:set) `{Equiv X} `{Ball X} :=
  locally_totally_bounded_def U `{!Bounded (X:=X) U} `{!Inhabited U}
  ε `{ε ∊ Q₊} : ∃ (l : list { x | x ∊ X }), U ⊆ union_of_balls (X:=X) ε l .
(*  : ∃ (V:set), U ⊆ V ∧ TotallyBounded (X:=X) V. *)
(* locally_totally_bounded_def q `{q ∊ Q₊} x `{x ∊ X} : TotallyBounded (X:=X) (B (X:=X) q x). *)


Definition set_within `{X:AmbientSpace} `{Ball X} t U V
  := ∀ x `{x ∊ X} u `{u ∊ U}, ball t x u → x ∊ V.

Class SetContained `{X:AmbientSpace} `{Ball X} (U V:set) :=
  set_contained : ∃ q `{q ∊ Q∞₊}, set_within q U V.
Arguments set_contained { _ X _} U V {_}.

Class WellContained `{X:AmbientSpace} `{Equiv X} `{Ball X} (U V : set) :=
{ well_contained_V :>> V ⊆ X
; well_contained_subsetoid :>> U ⊆ V
; well_contained_bounded :>> Bounded U
; well_contained_inhabited :>> Inhabited U
; well_contained :>> SetContained U V
}.
Notation "S ⊂⊂ T" := (WellContained S T) (at level 70) : mc_metric_scope.
Notation "(⊂⊂)" := (WellContained) (only parsing) : mc_metric_scope.
Notation "( S ⊂⊂)" := (WellContained S) (only parsing) : mc_metric_scope.
Notation "(⊂⊂ T )" := ((λ S, S ⊂⊂ T) : Subset) (only parsing) : mc_metric_scope.

Notation "x ⊆ y ⊂⊂ z"  := (x ⊆  y ∧ y ⊂⊂ z) (at level 70, y at next level) : mc_scope.
Notation "x ⊂⊂ y ⊂⊂ z" := (x ⊂⊂ y ∧ y ⊂⊂ z) (at level 70, y at next level) : mc_scope.
Notation "x ⊂⊂ y ⊆ z"  := (x ⊂⊂ y ∧ y ⊆  z) (at level 70, y at next level) : mc_scope.

Class Continuous
  `{X:AmbientSpace} `{Equiv X} `{Ball X} `{Y:AmbientSpace} `{Equiv Y} `{Ball Y}
   D R (f:D ⇀ R) : Prop :=
{ cont_X : MetricSpace X
; cont_Y : MetricSpace Y
; cont_X_ltb : LocallyTotallyBounded X
; cont_Y_ltb : LocallyTotallyBounded Y
; cont_D_open :>> Open (X:=X) D
; cont_R_open :>> Open (X:=Y) R
; cont_mor :>> Morphism (D ⇒ R) f
; continuity_ufm      U `{U ⊂⊂ D} : UniformlyContinuous U R f
; continuity_wc_range U `{U ⊂⊂ D} : f⁺¹(U) ⊂⊂ R
}.


Infix "==>" := UniformlyContinuous (at level 55, right associativity) : set_scope.
Infix "-->" :=          Continuous (at level 55, right associativity) : set_scope.

(** Richman's regular family of subsets *)

Inductive Family `(X:set) `{Equiv X} := family : (Q∞₊ ⇀ (⊆ X)) → Family X.
Arguments family {_ X _} _.
Definition family_to_fun `{X:@set A} `{Equiv X} (x : Family X)
  := match x with family f => (f:AQ→@set A) end.
Coercion family_to_fun : Family >-> Funclass.

Section Cauchy.
  Context `{X:set} `{Equiv X} `{Ball X}.

  Class Cauchy (S:Family X) : Prop :=
  { cauchy_family_msp : MetricSpace X
  ; cauchy_family_mor : Morphism (Q∞₊ ⇒ (⊆ X)) S
  ; cauchy_family_inhabited q `{q ∊ Q∞₊} : Inhabited (S q)
  ; cauchy_family_def p `{p ∊ Q₊} q `{q ∊ Q₊} x `{x ∊ S p} y `{y ∊ S q} : ball (p+q) x y
  }.

  Definition FamilyLimit (S:Family X) y := ∀ p `{p ∊ Q₊} x  `{x ∊ S p}, ball p x y.

  Definition cauchy_ball : Ball (Family X) := λ q S T,
      ∀ ε `{ε ∊ Q₊}, ∃ `{a ∊ Q₊} `{b ∊ Q₊} `{c ∊ Q₊} `{s ∊ S a} `{t ∊ T b},
        a + b + c < q + ε ∧ ball c s t.

  Instance family_equiv : Equiv (Family X) := λ S T,
    ∀ p `{p ∊ Q₊} q `{q ∊ Q₊} x `{x ∊ S p} y `{y ∊ T q}, ball (p+q) x y.

End Cauchy.

Definition CauchyFamilies `(X:set) `{Equiv X} `{Ball X} := Cauchy : set.

Hint Extern 10 (@set (Family ?X)) => eexact (CauchyFamilies X) : typeclass_instances.

Hint Extern 2 (Equiv (Family _)) => eapply @family_equiv : typeclass_instances.
Hint Extern 2 (Equiv (elt_type (CauchyFamilies _))) => eapply @family_equiv : typeclass_instances.
Hint Extern 0 (Proper (_ ==> _) (family_to_fun _)) =>
   eapply (cauchy_family_mor : Proper ((Q∞₊,=) ==> ((⊆ _),=)) (family_to_fun _)) : typeclass_instances.

Class Limit `(X:set) `{Equiv X} `{Ball X} := limit : CauchyFamilies X ⇀ X.

Class CompleteMetricSpace `(X:set) `{Equiv X} `{Ball X} `{!Limit X}:=
{ complete_msp_msp :>> MetricSpace X
; complete_msp_limit_mor : Morphism (CauchyFamilies X ⇒ X) limit
; complete_msp S `{S ∊ CauchyFamilies X} : FamilyLimit S (limit S)
}.

Hint Extern 2 (Morphism _ limit) => eapply @complete_msp_limit_mor : typeclass_instances.

Class ToCompletion `(X:set) `(X':set) := to_completion : X ⇀ X' .
Arguments to_completion {_} X {_} X' {_} _.

Section completion.
  Context `(X:set) `{MetricSpace _ (X:=X)}.
  Context `(X':set) `{CompleteMetricSpace _ (X:=X')}.
  Context `{!ToCompletion X X'}.

  Class Completion : Prop :=
  { completion_msp_X :>> MetricSpace X
  ; completion_cmsp :>> CompleteMetricSpace X'
  ; completion_iso : Isometry X X' (to_completion X X')
  ; completion_dense : Dense (X:=X') (to_completion X X')⁺¹(X)
  }.
End completion.

Hint Extern 2 (Isometry _ _ (to_completion _ _)) => eapply @completion_iso : typeclass_instances.
Hint Extern 2 (Morphism _ (to_completion _ _)) => eapply @isometry_mor : typeclass_instances.
Hint Extern 2 (Dense (to_completion ?X _)⁺¹(?X)) => eapply @completion_dense : typeclass_instances.

Section archimedean_field.
  Context `{Field A (F:=F)} {Alt: Lt A} {Ale: Le A} {Aball: Ball F}.

  Class ArchimedeanField_Metric : Prop :=
  { arch_field_ball_proper : Proper ((Qfull,=)==>(F,=)==>(F,=)==>impl) ball
  ; arch_field_ball_nonneg ε `{ε ∊ Qfull} x `{x ∊ F} y `{y ∊ F} : ball ε x y → ε ∊ Q∞⁺
  ; arch_field_ball_inf x `{x ∊ F} y `{y ∊ F} : ball ∞ x y
  ; arch_field_ball ε `{ε ∊ Q} x `{x ∊ F} y `{y ∊ F}
      : ball ε x y ↔ - rationals_to_field Q F ε ≤ x - y ≤ rationals_to_field Q F ε
  }.
End archimedean_field.

Arguments ArchimedeanField_Metric {A _ _ _ _ _ _ _} F {_ _}.

