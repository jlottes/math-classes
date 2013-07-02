Require Import
  List
  abstract_algebra interfaces.orders interfaces.rationals.
Require Export
  interfaces.affine_extension the_ae_rationals.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Class Ball A := ball : AQ → A → @Subset A.

Section contents.
  Context `{X:@Subset A} {Ae:Equiv X} {Aball:Ball X}.

  Class MetricSpace : Prop :=
  { msp_setoid :>> Setoid X
  ; msp_ball_proper : Proper ((Qfull,=)==>(X,=)==>(X,=)==>impl) ball
  ; msp_nonneg ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X} : ball ε x y → ε ∊ Q∞⁺
  ; msp_ball_inf x `{x ∊ X} y `{y ∊ X} : ball ∞ x y
  ; msp_refl ε `{ε ∊ Q⁺} : SubReflexive X (ball ε)
  ; msp_sym  ε `{ε ∊ Q⁺} : SubSymmetric X (ball ε)
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
Class AmbientSpace {A} := ambient_space : @Subset A.
Identity Coercion Id_AmbientSpace_Subset : AmbientSpace >-> Subset.

Definition B `{X:AmbientSpace} `{Ball X} : Qfull ⇀ X ⇀ every Subset := λ q x, ball q x ⊓ X .

Definition closure `{X:AmbientSpace} `{Ball X} : Subset → Subset := λ S x, x ∊ X ∧
    ∀ `{ε ∊ Q∞₊}, ∃ `{s ∊ S}, ball ε x s.

Definition interior `{X:AmbientSpace} `{Ball X} : Subset → Subset := λ S x, x ∊ S ∧
    ∃ `{q ∊ Q∞₊}, SubsetOf (B q x) S.
Notation "S °" := (interior S) (at level 1, format "S °") : mc_metric_scope.
Open Scope mc_metric_scope.

Class Dense `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ dense_msp : MetricSpace X
; dense_subsetoid :>> S ⊆ X
; dense_def  : closure S = X
}.

Class Closed `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ closed_msp : MetricSpace X
; closed_subsetoid :>> S ⊆ X
; closed_def  : closure S = S
}.
Notation ClosedFun := canonical_names.Closed.

Class Open `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ open_msp : MetricSpace X
; open_subsetoid :>> S ⊆ X
; open_def : S° = S
}.

Class Bounded `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ bounded_msp : MetricSpace X
; bounded_subsetoid :>> S ⊆ X
; bounded : ∃ `{d ∊ Q⁺}, ∀ `{x ∊ S} `{y ∊ S}, ball d x y
}.
Arguments bounded {_ X _ _} S {Bounded}.

Definition complement `{X:AmbientSpace} `{Ball X} : Tilde Subset
  := λ S x, x ∊ X ∧ ∀ `{s ∊ S}, ∃ q `{q ∊ Q∞₊}, ¬ ball q x s.
Hint Extern 2 (Tilde Subset) => eapply @complement : typeclass_instances.

Definition metric_complement `{X:AmbientSpace} `{Ball X} : Negate Subset
  := λ S x, x ∊ X ∧ ∃ q `{q ∊ Q∞₊}, ∀ `{s ∊ S}, ¬ ball q x s.
Hint Extern 2 (Negate Subset) => eapply @metric_complement : typeclass_instances.

Class MetricComplementStable `{X:AmbientSpace} `{Ball X} (S:Subset) : Prop :=
  metric_complement_stable : -∼S = S.
Arguments metric_complement_stable {_ X _} S {_} _.

Definition set_separated `{X:AmbientSpace} `{Ball X} q U V
  := ∀ u `{u ∊ U} v `{v ∊ V}, ¬ ball q u v.

Class SetApart `{X:AmbientSpace} `{Ball X} (U V:Subset) :=
  set_apart : ∃ q `{q ∊ Q∞₊}, set_separated q U V.
Arguments set_apart { _ X _} U V {_}.

Section maps.
  Context `(X:Subset) `(Y:Subset) `{MetricSpace _ (X:=X)} `{MetricSpace _ (X:=Y)}.

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

  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  (** Implied by UniformlyContinuous when X is LocallyTotallyBounded
     and Y has FinitePoints *)
  Class StronglyUniformlyContinuous (f:X ⇀ Y) :=
  { strongly_ufm_cont_ufm_cont :>> UniformlyContinuous f
  ; strongly_ufm_cont U `{!Bounded (X:=X) U} `{!Inhabited U} : Bounded f⁺¹(U)
  }.
End maps.
(*Arguments strongly_ufm_cont {_ X _ Y _ _ _ _} f {_} U {_ _}.*)

Class WellContained `{X:AmbientSpace} `{Equiv X} `{Ball X} (U V : Subset) :=
{ well_contained_X : MetricSpace X
; well_contained_U :>> U ⊆ X
; well_contained_V :>> V ⊆ X
; well_contained_subsetoid :>> U ⊆ V
; well_contained_bounded :>> Bounded U
; well_contained_inhabited :>> Inhabited U
; well_contained :>> SetApart U (∼V)
}.
Notation "S ⊂⊂ T" := (WellContained S T) (at level 70) : mc_metric_scope.
Notation "(⊂⊂)" := (WellContained) (only parsing) : mc_metric_scope.
Notation "( S ⊂⊂)" := (WellContained S) (only parsing) : mc_metric_scope.
Notation "(⊂⊂ T )" := ((λ S, S ⊂⊂ T) : Subset) (only parsing) : mc_metric_scope.

Class Continuous
  `{X:AmbientSpace} `{Equiv X} `{Ball X} `{Y:AmbientSpace} `{Equiv Y} `{Ball Y}
   D R (f:D ⇀ R) : Prop :=
{ cont_X : MetricSpace X
; cont_Y : MetricSpace Y
; cont_D :>> D ⊆ X
; cont_R :>> R ⊆ Y
; cont_D_stable :>> MetricComplementStable D
; cont_R_stable :>> MetricComplementStable R
; cont_mor :>> Morphism (D ⇒ R) f
; continuity_ufm      U `{U ⊂⊂ D} : UniformlyContinuous U R f
; continuity_wc_range U `{U ⊂⊂ D} : f⁺¹(U) ⊂⊂ R
}.

Class Located `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ located_msp : MetricSpace X
; located_subsetoid :>> S ⊆ X
; located_def x `{x ∊ X} p `{p ∊ Q⁺} q `{q ∊ Q₊} :
    p < q → (∃ `{y ∊ S}, ball q x y) ∨ (∀ `{y ∊ S}, ¬ ball p x y)
}.

Definition union_of_balls `{X:AmbientSpace} `{Ball X} {S:Subset} ε (l : list { x | x ∊ S }) :=
  fold_right (λ (a:{ x | x ∊ S }) (b:Subset), b ⊔ B ε (` a)) ⊥ l .

Class TotallyBounded `{X:AmbientSpace} `{Equiv X} `{Ball X} (S:Subset) :=
{ totally_bounded_msp : MetricSpace X
; totally_bounded_subsetoid :>> S ⊆ X
; totally_bounded ε `{ε ∊ Q₊} : ∃ (l : list { x | x ∊ S }), S ⊆ union_of_balls ε l
}.
Arguments totally_bounded {_ X _ _} S {TotallyBounded} ε {_}.

Class LocallyTotallyBounded `(X:Subset) `{Equiv X} `{Ball X} :=
  locally_totally_bounded_def q `{q ∊ Q₊} x `{x ∊ X} : TotallyBounded (X:=X) (B (X:=X) q x).

Infix "==>" := UniformlyContinuous (at level 55, right associativity) : subset_scope.
Infix "-->" :=          Continuous (at level 55, right associativity) : subset_scope.

(* Richman's regular family of subsets *)

Inductive Net `(X:Subset) `{Equiv X} := net : (Q∞₊ ⇀ (⊆ X)) → Net X.
Arguments net {_ X _} _.
Definition net_to_fun `{X:@Subset A} `{Equiv X} (x : Net X)
  := match x with net f => (f:AQ→@Subset A) end.
Coercion net_to_fun : Net >-> Funclass.

Section Cauchy.
  Context `{X:Subset} `{Equiv X} `{Ball X}.

  Class Cauchy (S:Net X) : Prop :=
  { cauchy_net_msp : MetricSpace X
  ; cauchy_net_mor : Morphism (Q∞₊ ⇒ (⊆ X)) S
  ; cauchy_net_inhabited q `{q ∊ Q∞₊} : Inhabited (S q)
  ; cauchy_net_def p `{p ∊ Q₊} q `{q ∊ Q₊} x `{x ∊ S p} y `{y ∊ S q} : ball (p+q) x y
  }.

  Definition NetLimit (S:Net X) y := ∀ p `{p ∊ Q₊} x  `{x ∊ S p}, ball p x y.

  Definition cauchy_ball : Ball (Net X) := λ q S T,
      ∀ ε `{ε ∊ Q₊}, ∃ `{a ∊ Q₊} `{b ∊ Q₊} `{c ∊ Q₊} `{s ∊ S a} `{t ∊ T b},
        a + b + c < q + ε ∧ ball c s t.

  Instance net_equiv : Equiv (Net X) := λ S T,
    ∀ p `{p ∊ Q₊} q `{q ∊ Q₊} x `{x ∊ S p} y `{y ∊ T q}, ball (p+q) x y.

End Cauchy.

Definition CauchyNets `(X:Subset) `{Equiv X} `{Ball X} := Cauchy : Subset.

Hint Extern 10 (@Subset (Net ?X)) => eexact (CauchyNets X) : typeclass_instances.

Hint Extern 2 (Equiv (Net _)) => eapply @net_equiv : typeclass_instances.
Hint Extern 2 (Equiv (elt_type (CauchyNets _))) => eapply @net_equiv : typeclass_instances.
Hint Extern 0 (Proper (_ ==> _) (net_to_fun _)) =>
   eapply (cauchy_net_mor : Proper ((Q∞₊,=) ==> ((⊆ _),=)) (net_to_fun _)) : typeclass_instances.

Class Limit `(X:Subset) `{Equiv X} `{Ball X} := limit : CauchyNets X ⇀ X.

Class CompleteMetricSpace `(X:Subset) `{Equiv X} `{Ball X} `{!Limit X}:=
{ complete_msp_msp :>> MetricSpace X
; complete_msp_limit_mor : Morphism (CauchyNets X ⇒ X) limit
; complete_msp S `{S ∊ CauchyNets X} : NetLimit S (limit S)
}.

Hint Extern 2 (Morphism _ limit) => eapply @complete_msp_limit_mor : typeclass_instances.

Class ToCompletion `(X:Subset) `(X':Subset) := to_completion : X ⇀ X' .
Arguments to_completion {_} X {_} X' {_} _.

Section completion.
  Context `(X:Subset) `{MetricSpace _ (X:=X)}.
  Context `(X':Subset) `{CompleteMetricSpace _ (X:=X')}.
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

Section archimedean_ordered_field.
  Context `{Field A (F:=F)} {Alt: Lt A} {Ale: Le A} {Aball: Ball F}.

  Class ArchimedeanOrderedField_Metric : Prop :=
  { arch_ord_field_ball_proper : Proper ((Qfull,=)==>(F,=)==>(F,=)==>impl) ball
  ; arch_ord_field_ball_nonneg ε `{ε ∊ Qfull} x `{x ∊ F} y `{y ∊ F} : ball ε x y → ε ∊ Q∞⁺
  ; arch_ord_field_ball_inf x `{x ∊ F} y `{y ∊ F} : ball ∞ x y
  ; arch_ord_field_ball ε `{ε ∊ Q} x `{x ∊ F} y `{y ∊ F}
      : ball ε x y ↔ - rationals_to_field Q F ε ≤ x - y ≤ rationals_to_field Q F ε
  }.

  (*Notation Z := the_integers.

  Class ArchimedeanOrderedField : Prop :=
  { arch_ord_field_field :>> Field F
  ; arch_ord_field_order :>> FullPseudoSemiRingOrder F
  ; archimedean x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < (integers_to_ring Z F n) * y
  ; arch_ord_field_ball_proper : Proper ((Qfull,=)==>(F,=)==>(F,=)==>impl) ball
  ; arch_ord_field_ball_nonneg ε `{ε ∊ Qfull} x `{x ∊ F} y `{y ∊ F} : ball ε x y → ε ∊ Q∞⁺
  ; arch_ord_field_ball_inf x `{x ∊ F} y `{y ∊ F} : ball ∞ x y
  ; arch_ord_field_ball ε `{ε ∊ Q} x `{x ∊ F} y `{y ∊ F}
      : ball ε x y ↔ - rationals_to_field Q F ε ≤ x - y ≤ rationals_to_field Q F ε
  }.*)
End archimedean_ordered_field.

Arguments ArchimedeanOrderedField_Metric {A _ _ _ _ _ _ _} F {_ _}.

