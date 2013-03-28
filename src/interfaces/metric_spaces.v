Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals
  theory.setoids the_integers.
Require Export
  interfaces.affine_extension the_ae_rationals.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Class Ball A := ball : B → A → @Subset A.

Section contents.
  Context `{X:@Subset A} `{Ae:Equiv X} {Aball:Ball X}.

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

  Class PrelengthMetricSpace : Prop :=
  { plmsp_msp :>> MetricSpace
  ; prelength_msp x `{x ∊ X} y `{y ∊ X} ε `{ε ∊ Q₊} δ₁ `{δ₁ ∊ Q₊} δ₂ `{δ₂ ∊ Q₊}
      : ε < δ₁ + δ₂ → ball ε x y → ∃ `{z ∊ X}, ball δ₁ x z ∧ ball δ₂ z y
  }.

End contents.

Arguments MetricSpace {A} X {_ _}.
Arguments PrelengthMetricSpace {A} X {_ _}.

Definition closure `(X:Subset) `{Ball X} : Subset → Subset := λ S x, x ∊ X ∧
    ∀ `{ε ∊ Q∞₊}, ∃ `{s ∊ S}, ball ε x s.

Class Dense `(X:Subset) `{Equiv X} `{Ball X} (S:Subset) :=
{ dense_msp : MetricSpace X
; dense_subsetoid :>> S ⊆ X
; dense_def  : closure X S = X
}.

Class ClosedSet `(X:Subset) `{Equiv X} `{Ball X} (S:Subset) :=
{ closed_msp : MetricSpace X
; closed_subsetoid :>> S ⊆ X
; closed_def  : closure X S = S
}.

Class Open `(X:Subset) `{Equiv X} `{Ball X} (S:Subset) :=
{ open_msp : MetricSpace X
; open_subsetoid :>> S ⊆ X
; open x `{x ∊ S} : ∃ `{q ∊ Q∞₊}, SubsetOf (X ⊓ ball q x) S
}.
Arguments open {_ X _ _} S {Open} x {_}.

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
End maps.

(* Richman's regular family of subsets *)

Inductive Net `(X:Subset) `{Equiv X} := net : (Q₊ ⇀ (⊆ X)) → Net X.
Arguments net {_ X _} _.
Definition net_to_fun `{X:@Subset A} `{Equiv X} (x : Net X)
  := match x with net f => (f:B→@Subset A) end.
Coercion net_to_fun : Net >-> Funclass.

Section Cauchy.
  Context `{X:Subset} `{Equiv X} `{Ball X}.

  Class Cauchy (S:Net X) : Prop :=
  { cauchy_net_msp : MetricSpace X
  ; cauchy_net_mor : Morphism (Q∞₊ ⇒ (⊆ X)) S
  ; cauchy_net_inhabited q `{q ∊ Q∞₊} : ∃ x, x ∊ S q
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
  { completion_msp_X : MetricSpace X
  ; completion_cmsp :>> CompleteMetricSpace X'
  ; completion_iso : Isometry X X' (to_completion X X')
  ; completion_dense : Dense X' (to_completion X X')⁺¹(X)
  }.
End completion.

Hint Extern 2 (Isometry _ _ (to_completion _ _)) => eapply @completion_iso : typeclass_instances.
Hint Extern 2 (Morphism _ (to_completion _ _)) => eapply @isometry_mor : typeclass_instances.
Hint Extern 2 (Dense _ (to_completion ?X _)⁺¹(?X)) => eapply @completion_dense : typeclass_instances.

Section archimedean_ordered_field.
  Context `{Field A (F:=F)} {Alt: Lt A} {Ale: Le A} {Aball: Ball F}.

  Notation Z := the_integers.

  Class ArchimedeanOrderedField : Prop :=
  { arch_ord_field_field :>> Field F
  ; arch_ord_field_order :>> FullPseudoSemiRingOrder F
  ; archimedean x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < (integers_to_ring Z F n) * y
  ; arch_ord_field_ball_proper : Proper ((Qfull,=)==>(F,=)==>(F,=)==>impl) ball
  ; arch_ord_field_ball_nonneg ε `{ε ∊ Qfull} x `{x ∊ F} y `{y ∊ F} : ball ε x y → ε ∊ Q∞⁺
  ; arch_ord_field_ball_inf x `{x ∊ F} y `{y ∊ F} : ball ∞ x y
  ; arch_ord_field_ball ε `{ε ∊ Q} x `{x ∊ F} y `{y ∊ F}
      : ball ε x y ↔ - rationals_to_field Q F ε ≤ x - y ≤ rationals_to_field Q F ε
  }.
End archimedean_ordered_field.

Arguments ArchimedeanOrderedField {A _ _ _ _ _ _ _ _} F {_ _ _}.

