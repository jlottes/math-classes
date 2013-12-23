Require Import
  abstract_algebra interfaces.orders interfaces.rationals
  interfaces.archimedean_fields interfaces.metric_spaces
  the_ae_rationals.
Require Export
  arch_field_completion_ops arch_field_completion_field.
Require Import
  arch_field_completion_order arch_field_completion_order_strict.

Local Notation Q := the_ae_rationals.
Local Open Scope grp_scope.

Section contents.
  Context `{ArchimedeanField A1 (F:=F)} `{Ball F} `{!ArchimedeanField_Metric F}.
  Context `{R:@set A2} {Re:Equiv R} {Rue:UnEq R} {Rball:Ball R} {Rlimit:Limit R}.
  Context `{!ToCompletion F R} `{!Completion F R} `{!MetricInequality R}.

  Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.

  Hint Extern 0 (Zero   A2) => eexact (Creals_zero   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (One    A2) => eexact (Creals_one    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Negate A2) => eexact (Creals_negate (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Plus   A2) => eexact (Creals_plus   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Mult   A2) => eexact (Creals_mult   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Inv    A2) => eexact (Creals_inv    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Le     A2) => eexact (Creals_le     (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Lt     A2) => eexact (Creals_lt     (F:=F) (R:=R)) : typeclass_instances.

  Notation "%" := (rationals_to_field Q F).
  Notation "#" := (to_completion F R).

  Instance: Field R := Creals_field.
  Instance: SemiRing_Morphism F R # := Creals_inject_ring_mor.
  Instance: Isometry R R (-) := Creals_negate_iso.
  Instance: UniformlyContinuous (R*R) R (uncurry (+) : R*R ⇀ R) := Creals_plus_cont.
  Instance: Continuous (R*R) R (uncurry (.*.) : R*R ⇀ R) := Creals_mult_cont.
  Instance: Continuous (R ₀) (R ₀) (⁻¹) := Creals_inv_cont.

  Instance: SemiRingOrder R := Creals_ring_order.
  Instance: OrderEmbedding Q R (# ∘ %) := Creals_order_embedding.
  Let ball_correct := Creals_ball_order.

  Instance Creals_arch_field: ArchimedeanField R := Creals_arch_field_aux ball_correct.
  Instance Creals_arch_field_metric: ArchimedeanField_Metric R := Creals_arch_field_metric_aux ball_correct.

End contents.
