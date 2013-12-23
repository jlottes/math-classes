Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_fields interfaces.metric_spaces
  interfaces.rationals the_ae_rationals
  metric.complete metric.continuity.

Local Open Scope grp_scope.

Section contents.
  Context `{ArchimedeanField (F:=F)} `{Ball F} `{!ArchimedeanField_Metric F}.
  Context `{R:set} {Re:Equiv R} {Rue:UnEq R} {Rball:Ball R} {Rlimit:Limit R}.
  Context `{!ToCompletion F R} `{!Completion F R} `{!MetricInequality R}.

  Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.

  Notation "#" := (to_completion F R).

  (* C for Cauchy / completion *)
  Instance Creals_zero   : Zero   R := # 0.
  Instance Creals_one    : One    R := # 1.
  Instance Creals_negate : Negate R := ufm_completion_map (-).
  Instance Creals_plus   : Plus   R := curry (ufm_completion_map (uncurry (+))).
  Instance Creals_mult   : Mult   R := curry (continuous_extension (to_completion (F*F) (R*R)) # (F*F) F (uncurry (.*.)):R*R ⇀ R).
  Instance Creals_inv    : Inv    R := continuous_extension # # (F ₀) (F ₀) (⁻¹).

  Notation Q := the_ae_rationals.
  Notation "%" := (rationals_to_field Q F).

  Instance Creals_le : Le R := λ x y, ∀ `{ε ∊ Q₊} `{q ∊ Q}, ball ε (#(%q)) (y-x) → -ε ≤ q.
  Instance Creals_lt : Lt R := λ x y, ∃ `{q ∊ Q₊}, x + #(%q) ≤ y.

End contents.
