Require Import abstract_algebra.

Local Open Scope grp_scope.

Class SubSemiGroup {A Aop Ae} S T :=
  { subsemigroup_a : @SemiGroup A Aop Ae S
  ; subsemigroup_b : SemiGroup T
  ; subsemigroup_sub :>> SubSetoid S T
  }.

Class SubMonoid {A Aop Aunit Ae} M N :=
  { submon_a : @Monoid A Aop Ae Aunit M
  ; submon_b : Monoid N
  ; submon_sub :>> SubSetoid M N
  }.

Class SubGroup {A Aop Aunit Ainv Ae} G H :=
  { subgroup_a : @Group A Aop Aunit Ainv Ae G
  ; subgroup_b : Group H
  ; subgroup_sub :>> SubSetoid G H
  }.

Class Normal_SubGroup {A Aop Aunit Ainv Ae} N G :=
  { normal_subgroup_sub :>> @SubGroup A Aop Aunit Ainv Ae N G
  ; normality n `{n ∊ N} g `{g ∊ G} : g & n & g⁻¹ ∊ N
  }.

Notation "N ◁ G" := (Normal_SubGroup N G) (at level 70) : grp_scope.

Class SubRng {A Aplus Amult Azero Anegate Ae} R S :=
  { subrng_a : @Rng A Aplus Amult Azero Anegate Ae R
  ; subrng_b : Rng S
  ; subrng_sub :>> SubSetoid R S
  }.

Notation AdditiveSubGroup := (SubGroup (Aop:=plus_is_sg_op) (Aunit:=zero_is_mon_unit) (Ainv:=negate_is_inv)).

(* We will prove RngIdeal I R -> SubRng I R *)
Class RngIdeal {A Aplus Amult Azero Anegate Ae} I R :=
  { rngideal_b : @Rng A Aplus Amult Azero Anegate Ae R
  ; rngideal_sub :>> AdditiveSubGroup I R
  ; rngideal_l r `{r ∊ R} x `{x ∊ I} : r * x ∊ I
  ; rngideal_r r `{r ∊ R} x `{x ∊ I} : x * r ∊ I
  }.

Lemma subsemigroup_el   `{sub:SubSemiGroup    (S:=X) (T:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.
Lemma submonoid_el      `{sub:SubMonoid       (M:=X) (N:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.
Lemma subgroup_el       `{sub:SubGroup        (G:=X) (H:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.
Lemma normalsubgroup_el `{sub:Normal_SubGroup (N:=X) (G:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.
Lemma subrng_el         `{sub:SubRng          (R:=X) (S:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.
Lemma rngideal_el       `{sub:RngIdeal        (I:=X) (R:=Y)} x `{x ∊ X} : x ∊ Y. Proof subset x.

Hint Extern 19 (?x ∊ ?S) => match goal with
  | sub : SubSemiGroup    _ ?S |- _ => eapply (subsemigroup_el   (sub:=sub) x)
  | sub : SubMonoid       _ ?S |- _ => eapply (submonoid_el      (sub:=sub) x)
  | sub : SubGroup        _ ?S |- _ => eapply (subgroup_el       (sub:=sub) x)
  | sub : Normal_SubGroup _ ?S |- _ => eapply (normalsubgroup_el (sub:=sub) x)
  | sub : SubRng          _ ?S |- _ => eapply (subrng_el         (sub:=sub) x)
  | sub : RngIdeal        _ ?S |- _ => eapply (rngideal_el       (sub:=sub) x)
end : typeclass_instances.

(* Check fun `{Normal_SubGroup (N:=H) (G:=G)} `{x ∊ H} => _ : x ∊ G. *)

