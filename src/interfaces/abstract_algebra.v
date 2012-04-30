Require Export
  canonical_names restrict_rel find_proper interfaces.subset interfaces.common_props
  util decision propholds workarounds setoid_tactics.

(* 
For various structures we omit declaration of substructures. For example, if we 
say:

Class Setoid_Morphism :=
  { setoidmor_a :> Setoid A
  ; setoidmor_b :> Setoid B
  ; sm_proper :> Proper ((=) ==> (=)) f }.

then each time a Setoid instance is required, Coq will try to prove that a
Setoid_Morphism exists. This obviously results in an enormous blow-up of the
search space. Moreover, one should be careful to declare a Setoid_Morphisms
as a substructure. Consider [f t1 t2], now if we want to perform setoid rewriting
in [t2] Coq will first attempt to prove that [f t1] is Proper, for which it will 
attempt to prove [Setoid_Morphism (f t1)]. If many structures declare
Setoid_Morphism as a substructure, setoid rewriting will become horribly slow.
*)

(* An unbundled variant of the former CoRN RSetoid *)
Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Class UnEqualitySetoid A {Ae : Equiv A } {Aue : UnEq A} : Prop :=
  { uneq_setoid : Setoid A
  ; uneq_proper : Proper ((=) ==> (=) ==> impl) (≠)
  ; uneq_ne   x y : x ≠ y → ¬ x = y
  ; equiv_nue x y : x = y → ¬ x ≠ y
  }.

Class TightApart A {Ae : Equiv A} {Aue : UnEq A} : Prop
  := tight_apart x y : ¬ x ≠ y ↔ x = y.

Class StrongSetoid A {Ae : Equiv A} {Aue : UnEq A} : Prop :=
  { strong_setoid_apartness   :> Apartness (≠)
  ; strong_setoid_tight_apart :> TightApart A
  }.

(*
Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A → B).

  Class Setoid_Morphism :=
    { setoidmor_a : Setoid A
    ; setoidmor_b : Setoid B
    ; sm_proper :> Proper ((=) ==> (=)) f }.

End setoid_morphisms.

Arguments sm_proper {A B Ae Be f Setoid_Morphism} _ _ _.
Hint Extern 4 (?f _ = ?f _) => eapply (sm_proper (f:=f)).
*)

Class ProperSubset {A} {Ae:Equiv A} (S:Subset A) : Prop
  := subset_proper : Proper ((=) ==> impl) (∊ S).

Class SubSetoid {A} {Ae : Equiv A} (S:Subset A) : Prop :=
  { subsetoid_setoid :>> Setoid A
  ; subsetoid_proper :> ProperSubset S
  }.

Class SubStrongSetoid {A} {Ae : Equiv A} {Aue : UnEq A} (S:Subset A) : Prop :=
  { substrongsetoid_strongsetoid :>> StrongSetoid A
  ; substrongsetoid_proper :> ProperSubset S
  }.

Section subsetoid_morphisms.
  Context `{Ae : Equiv A} `{Be : Equiv B} `{Ce : Equiv C}.
  Context {Aue : UnEq A} {Bue : UnEq B} {Cue : UnEq C}.

  Class Domain   (f:A → B) (D:Subset A) := is_dom   : unit.
  Class CoDomain (f:A → B) (C:Subset B) := is_codom : unit.

  Section unary.
    Context (f : A → B).

    Class SubSetoid_Morphism (S:Subset A) (T:Subset B) :=
      { subsetoidmor_s  : SubSetoid S
      ; subsetoidmor_t  : SubSetoid T
      ; subsetoidmor_sp :> SubProper ((S,=) ==> (T,=) ) f
      }.

    Global Instance ssm_dom   `{!SubSetoid_Morphism X Y} : Domain   f X := tt.
    Global Instance ssm_codom `{!SubSetoid_Morphism X Y} : CoDomain f Y := tt.

    Class SubStrongSetoid_Morphism (S:Subset A) (T:Subset B) :=
      { strong_subsetoidmor_s : SubStrongSetoid S
      ; strong_subsetoidmor_t : SubStrongSetoid T
      ; strong_subsetoidmor_closed : Closed (S ==> T) f
      ; strong_extensionality `{x ∊ S} `{y ∊ S} : f x ≠ f y → x ≠ y
      }.

    Global Instance sssm_dom   `{!SubStrongSetoid_Morphism X Y} : Domain   f X := tt.
    Global Instance sssm_codom `{!SubStrongSetoid_Morphism X Y} : CoDomain f Y := tt.


  End unary.


  Section binary.
    Context (f : A → B → C).

    Class SubSetoid_Binary_Morphism (S:Subset A) (T:Subset B) (U:Subset C) :=
      { binary_subsetoidmor_s  : SubSetoid S
      ; binary_subsetoidmor_t  : SubSetoid T
      ; binary_subsetoidmor_u  : SubSetoid U
      ; ssm_binary_proper :> SubProper ((S,=)==>(T,=)==>(U,=)) f
      }.

    Class SubStrongSetoid_Binary_Morphism (S:Subset A) (T:Subset B) (U:Subset C) :=
      { strong_binary_subsetoidmor_s : SubStrongSetoid S
      ; strong_binary_subsetoidmor_t : SubStrongSetoid T
      ; strong_binary_subsetoidmor_u : SubStrongSetoid U
      ; strong_binary_subsetoidmor_closed : Closed (S ==> T ==> U) f
      ; strong_binary_extensionality `{x₁ ∊ S} `{y₁ ∊ T} `{x₂  ∊ S} `{y₂  ∊ T} :
          f x₁ y₁ ≠ f x₂ y₂ → x₁ ≠ x₂ ∨ y₁ ≠ y₂
      }.

  End binary.

  Section images.
    Definition image (f:A → B) (S:Subset A) : Subset B
      := λ y, ∃ x, x ∊ S ∧ f x = y.
    Definition inv_image (f:A → B) `{!Domain f D} (T:Subset B) : Subset A
      := λ x, x ∊ D ∧ f x ∊ T.
  End images.

End subsetoid_morphisms.

Arguments strong_extensionality        {A _ B _     _ _  } f {S T   _} _ {_} _ {_} _.
Arguments strong_binary_extensionality {A _ B _ C _ _ _ _} f {S T U _} _ {_} _ {_} _ {_} _ {_} _.

Notation "f ⁺¹( T )" :=     (image f T) (at level 1, format "f ⁺¹( T )" ) : mc_scope.
Notation "f ⁻¹( T )" := (inv_image f T) (at level 1, format "f ⁻¹( T )") : mc_scope.

Section upper_classes.
  Context {A} {Ae : Equiv A}.

  Class SemiGroup {Sop: SgOp A} (S:Subset A) : Prop :=
    { sg_subsetoid :>> SubSetoid S
    ; sg_ass :> Associative (&) S
    ; sg_op_proper :> SubSetoid_Binary_Morphism (&) S S S
    }.

  Class Monoid {Mop} {Munit : MonUnit A} (M:Subset A) : Prop :=
    { monoid_semigroup :> @SemiGroup Mop M
    ; monoid_unit_exists :> mon_unit ∊ M
    ; monoid_left_id :> LeftIdentity (&) mon_unit M
    ; monoid_right_id :> RightIdentity (&) mon_unit M
    }.

  Class CommutativeMonoid {Mop Munit} (M:Subset A): Prop :=
    { commonoid_mon :>> @Monoid Mop Munit M
    ; commonoid_commutative :> Commutative (&) M
    }.

  Class Group {Gop Gunit} {Ginv : Inv A} (G:Subset A): Prop :=
    { group_monoid :>> @Monoid Gop Gunit G
    ; inverse_proper :> SubSetoid_Morphism (⁻¹) G G
    ; inverse_l :> LeftInverse  (&) (⁻¹) mon_unit G
    ; inverse_r :> RightInverse (&) (⁻¹) mon_unit G
    }.

  Class AbGroup {Gop Gunit Ginv} (G:Subset A): Prop :=
    { abgroup_group :>> @Group Gop Gunit Ginv G
    ; abgroup_commutative :> Commutative (&) G
    }.

  Context {Aplus: Plus A} {Amult: Mult A} {Azero: Zero A} {Aone: One A}.

  Class SemiRng (R:Subset A): Prop :=
    { semiplus_monoid    :>> @CommutativeMonoid plus_is_sg_op zero_is_mon_unit R
    ; semimult_semigroup :>> @SemiGroup mult_is_sg_op R
    ; plus_mult_distr_l :> LeftDistribute (.*.) (+) R
    ; plus_mult_distr_r :> RightDistribute (.*.) (+) R
    ; mult_0_l :> LeftAbsorb (.*.) 0 R
    ; mult_0_r :> RightAbsorb (.*.) 0 R
    }.

  Class SemiRing (R:Subset A): Prop :=
    { semiring_semirng :>> SemiRng R
    ; semiring_one :> 1 ∊ R
    ; mult_1_l :> LeftIdentity (.*.) 1 R
    ; mult_1_r :> RightIdentity (.*.) 1 R
    }.

  Context {Anegate: Negate A}.

  Class Rng (R:Subset A): Prop :=
    { rngplus_abgroup   :>> @AbGroup   plus_is_sg_op zero_is_mon_unit negate_is_inv R
    ; rngmult_semigroup :>> @SemiGroup mult_is_sg_op R
    ; rng_distr_l :> LeftDistribute (.*.) (+) R
    ; rng_distr_r :> RightDistribute (.*.) (+) R
    }.

  Class Ring (R:Subset A): Prop :=
    { ringplus_abgroup :>> @AbGroup plus_is_sg_op zero_is_mon_unit negate_is_inv R
    ; ringmult_monoid  :>> @Monoid  mult_is_sg_op one_is_mon_unit R
    ; ring_distr_l :> LeftDistribute (.*.) (+) R
    ; ring_distr_r :> RightDistribute (.*.) (+) R
    }.

  Class CommutativeRing (R:Subset A): Prop :=
    { comringplus_abgroup   :>> @AbGroup plus_is_sg_op zero_is_mon_unit negate_is_inv R
    ; comringmult_commonoid :>> @CommutativeMonoid mult_is_sg_op one_is_mon_unit R
    ; comring_distr_l :> LeftDistribute (.*.) (+) R
    }.

  Context {Aue: UnEq A}.

  Class IntegralDomain R : Prop :=
    { intdom_comring : CommutativeRing R
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes :> NoZeroDivisors R
    }.

  Context {Ainv: Inv A}.

  Class Field (F:Subset A): Prop :=
    { field_comring      :>> CommutativeRing F
    ; field_strongsetoid :>> StrongSetoid A
    ; field_plus_ext     :> SubStrongSetoid_Binary_Morphism (+)   F F F
    ; filed_mult_ext     :> SubStrongSetoid_Binary_Morphism (.*.) F F F
    ; field_nontrivial   : PropHolds (1 ≠ 0)
    ; field_inv_proper   :> SubSetoid_Morphism (⁻¹) (F ₀) (F ₀)
    ; field_inv_l        :> LeftInverse  (.*.) (⁻¹) 1 (F ₀)
    }.

End upper_classes.

Arguments inverse_l {A Ae Gop Gunit Ginv G Group} _ {_}.
Arguments inverse_r {A Ae Gop Gunit Ginv G Group} _ {_}.
Arguments plus_mult_distr_l {A Ae Aplus Amult Azero R SemiRng} _ {_} _ {_} _ {_}.
Arguments plus_mult_distr_r {A Ae Aplus Amult Azero R SemiRng} _ {_} _ {_} _ {_}.
Arguments mult_0_l {A Ae Aplus Amult Azero R SemiRng} _ {_}.
Arguments mult_0_r {A Ae Aplus Amult Azero R SemiRng} _ {_}.
Arguments mult_1_l {A Ae Aplus Amult Azero Aone R SemiRing} _ {_}.
Arguments mult_1_r {A Ae Aplus Amult Azero Aone R SemiRing} _ {_}.
Arguments field_inv_l {A Ae Aplus Amult Azero Aone Anegate Aue Ainv F Field} _ {_}.

Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @field_nontrivial : typeclass_instances.

Section morphism_classes.
  Context `{Ae : Equiv A} `{Be : Equiv B}.

  Class SemiGroup_Morphism {Sop Top} (f : A → B) (S:Subset A) (T:Subset B) :=
    { sgmor_a : @SemiGroup _ _ Sop S
    ; sgmor_b : @SemiGroup _ _ Top T
    ; sgmor_subsetmor :>> SubSetoid_Morphism f S T
    ; preserves_sg_op x `{x ∊ S} y `{y ∊ S} : f (x & y) = f x & f y
    }.

  Class Monoid_Morphism {Munit Nunit Mop Nop} (f : A → B) (M:Subset A) (N:Subset B) :=
    { monmor_a : @Monoid _ _ Mop Munit M
    ; monmor_b : @Monoid _ _ Nop Nunit N
    ; monmor_sgmor :>> SemiGroup_Morphism f M N
    ; preserves_mon_unit : f mon_unit = mon_unit
    }.

  Class SemiRng_Morphism {Aplus Amult Azero
                          Bplus Bmult Bzero}
                          (f : A → B) (R:Subset A) (S:Subset B) :=
    { srngmor_a : @SemiRng _ _ Aplus Amult Azero R
    ; srngmor_b : @SemiRng _ _ Bplus Bmult Bzero S
    ; srngmor_plus_mor :>> @Monoid_Morphism zero_is_mon_unit zero_is_mon_unit plus_is_sg_op plus_is_sg_op f R S
    ; srngmor_mult_mor :>> @SemiGroup_Morphism mult_is_sg_op mult_is_sg_op f R S
    }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone
                           Bplus Bmult Bzero Bone}
                          (f : A → B) (R:Subset A) (S:Subset B) :=
    { sringmor_a : @SemiRing _ _ Aplus Amult Azero Aone R
    ; sringmor_b : @SemiRing _ _ Bplus Bmult Bzero Bone S
    ; sringmor_srng_mor :>> SemiRng_Morphism f R S
    ; preserves_1 : f 1 = 1
    }.

  Class Rng_Morphism {Aplus Amult Azero Anegate
                      Bplus Bmult Bzero Bnegate}
                     (f : A → B) (R:Subset A) (S:Subset B) :=
    { rngmor_a : @Rng _ _ Aplus Amult Azero Anegate R
    ; rngmor_b : @Rng _ _ Bplus Bmult Bzero Bnegate S
    ; rngmor_plus_mor :>> @SemiGroup_Morphism plus_is_sg_op plus_is_sg_op f R S
    ; rngmor_mult_mor :>> @SemiGroup_Morphism mult_is_sg_op mult_is_sg_op f R S
    }.

  Class Ring_Morphism {Aplus Amult Azero Aone Anegate
                       Bplus Bmult Bzero Bone Bnegate}
                      (f : A → B) (R:Subset A) (S:Subset B) :=
    { ringmor_a : @Ring _ _ Aplus Amult Azero Aone Anegate R
    ; ringmor_b : @Ring _ _ Bplus Bmult Bzero Bone Bnegate S
    ; ringmor_rngmor :>> Rng_Morphism f R S
    ; ringmor_image_has_1 : ∃ `{x ∊ R}, f x = 1
    }.

End morphism_classes.

Section jections.
  Context `{Ae : Equiv A} {Aue: UnEq A} `{Be : Equiv B} {Bue: UnEq B} (f : A → B).

  Class StrongInjective (S:Subset A) (T:Subset B) : Prop :=
    { strong_injective  x `{x ∊ S} y `{y ∊ S} : x ≠ y → f x ≠ f y
    ; strong_injective_mor : SubStrongSetoid_Morphism f S T
    }.

  Class Injective (S:Subset A) (T:Subset B) : Prop :=
    { injective x `{x ∊ S} y `{y ∊ S} : f x = f y → x = y
    ; injective_mor : SubSetoid_Morphism f S T
    }.

End jections.

