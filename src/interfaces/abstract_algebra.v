Require Export
  canonical_names restrict_rel find_proper interfaces.common_props
  util decision propholds.

Class Setoid `{Ae : Equiv A} S : Prop := setoid_eq :> SubEquivalence S (=).

Class UnEqualitySetoid `{Ae : Equiv A} {Aue : UnEq A} S : Prop :=
  { uneq_setoid :>> Setoid S
  ; uneq_proper : Proper ((S,=) ==> (S,=) ==> impl) (≠)
  ; uneq_ne   x `{x ∊ S} y `{y ∊ S} : x ≠ y → ¬ x = y
  ; equiv_nue x `{x ∊ S} y `{y ∊ S} : x = y → ¬ x ≠ y
  }.

Class StrongSetoid `{Ae : Equiv A} {Aue : UnEq A} S : Prop :=
  { strongsetoid_apart :> SubApartness S (≠)
  ; strongsetoid_tightapart :> TightApart S
  }.

Class RegularSubset `{Ae : Equiv A} S T : Prop :=
  { regular_subset_sub :> S ⊆ T
  ; regular_subset_reg : Proper ((T,=) ==> impl) (∊ S)
  }.

Class SubSetoid `{Ae: Equiv A} S T : Prop :=
  { subsetoid_b : Setoid T
  ; subsetoid_regular :> RegularSubset S T
  }.

Class SubStrongSetoid `{Ae: Equiv A} {Aue: UnEq A} S T : Prop :=
  { substrongsetoid_b : StrongSetoid T
  ; substrongsetoid_regular : RegularSubset S T
  }.

Section morphisms.
  Context {A B C} {Ae:Equiv A} {Be:Equiv B} {Ce:Equiv C}.
  Context {Aue:UnEq A} {Bue:UnEq B} {Cue:UnEq C}.
  Context (S:Subset A) (T:Subset B) (U:Subset C).

  Section unary.
    Context (f : A → B).

    Class Setoid_Morphism :=
      { setoidmor_a  : Setoid S
      ; setoidmor_b  : Setoid T
      ; setoidmor_proper :> Proper ((S,=)==>(T,=)) f
      }.

    Class StrongSetoid_Morphism :=
      { strong_setoidmor_a : StrongSetoid S
      ; strong_setoidmor_b : StrongSetoid T
      ; strong_setoidmor_closed : Closed (S ==> T) f
      ; strong_extensionality `{x ∊ S} `{y ∊ S} : f x ≠ f y → x ≠ y
      }.

  End unary.

  Section binary.
    Context (f : A → B → C).

    Class Setoid_Binary_Morphism :=
      { binary_setoidmor_a  : Setoid S
      ; binary_setoidmor_b  : Setoid T
      ; binary_setoidmor_c  : Setoid U
      ; binary_sm_proper :> Proper ((S,=)==>(T,=)==>(U,=)) f
      }.

    Class StrongSetoid_Binary_Morphism :=
      { strong_binary_setoidmor_a : StrongSetoid S
      ; strong_binary_setoidmor_b : StrongSetoid T
      ; strong_binary_setoidmor_c : StrongSetoid U
      ; strong_binary_setoidmor_closed : Closed (S ==> T ==> U) f
      ; strong_binary_extensionality `{x₁ ∊ S} `{y₁ ∊ T} `{x₂  ∊ S} `{y₂  ∊ T} :
          f x₁ y₁ ≠ f x₂ y₂ → x₁ ≠ x₂ ∨ y₁ ≠ y₂
      }.

  End binary.

End morphisms.
Arguments setoidmor_a {A B Ae Be S T} f {_}.
Arguments setoidmor_b {A B Ae Be S T} f {_}.
Arguments setoidmor_proper {A B Ae Be S T} f {_} _ _ _.
Arguments binary_setoidmor_a {A B C Ae Be Ce S T U} f {_}.
Arguments binary_setoidmor_b {A B C Ae Be Ce S T U} f {_}.
Arguments binary_setoidmor_c {A B C Ae Be Ce S T U} f {_}.
Arguments binary_sm_proper   {A B C Ae Be Ce S T U} f {_} _ _ _ _ _ _.
Arguments strong_setoidmor_a             {A B   _ _ _ _     S T  } f {_}.
Arguments strong_setoidmor_b             {A B   _ _ _ _     S T  } f {_}.
Arguments strong_setoidmor_closed        {A B   _ _ _ _     S T  } f {_} _ {_}.
Arguments strong_extensionality          {A B   _ _ _ _     S T  } f {_} _ {_} _ {_} _.
Arguments strong_binary_setoidmor_a      {A B C _ _ _ _ _ _ S T U} f {_}.
Arguments strong_binary_setoidmor_b      {A B C _ _ _ _ _ _ S T U} f {_}.
Arguments strong_binary_setoidmor_c      {A B C _ _ _ _ _ _ S T U} f {_}.
Arguments strong_binary_setoidmor_closed {A B C _ _ _ _ _ _ S T U} f {_} _ {_} _ {_}.
Arguments strong_binary_extensionality   {A B C _ _ _ _ _ _ S T U} f {_} _ {_} _ {_} _ {_} _ {_} _.

Section groups.

  Context {A} {op: SgOp A} {unit: MonUnit A} {Ainv: Inv A} {Ae: Equiv A}.

  Class SemiGroup S : Prop :=
    { sg_setoid    :> Setoid S
    ; sg_ass       : Associative (&) S
    ; sg_op_proper : Setoid_Binary_Morphism S S S (&)
    }.

  Class CommutativeSemiGroup S : Prop :=
    { comsg_sg :>> SemiGroup S
    ; comsg_commutative : Commutative (&) S
    }.

  Class Monoid M : Prop :=
    { monoid_semigroup   :>> SemiGroup M
    ; monoid_unit_exists : mon_unit ∊ M
    ; monoid_left_id     : LeftIdentity  (&) mon_unit M
    ; monoid_right_id    : RightIdentity (&) mon_unit M
    }.

  Class CommutativeMonoid M: Prop :=
    { commonoid_comsg   :>> CommutativeSemiGroup M
    ; commonoid_unit    : mon_unit ∊ M
    ; commonoid_left_id : LeftIdentity  (&) mon_unit M
    }.

  Class Group G : Prop :=
    { group_monoid :>> Monoid G
    ; inverse_proper : Setoid_Morphism G G (⁻¹)
    ; inverse_l : LeftInverse  (&) (⁻¹) mon_unit G
    ; inverse_r : RightInverse (&) (⁻¹) mon_unit G
    }.

  Class AbGroup G : Prop :=
    { abgroup_commonoid :>> CommutativeMonoid G
    ; abgroup_inverse_proper : Setoid_Morphism G G (⁻¹)
    ; abgroup_inverse_l      : LeftInverse  (&) (⁻¹) mon_unit G
    }.

End groups.
Hint Extern 0 (Associative (&) _) => eapply @sg_ass : typeclass_instances.
Hint Extern 0 (Setoid_Binary_Morphism _ _ _ (&)) => eapply @sg_op_proper : typeclass_instances.
Hint Extern 0 (Commutative (&) _) => eapply @comsg_commutative : typeclass_instances.
Hint Extern 0 (mon_unit ∊ _) => eapply @monoid_unit_exists : typeclass_instances.
Hint Extern 0 (LeftIdentity  (&) _ _) => eapply @monoid_left_id : typeclass_instances.
Hint Extern 0 (RightIdentity (&) _ _) => eapply @monoid_right_id : typeclass_instances.
Hint Extern 0 (Setoid_Morphism _ _ (⁻¹)) => eapply @inverse_proper : typeclass_instances.
Hint Extern 0 (LeftInverse  (&) _ _ _) => eapply @inverse_l : typeclass_instances.
Hint Extern 0 (RightInverse (&) _ _ _) => eapply @inverse_r : typeclass_instances.

Arguments inverse_l {A op unit Ainv Ae G Group} _ {_}.
Arguments inverse_r {A op unit Ainv Ae G Group} _ {_}.

Notation AdditiveMonoid := (CommutativeMonoid (op:=plus_is_sg_op) (unit:=zero_is_mon_unit)).
Notation AdditiveGroup  := (AbGroup (op:=plus_is_sg_op) (unit:=zero_is_mon_unit) (Ainv:=negate_is_inv)).

Notation MultiplicativeSemiGroup := (SemiGroup (op:=mult_is_sg_op)).
Notation MultiplicativeMonoid := (Monoid (op:=mult_is_sg_op) (unit:=one_is_mon_unit)).
Notation MultiplicativeComMonoid := (CommutativeMonoid (op:=mult_is_sg_op) (unit:=one_is_mon_unit)).
Notation MultiplicativeGroup := (Group (op:=mult_is_sg_op) (unit:=one_is_mon_unit)).
Notation MultiplicativeAbGroup := (AbGroup (op:=mult_is_sg_op) (unit:=one_is_mon_unit)).

Section rings.
  Context `{Aplus: Plus A} {Amult: Mult A} {Azero: Zero A} {Aone: One A} {Anegate: Negate A}.
  Context {Ainv: Inv A} {Ae:Equiv A} {Aue:UnEq A}.

  Class SemiRng R : Prop :=
    { semiplus_monoid    :>> AdditiveMonoid R
    ; semimult_semigroup :>> MultiplicativeSemiGroup R
    ; plus_mult_distr_l : LeftDistribute  (.*.) (+) R
    ; plus_mult_distr_r : RightDistribute (.*.) (+) R
    ; mult_0_l : LeftAbsorb  (.*.) 0 R
    ; mult_0_r : RightAbsorb (.*.) 0 R
    }.

  Class SemiRing R : Prop :=
    { semiring_semirng :>> SemiRng R
    ; semiring_one : 1 ∊ R
    ; mult_1_l : LeftIdentity  (.*.) 1 R
    ; mult_1_r : RightIdentity (.*.) 1 R
    }.

  Class CommutativeSemiRing R : Prop :=
    { comsemiplus_monoid :>> AdditiveMonoid R
    ; comsemimult_monoid :>> MultiplicativeComMonoid R
    ; comsemi_distr_l  : LeftDistribute (.*.) (+) R
    ; comsemi_asborb_l : LeftAbsorb (.*.) 0 R
    }.

  Class Rng R : Prop :=
    { rngplus_abgroup   :>> AdditiveGroup R
    ; rngmult_semigroup :>> MultiplicativeSemiGroup R
    ; rng_distr_l : LeftDistribute  (.*.) (+) R
    ; rng_distr_r : RightDistribute (.*.) (+) R
    }.

  Class Ring R : Prop :=
    { ring_rng :>> Rng R
    ; ring_one : 1 ∊ R
    ; ring_mult_1_l : LeftIdentity  (.*.) 1 R
    ; ring_mult_1_r : RightIdentity (.*.) 1 R
    }.

  Class CommutativeRing R : Prop :=
    { comringplus_abgroup   :>> AdditiveGroup R
    ; comringmult_commonoid :>> MultiplicativeComMonoid R
    ; comring_distr_l : LeftDistribute (.*.) (+) R
    }.

  Class IntegralDomain R : Prop :=
    { intdom_uneq :>> UnEqualitySetoid R 
    ; intdom_comring :>> CommutativeRing R
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes : Closed (R ₀ ==> R ₀ ==> R ₀) (.*.)
    ; intdom_cancel z `{z ∊ R ₀} :> LeftCancellation (.*.) z R
    }.

  Class Field F : Prop :=
    { field_comring      :>> CommutativeRing F
    ; field_strongsetoid :>> StrongSetoid F
    ; field_plus_ext     : StrongSetoid_Binary_Morphism F F F (+)
    ; field_mult_ext     : StrongSetoid_Binary_Morphism F F F (.*.)
    ; field_nontrivial   : PropHolds (1 ≠ 0)
    ; field_inv_proper   : Setoid_Morphism (F ₀) (F ₀) (⁻¹)
    ; field_inv_l        : LeftInverse (.*.) (⁻¹) 1 (F ₀)
    }.

End rings.

Hint Extern 0 (Associative (+)   _) => eapply (@sg_ass _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Associative (.*.) _) => eapply (@sg_ass _ mult_is_sg_op) : typeclass_instances.
Hint Extern 0 (Setoid_Binary_Morphism _ _ _ (+)  ) => eapply (@sg_op_proper _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Setoid_Binary_Morphism _ _ _ (.*.)) => eapply (@sg_op_proper _ mult_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (+)   _) => eapply (@comsg_commutative _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (.*.) _) => eapply (@comsg_commutative _ mult_is_sg_op) : typeclass_instances.
Hint Extern 0 (0 ∊ _) => eapply (@monoid_unit_exists _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 5 (1 ∊ _) => eapply (@monoid_unit_exists _ mult_is_sg_op one_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (+) _ _) => eapply (@monoid_left_id  _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 0 (RightIdentity (+) _ _) => eapply (@monoid_right_id _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (.*.) _ _) => eapply (@mult_1_l) : typeclass_instances.
Hint Extern 0 (RightIdentity (.*.) _ _) => eapply (@mult_1_r) : typeclass_instances.
Hint Extern 0 (Setoid_Morphism _ _ (-)) => eapply (@inverse_proper _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (LeftInverse  (-) _ _ _) => eapply (@inverse_l _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (RightInverse (-) _ _ _) => eapply (@inverse_r _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (LeftDistribute  (.*.) (+) _) => eapply @plus_mult_distr_l : typeclass_instances.
Hint Extern 0 (RightDistribute (.*.) (+) _) => eapply @plus_mult_distr_r : typeclass_instances.
Hint Extern 0 (LeftAbsorb  (.*.) _ _) => eapply @mult_0_l : typeclass_instances.
Hint Extern 0 (RightAbsorb (.*.) _ _) => eapply @mult_0_r : typeclass_instances.

Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @field_nontrivial : typeclass_instances.

Hint Extern 5 (StrongSetoid_Binary_Morphism _ _ _ (+)  ) => eapply @field_plus_ext : typeclass_instances.
Hint Extern 5 (StrongSetoid_Binary_Morphism _ _ _ (.*.)) => eapply @field_mult_ext : typeclass_instances.
Hint Extern 5 (Setoid_Morphism _ _ (⁻¹)) => eapply @field_inv_proper : typeclass_instances.
Hint Extern 2 (LeftInverse (.*.) _ _ _) => eapply @field_inv_l : typeclass_instances.

Arguments plus_mult_distr_l {A Aplus Amult Azero Ae R SemiRng} _ {_} _ {_} _ {_}.
Arguments plus_mult_distr_r {A Aplus Amult Azero Ae R SemiRng} _ {_} _ {_} _ {_}.
Arguments mult_0_l {A Aplus Amult Azero Ae R SemiRng} _ {_}.
Arguments mult_0_r {A Aplus Amult Azero Ae R SemiRng} _ {_}.
Arguments mult_1_l {A Aplus Amult Azero Aone Ae R SemiRing} _ {_}.
Arguments mult_1_r {A Aplus Amult Azero Aone Ae R SemiRing} _ {_}.
Arguments field_inv_l {A Aplus Amult Azero Aone Anegate Ainv Ae Aue F Field} _ {_}.

Class SemiGroup_Morphism {A B Aop Bop Ae Be} S T f :=
  { sgmor_a : @SemiGroup A Aop Ae S
  ; sgmor_b : @SemiGroup B Bop Be T
  ; sgmor_subsetmor :>> Setoid_Morphism S T f
  ; sgmor_preserves_sg_op `{x ∊ S} `{y ∊ S} : f (x & y) = f x & f y
  }.
Definition preserves_sg_op {A B} {S:Subset A} {T:Subset B} {f : S ⇀ T}
  `{SemiGroup_Morphism A B (S:=S) (T:=T) (f:=f)} x `{x ∊ S} y `{y ∊ S} := sgmor_preserves_sg_op (x:=x) (y:=y).

Class Monoid_Morphism {A B Aop Bop Aunit Bunit Ae Be} M N f :=
  { monmor_a : @Monoid A Aop Aunit Ae M
  ; monmor_b : @Monoid B Bop Bunit Be N
  ; monmor_sgmor :>> SemiGroup_Morphism M N f
  ; monmor_preserves_mon_unit : f mon_unit = mon_unit
  }.
Definition preserves_mon_unit {A B} {M:Subset A} {N:Subset B} {f : M ⇀ N}
  `{Monoid_Morphism A B (M:=M) (N:=N) (f:=f)} := monmor_preserves_mon_unit.

Notation AdditiveSemiGroup_Morphism := (SemiGroup_Morphism (Aop:=plus_is_sg_op) (Bop:=plus_is_sg_op)).
Notation AdditiveMonoid_Morphism := (Monoid_Morphism (Aop:=plus_is_sg_op) (Bop:=plus_is_sg_op) (Aunit:=zero_is_mon_unit) (Bunit:=zero_is_mon_unit)).
Notation MultiplicativeSemiGroup_Morphism := (SemiGroup_Morphism (Aop:=mult_is_sg_op) (Bop:=mult_is_sg_op)).

Section morphism_classes.
  Context {A B} {Ae:Equiv A} {Be:Equiv B}.
  Context {Aplus:Plus A} {Bplus:Plus B}.
  Context {Amult:Mult A} {Bmult:Mult B}.
  Context {Azero:Zero A} {Bzero:Zero B}.
  Context {Aone :One  A} {Bone :One  B}.

  Class SemiRng_Morphism R S f :=
    { srngmor_a : SemiRng (A:=A) R
    ; srngmor_b : SemiRng (A:=B) S
    ; srngmor_plus_mor :>> AdditiveMonoid_Morphism R S f
    ; srngmor_mult_mor :>> MultiplicativeSemiGroup_Morphism R S f
    }.

  Class SemiRing_Morphism R S f :=
    { sringmor_a : SemiRing (A:=A) R
    ; sringmor_b : SemiRing (A:=B) S
    ; sringmor_srng_mor :>> SemiRng_Morphism R S f
    ; sringmor_preserves_1 : f 1 = 1
    }.

  Context {Anegate :Negate A} {Bnegate :Negate B}.

  Class Rng_Morphism R S f :=
    { rngmor_a : Rng (A:=A) R
    ; rngmor_b : Rng (A:=B) S
    ; rngmor_plus_mor :>> AdditiveSemiGroup_Morphism R S f
    ; rngmor_mult_mor :>> MultiplicativeSemiGroup_Morphism R S f
    }.

  Class Ring_Morphism R S f :=
    { ringmor_a : Ring (A:=A) R
    ; ringmor_b : Ring (A:=B) S
    ; ringmor_rngmor :>> Rng_Morphism R S f
    ; ringmor_1 : ∃ `{x ∊ R}, f x = 1
    }.
End morphism_classes.
Definition preserves_1 `{SemiRing (R:=R1)} `{SemiRing (R:=R2)} {f : R1 ⇀ R2} `{!SemiRing_Morphism R1 R2 f} := sringmor_preserves_1.

Section jections.
  Context {A B} {Ae:Equiv A} {Aue:UnEq A} {Be:Equiv B} {Bue:UnEq B}.
  Context (S:Subset A) (T:Subset B) (f : A → B) {inv : Inverse (f : S ⇀ T)}.

  Open Scope mc_fun_scope.

  Class StrongInjective : Prop :=
    { strong_injective `{x ∊ S} `{y ∊ S} : x ≠ y → f x ≠ f y
    ; strong_injective_mor : StrongSetoid_Morphism S T f
    }.

  Class Injective : Prop :=
    { injective_def `{x ∊ S} `{y ∊ S} : f x = f y → x = y
    ; injective_mor : Setoid_Morphism S T f
    }.

  Class Surjective : Prop :=
    { surjective : (f : S ⇀ T) ∘ f⁻¹ = id (* a.k.a. "split-epi" *)
    ; surjective_mor : Setoid_Morphism S T f
    ; surjective_closed : Closed (T ==> S) (f⁻¹)
    }.

  Class Bijective : Prop :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective
    }.
End jections.
Arguments strong_injective {A B Ae Aue Be Bue S T} f {_} x {_} y {_} _.
Arguments strong_injective_mor {A B Ae Aue Be Bue S T} f {_}.
(* Arguments injective {A B Ae Be S T} f {_} x {_} y {_} _. *)
Arguments injective_mor {A B Ae Be S T} f {_}.
Arguments surjective {A B Ae Be S T} f {_} {_} _ _ _.
Arguments surjective_mor {A B Ae Be S T} f {_} {_}.
Arguments surjective_closed {A B Ae Be S T} f {_} {_} _ {_}.

Definition injective {A B S T} (f : S ⇀ T) `{Equiv A} `{Equiv B} `{!Injective (A:=A) (B:=B) S T f} x `{x ∊ S} y `{y ∊ S} := injective_def S T f (x:=x) (y:=y).

Hint Extern 5 (inverse _ _ ∊ _) => eapply @surjective_closed.
