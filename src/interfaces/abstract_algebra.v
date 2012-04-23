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

Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A → B).

  Class Setoid_Morphism :=
    { setoidmor_a : Setoid A
    ; setoidmor_b : Setoid B
    ; sm_proper :> Proper ((=) ==> (=)) f }.

End setoid_morphisms.

Arguments sm_proper {A B Ae Be f Setoid_Morphism} _ _ _.
Hint Extern 4 (?f _ = ?f _) => eapply (sm_proper (f:=f)).

Class SubSetoid {A} {Ae : Equiv A} (S:Subset A) : Prop :=
  { subsetoid_setoid :>> @Setoid A Ae
  ; subset_proper : Proper ((=) ==> impl) (∊ S)
  }.

Section subsetoid_morphisms.
  Context `{Ae : Equiv A} `{Be : Equiv B} `{Ce : Equiv C}.

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

  End unary.


  Section binary.
    Context (f : A → B → C).

    Class SubSetoid_Binary_Morphism (S:Subset A) (T:Subset B) (U:Subset C) :=
      { subsetoidmor_binary_s  : SubSetoid S
      ; subsetoidmor_binary_t  : SubSetoid T
      ; subsetoidmor_binary_u  : SubSetoid U
      ; ssm_binary_proper :> SubProper ((S,=)==>(T,=)==>(U,=)) f
      }.
  End binary.

  Section images.
    Definition image (f:A → B) (S:Subset A) : Subset B
      := λ y, ∃ x, x ∊ S ∧ f x = y.
    Definition inv_image (f:A → B) `{!Domain f D} (T:Subset B) : Subset A
      := λ x, x ∊ D ∧ f x ∊ T.
  End images.

End subsetoid_morphisms.

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
    ; semirng_distr_l :> LeftDistribute (.*.) (+) R
    ; semirng_distr_r :> RightDistribute (.*.) (+) R
    ; semirng_left_absorb :> LeftAbsorb (.*.) 0 R
    ; semirng_right_absorb :> RightAbsorb (.*.) 0 R
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

  Class IntegralDomain R : Prop :=
    { intdom_comring : CommutativeRing R
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes :> NoZeroDivisors R
    }.

  Context {Ainv: Inv A}.

  Class Field (F:Subset A): Prop :=
    { field_comring    :>> CommutativeRing F
    ; field_nontrivial : PropHolds (1 ≠ 0)
    ; field_inv_proper :> SubSetoid_Morphism (⁻¹) (F ₀) (F ₀)
    ; field_inv_l      :> LeftInverse  (.*.) (⁻¹) 1 (F ₀)
    }.

End upper_classes.

Arguments inverse_l {A Ae Gop Gunit Ginv G Group} _ {_}.
Arguments inverse_r {A Ae Gop Gunit Ginv G Group} _ {_}.
Arguments mult_1_l {A Ae Aplus Amult Azero Aone R SemiRing} _ {_}.
Arguments mult_1_r {A Ae Aplus Amult Azero Aone R SemiRing} _ {_}.
Arguments field_inv_l {A Ae Aplus Amult Azero Aone Anegate Ainv F Field} _ {_}.

Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @field_nontrivial : typeclass_instances.

Section morphism_classes.
  Context `{Ae : Equiv A} `{Be : Equiv B}.

  Class SemiGroup_Morphism {Sop Top} (f : A → B) (S:Subset A) (T:Subset B) :=
    { sgmor_a : @SemiGroup _ _ Sop S
    ; sgmor_b : @SemiGroup _ _ Top T
    ; sgmor_subsetmor :>> SubSetoid_Morphism f S T
    ; preserves_sg_op x `{!x ∊ S} y `{!y ∊ S} : f (x & y) = f x & f y
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
  Context `{Ae : Equiv A} `{Be : Equiv B} (f : A → B).
         (* `{inv : !Inverse f} *)

  Class Injective (S:Subset A) (T:Subset B) : Prop :=
    { injective x `{!x ∊ S} y `{!y ∊ S} : f x = f y → x = y
    ; injective_mor : SubSetoid_Morphism f S T}.

(*
  Class Surjective : Prop :=
    { surjective : f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *)
    ; surjective_mor : Setoid_Morphism f }.

  Class Bijective : Prop :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective }.
*)
End jections.


(*

Section upper_classes.
  Context A {Ae : Equiv A}.

  Class SemiGroup {Aop: SgOp A} : Prop :=
    { sg_setoid :> Setoid A
    ; sg_ass :> Associative (&)
    ; sg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&) }.

  Class CommutativeSemiGroup {Aop : SgOp A} : Prop :=
    { comsg_setoid :> @SemiGroup Aop
    ; comsg_ass :> Commutative (&) }.

  Class SemiLattice {Aop : SgOp A} : Prop :=
    { semilattice_sg :> @CommutativeSemiGroup Aop
    ; semilattice_idempotent :> BinaryIdempotent (&)}.

  Class Monoid {Aop : SgOp A} {Aunit : MonUnit A} : Prop :=
    { monoid_semigroup :> SemiGroup
    ; monoid_left_id :> LeftIdentity (&) mon_unit
    ; monoid_right_id :> RightIdentity (&) mon_unit }.

  Class CommutativeMonoid {Aop Aunit} : Prop :=
    { commonoid_mon :> @Monoid Aop Aunit
    ; commonoid_commutative :> Commutative (&) }.

  Class Group {Aop Aunit} {Anegate : Negate A} : Prop :=
    { group_monoid :> @Monoid Aop Aunit
    ; negate_proper :> Setoid_Morphism (-)
    ; negate_l :> LeftInverse (&) (-) mon_unit
    ; negate_r :> RightInverse (&) (-) mon_unit }.

  Class BoundedSemiLattice {Aop Aunit} : Prop :=
    { bounded_semilattice_mon :> @CommutativeMonoid Aop Aunit
    ; bounded_semilattice_idempotent :> BinaryIdempotent (&)}.

  Class AbGroup {Aop Aunit Anegate} : Prop :=
    { abgroup_group :> @Group Aop Aunit Anegate
    ; abgroup_commutative :> Commutative (&) }.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class SemiRing : Prop :=
    { semiplus_monoid :> @CommutativeMonoid plus_is_sg_op zero_is_mon_unit
    ; semimult_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; semiring_distr :> LeftDistribute (.*.) (+)
    ; semiring_left_absorb :> LeftAbsorb (.*.) 0 }.

  Context {Anegate : Negate A}.

  Class Ring : Prop :=
    { ring_group :> @AbGroup plus_is_sg_op zero_is_mon_unit _
    ; ring_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; ring_dist :> LeftDistribute (.*.) (+) }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain : Prop :=
    { intdom_ring : Ring 
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes :> NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/) because it can de derived *)
  Class Field {Aap: Apart A} {Arecip: Recip A} : Prop :=
    { field_ring :> Ring
    ; field_strongsetoid :> StrongSetoid A
    ; field_plus_ext :> StrongSetoid_BinaryMorphism (+)
    ; field_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_proper :> Setoid_Morphism (//)
    ; recip_inverse : ∀ x, `x // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/), f (/x) = / (f x), / /x = x, /x * /y = /(x * y) 
    hold without any additional assumptions *)
  Class DecField {Adec_recip : DecRecip A} : Prop :=
    { decfield_ring :> Ring
    ; decfield_nontrivial : PropHolds (1 ≠ 0)
    ; dec_recip_proper :> Setoid_Morphism (/)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : ∀ x, x ≠ 0 → x / x = 1 }.
End upper_classes.

(* Due to bug #2528 *)
Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≶ 0)) => eapply @field_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @decfield_nontrivial : typeclass_instances.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Arguments recip_inverse {A Ae Aplus Amult Azero Aone Anegate Aap Arecip Field} _.
Arguments dec_recip_inverse {A Ae Aplus Amult Azero Aone Anegate Adec_recip DecField} _ _.
Arguments dec_recip_0 {A Ae Aplus Amult Azero Aone Anegate Adec_recip DecField}.
Arguments sg_op_proper {A Ae Aop SemiGroup} _ _ _ _ _ _.

Section lattice.
  Context A `{Ae: Equiv A} {Ajoin: Join A} {Ameet: Meet A} `{Abottom : Bottom A}.

  Class JoinSemiLattice : Prop := 
    join_semilattice :> @SemiLattice A Ae join_is_sg_op.
  Class BoundedJoinSemiLattice : Prop := 
    bounded_join_semilattice :> @BoundedSemiLattice A Ae join_is_sg_op bottom_is_mon_unit.
  Class MeetSemiLattice : Prop := 
    meet_semilattice :> @SemiLattice A Ae meet_is_sg_op.

  Class Lattice : Prop := 
    { lattice_join :> JoinSemiLattice
    ; lattice_meet :> MeetSemiLattice
    ; join_meet_absorption :> Absorption (⊔) (⊓) 
    ; meet_join_absorption :> Absorption (⊓) (⊔)}.

  Class DistributiveLattice : Prop := 
    { distr_lattice_lattice :> Lattice
    ; join_meet_distr_l :> LeftDistribute (⊔) (⊓) }.
End lattice.

Class Category O `{!Arrows O} `{∀ x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv :> ∀ x y, Setoid (x ⟶ y)
  ; comp_proper :> ∀ x y z, Proper ((=) ==> (=) ==> (=)) (comp x y z)
  ; comp_assoc :> ArrowsAssociative O
  ; id_l :> ∀ x y, LeftIdentity (comp x y y) cat_id
  ; id_r :> ∀ x y, RightIdentity (comp x x y) cat_id }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)
Arguments comp_assoc {O arrows eq CatId CatComp Category w x y z} _ _ _ : rename.

Section morphism_classes.
  Context {A B} {Ae : Equiv A} {Be : Equiv B}.

  Class SemiGroup_Morphism {Aop Bop} (f : A → B) :=
    { sgmor_a : @SemiGroup A Ae Aop
    ; sgmor_b : @SemiGroup B Be Bop
    ; sgmor_setmor :> Setoid_Morphism f
    ; preserves_sg_op : ∀ x y, f (x & y) = f x & f y }.

  Class JoinSemiLattice_Morphism {Ajoin Bjoin} (f : A → B) :=
    { join_slmor_a : @JoinSemiLattice A Ae Ajoin
    ; join_slmor_b : @JoinSemiLattice B Be Bjoin
    ; join_slmor_sgmor :> @SemiGroup_Morphism join_is_sg_op join_is_sg_op f }.

  Class MeetSemiLattice_Morphism {Ameet Bmeet} (f : A → B) :=
    { meet_slmor_a : @MeetSemiLattice A Ae Ameet
    ; meet_slmor_b : @MeetSemiLattice B Be Bmeet
    ; meet_slmor_sgmor :> @SemiGroup_Morphism meet_is_sg_op meet_is_sg_op f }.

  Class Monoid_Morphism {Aunit Bunit Aop Bop} (f : A → B) :=
    { monmor_a : @Monoid A Ae Aop Aunit
    ; monmor_b : @Monoid B Be Bop Bunit
    ; monmor_sgmor :> SemiGroup_Morphism f
    ; preserves_mon_unit : f mon_unit = mon_unit }.

  Class BoundedJoinSemiLattice_Morphism {Abottom Bbottom Ajoin Bjoin} (f : A → B) :=
    { bounded_join_slmor_a : @BoundedJoinSemiLattice A Ae Ajoin Abottom
    ; bounded_join_slmor_b : @BoundedJoinSemiLattice B Be Bjoin Bbottom
    ; bounded_join_slmor_monmor :> @Monoid_Morphism bottom_is_mon_unit bottom_is_mon_unit join_is_sg_op join_is_sg_op f }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { semiringmor_a : @SemiRing A Ae Aplus Amult Azero Aone
    ; semiringmor_b : @SemiRing B Be Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor :> @Monoid_Morphism zero_is_mon_unit zero_is_mon_unit plus_is_sg_op plus_is_sg_op f
    ; semiringmor_mult_mor :> @Monoid_Morphism one_is_mon_unit one_is_mon_unit mult_is_sg_op mult_is_sg_op f }.

  Class Lattice_Morphism {Ajoin Ameet Bjoin Bmeet} (f : A → B) :=
    { latticemor_a : @Lattice A Ae Ajoin Ameet
    ; latticemor_b : @Lattice B Be Bjoin Bmeet
    ; latticemor_join_mor :> JoinSemiLattice_Morphism f
    ; latticemor_meet_mor :> MeetSemiLattice_Morphism f }.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class StrongSemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { strong_semiringmor_sr_mor :> @SemiRing_Morphism Aplus Amult Azero Aone Bplus Bmult Bzero Bone f
    ; strong_semiringmor_strong_mor :> StrongSetoid_Morphism f }.
End morphism_classes.

Section jections.
  Context {A B} {Ae : Equiv A} {Aap : Apart A} 
    {Be : Equiv B} {Bap : Apart B} (f : A → B) `{inv : !Inverse f}.

  Class StrongInjective : Prop :=
    { strong_injective : ∀ x y, x ≶ y → f x ≶ f y
    ; strong_injective_mor : StrongSetoid_Morphism f }.

  Class Injective : Prop :=
    { injective : ∀ x y, f x = f y → x = y
    ; injective_mor : Setoid_Morphism f }.

  Class Surjective : Prop :=
    { surjective : f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *)
    ; surjective_mor : Setoid_Morphism f }.

  Class Bijective : Prop :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective }.
End jections.
*)
