Require Export
  canonical_names restrict_rel find_proper interfaces.common_props
  util decision propholds.

Class Setoid `{Ae : Equiv A} S : Prop := setoid_eq : SubEquivalence S (=).
Hint Extern 2 (SubEquivalence _ (=)) => eapply @setoid_eq : typeclass_instances.

Class InequalitySetoid `{Ae : Equiv A} {Aue : UnEq A} S : Prop :=
  { uneq_setoid :>> Setoid S
  ; uneq_proper : Proper ((S,=) ==> (S,=) ==> impl) (≠)
  ; uneq_ne   x `{x ∊ S} y `{y ∊ S} : x ≠ y → ¬ x = y
  ; equiv_nue x `{x ∊ S} y `{y ∊ S} : x = y → ¬ x ≠ y
  }.

Class StrongSetoid `{Ae : Equiv A} {Aue : UnEq A} S : Prop :=
  { strongsetoid_apart : SubApartness S (≠)
  ; strongsetoid_tightapart :> TightApart S
  }.
Hint Extern 2 (SubApartness _ (≠)) => eapply @strongsetoid_apart: typeclass_instances.

Class SubSetoid `{Ae: Equiv A} S T : Prop :=
  { subsetoid_a :>> Setoid S  (* derivable from the other axioms, but convenient *)
  ; subsetoid_b :   Setoid T
  ; subsetoid_regular : Proper ((T,=) ==> impl) (∊ S)
  ; subsetoid_subset : SubsetOf S T
  }.
Hint Extern 4 (SubsetOf _ _) => eapply @subsetoid_subset : typeclass_instances.
Notation "S ⊆ T" := (SubSetoid S T) (at level 70) : mc_scope.
Notation "(⊆)" := (SubSetoid) (only parsing) : mc_scope.
Notation "( S ⊆)" := (SubSetoid S) (only parsing) : mc_scope.
Notation "(⊆ T )" := ((λ S, S ⊆ T) : Subset) (only parsing) : mc_scope.
(* Hint Extern 2 (?x ⊆ ?x) => reflexivity : typeclass_instances.
Hint Extern 2 (?x ⊆ ?y) => auto_trans : typeclass_instances. *)
Notation " ( S ,⊆) " := (restrict_rel S (⊆)) : signature_scope.
Notation "S ⊆ T ⊆ U" := (S ⊆ T ∧ T ⊆ U) (at level 70, T at next level) : mc_scope.

Hint Extern 2 (Equiv (elt_type (⊆ _))) => eapply @subset_equiv : typeclass_instances.


Definition morphism {A B} (X:Subset) (Y:Subset) `{Equiv X} `{Equiv Y} : @Subset (A → B) := λ f, (@equiv (X ⇀ Y) _) f f.
Infix "⇒" := morphism (at level 65, right associativity) : mc_scope.
Class Morphism `(S:Subset) f := morphism_prf : f ∊ S.
Hint Extern 0 (_ ∊ _ ⇒ _) => eapply @morphism_prf : typeclass_instances.
Hint Extern 0 (Equiv (elt_type (?X ⇒ ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.

Class Strong_Morphism {A B} `{UnEq A} `{UnEq B} (X:@Subset A) (Y:@Subset B) f : Prop :=
  { strong_morphism_closed : Closed (X ⇀ Y) f
  ; strong_morphism_proper : strong_ext_equiv f f
  }.

Class Strong_Binary_Morphism {A B C} `{UnEq A} `{UnEq B} `{UnEq C} (X:@Subset A) (Y:@Subset B) (Z:@Subset C) f : Prop :=
  { strong_binary_morphism_closed : Closed (X ⇀ Y ⇀ Z) f
  ; strong_binary_morphism_proper : strong_ext_equiv (uncurry f) (uncurry f)
  }.

Section groups.

  Context {A} {op: SgOp A} {unit: MonUnit A} {Ainv: Inv A} {Ae: Equiv A} {Aue: UnEq A}.

  Class SemiGroup S : Prop :=
    { sg_setoid    :> Setoid S
    ; sg_ass       : Associative (&) S
    ; sg_op_proper : Morphism (S ⇒ S ⇒ S) (&)
    }.

  Class CommutativeSemiGroup S : Prop :=
    { comsg_sg :>> SemiGroup S
    ; comsg_commutative : Commutative (&) S
    }.

  Class SemiLattice L : Prop :=
    { semilattice_sg :>> CommutativeSemiGroup L
    ; semilattice_idempotent : BinaryIdempotent (&) L
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

  Class BoundedSemiLattice L : Prop :=
    { bounded_semilattice_mon :>> CommutativeMonoid L
    ; bounded_semilattice_idempotent : BinaryIdempotent (&) L
    }.

  Class Group G : Prop :=
    { group_monoid :>> Monoid G
    ; inverse_proper : Morphism (G ⇒ G) (⁻¹)
    ; inverse_l : LeftInverse  (&) (⁻¹) mon_unit G
    ; inverse_r : RightInverse (&) (⁻¹) mon_unit G
    }.

  Class AbGroup G : Prop :=
    { abgroup_commonoid :>> CommutativeMonoid G
    ; abgroup_inverse_proper : Morphism (G ⇒ G) (⁻¹)
    ; abgroup_inverse_l      : LeftInverse  (&) (⁻¹) mon_unit G
    }.

  Class StrongSemiGroupOp S : Prop :=
    { strong_sg_op_strongsetoid :>> StrongSetoid S
    ; strong_sg_op_proper : Strong_Binary_Morphism S S S (&)
    }.

End groups.
Hint Extern 0 (Associative (&) _) => class_apply @sg_ass : typeclass_instances.
Hint Extern 0 (Morphism _ (&)) => class_apply @sg_op_proper : typeclass_instances.
Hint Extern 0 (Commutative (&) _) => class_apply @comsg_commutative : typeclass_instances.
Hint Extern 0 (BinaryIdempotent (&) _) => class_apply @semilattice_idempotent : typeclass_instances.
Hint Extern 0 (mon_unit ∊ _) => class_apply @monoid_unit_exists : typeclass_instances.
Hint Extern 0 (LeftIdentity  (&) _ _) => class_apply @monoid_left_id : typeclass_instances.
Hint Extern 0 (RightIdentity (&) _ _) => class_apply @monoid_right_id : typeclass_instances.
Hint Extern 5 (Morphism _ (⁻¹)) => class_apply @inverse_proper : typeclass_instances.
Hint Extern 0 (LeftInverse  (&) _ _ _) => class_apply @inverse_l : typeclass_instances.
Hint Extern 0 (RightInverse (&) _ _ _) => class_apply @inverse_r : typeclass_instances.
Hint Extern 0 (Strong_Binary_Morphism _ _ _ (&)) => class_apply @strong_sg_op_proper : typeclass_instances.

Arguments inverse_l {A op unit Ainv Ae G Group} _ {_}.
Arguments inverse_r {A op unit Ainv Ae G Group} _ {_}.

Notation MeetSemiLattice := (SemiLattice (op:=meet_is_sg_op)).
Notation JoinSemiLattice := (SemiLattice (op:=join_is_sg_op)).
Notation BoundedMeetSemiLattice := (BoundedSemiLattice (op:=meet_is_sg_op) (unit:=top_is_mon_unit)).
Notation BoundedJoinSemiLattice := (BoundedSemiLattice (op:=join_is_sg_op) (unit:=bottom_is_mon_unit)).

Section lattice.
  Context {A} {Ajoin: Join A} {Ameet: Meet A} {Ae: Equiv A}.

  Class Lattice L : Prop := 
    { lattice_join :>> JoinSemiLattice L
    ; lattice_meet :>> MeetSemiLattice L
    ; join_meet_absorption : Absorption (⊔) (⊓) L L 
    ; meet_join_absorption : Absorption (⊓) (⊔) L L
    }.

  Class DistributiveLattice L : Prop := 
    { distr_lattice_lattice :>> Lattice L
    ; join_meet_distr_l : LeftDistribute (⊔) (⊓) L
    }.
End lattice.

Hint Extern 0 (Associative (⊓) _) => eapply (@sg_ass _ meet_is_sg_op) : typeclass_instances.
Hint Extern 0 (Associative (⊔) _) => eapply (@sg_ass _ join_is_sg_op) : typeclass_instances.
Hint Extern 0 (Morphism _ (⊓)) => eapply (@sg_op_proper _ meet_is_sg_op) : typeclass_instances.
Hint Extern 0 (Morphism _ (⊔)) => eapply (@sg_op_proper _ join_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (⊓) _) => eapply (@comsg_commutative _ meet_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (⊔) _) => eapply (@comsg_commutative _ join_is_sg_op) : typeclass_instances.
Hint Extern 0 (BinaryIdempotent (⊓) _) => eapply (@semilattice_idempotent _ meet_is_sg_op) : typeclass_instances.
Hint Extern 0 (BinaryIdempotent (⊔) _) => eapply (@semilattice_idempotent _ join_is_sg_op) : typeclass_instances.
Hint Extern 5 (⊤ ∊ _) => eapply (@monoid_unit_exists _ meet_is_sg_op top_is_mon_unit) : typeclass_instances.
Hint Extern 5 (⊥ ∊ _) => eapply (@monoid_unit_exists _ join_is_sg_op bottom_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (⊔) _ _) => eapply (@monoid_left_id  _ join_is_sg_op bottom_is_mon_unit) : typeclass_instances.
Hint Extern 0 (RightIdentity (⊔) _ _) => eapply (@monoid_right_id _ join_is_sg_op bottom_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (⊓) _ _) => eapply (@monoid_left_id  _ meet_is_sg_op top_is_mon_unit) : typeclass_instances.
Hint Extern 0 (RightIdentity (⊓) _ _) => eapply (@monoid_right_id _ meet_is_sg_op top_is_mon_unit) : typeclass_instances.

Hint Extern 0 (Absorption (⊔) (⊓) _ _) => class_apply @join_meet_absorption : typeclass_instances.
Hint Extern 0 (Absorption (⊓) (⊔) _ _) => class_apply @meet_join_absorption : typeclass_instances.
Hint Extern 0 (LeftDistribute (⊔) (⊓) _) => class_apply @join_meet_distr_l : typeclass_instances.

Arguments join_meet_absorption {A _ _ _ L _} _ {_} _ {_}.
Arguments meet_join_absorption {A _ _ _ L _} _ {_} _ {_}.
Arguments join_meet_distr_l    {A _ _ _ L _} _ {_} _ {_} _ {_}.


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

  Class StrongRngOps R : Prop :=
    { strong_rng_ops_strongsetoid :>> StrongSetoid R
    ; strong_rng_ops_plus : Strong_Binary_Morphism R R R (+)
    ; strong_rng_ops_mult : Strong_Binary_Morphism R R R (.*.)
    }.

  Class IntegralDomain D : Prop :=
    { intdom_comring :>> CommutativeRing D
    ; intdom_strong :>> StrongRngOps D
    ; intdom_nontrivial : 1 ∊ D ₀
    ; intdom_nozeroes : Closed (D ₀ ⇀ D ₀ ⇀ D ₀) (.*.)
    }.

  Class Field F : Prop :=
    { field_cring :>> CommutativeRing F
    ; field_strong :>> StrongRngOps F
    ; field_nontrivial : 1 ∊ F ₀
    ; field_inv_proper : Morphism (F ₀ ⇒ F ₀) (⁻¹)
    ; field_inv_l      : LeftInverse (.*.) (⁻¹) 1 (F ₀)
    }.

End rings.

Hint Extern 0 (Associative (+)   _) => eapply (@sg_ass _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Associative (.*.) _) => eapply (@sg_ass _ mult_is_sg_op) : typeclass_instances.
Hint Extern 0 (Morphism _ (+)  ) => eapply (@sg_op_proper _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Morphism _ (.*.)) => eapply (@sg_op_proper _ mult_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (+)   _) => eapply (@comsg_commutative _ plus_is_sg_op) : typeclass_instances.
Hint Extern 0 (Commutative (.*.) _) => eapply (@comsg_commutative _ mult_is_sg_op) : typeclass_instances.
Hint Extern 5 (0 ∊ _) => eapply (@monoid_unit_exists _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 5 (1 ∊ _) => eapply (@monoid_unit_exists _ mult_is_sg_op one_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (+) _ _) => eapply (@monoid_left_id  _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 0 (RightIdentity (+) _ _) => eapply (@monoid_right_id _ plus_is_sg_op zero_is_mon_unit) : typeclass_instances.
Hint Extern 0 (LeftIdentity  (.*.) _ _) => eapply (@mult_1_l) : typeclass_instances.
Hint Extern 0 (RightIdentity (.*.) _ _) => eapply (@mult_1_r) : typeclass_instances.
Hint Extern 0 (Morphism _ (-)) => eapply (@inverse_proper _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (LeftInverse  (-) _ _ _) => eapply (@inverse_l _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (RightInverse (-) _ _ _) => eapply (@inverse_r _ plus_is_sg_op zero_is_mon_unit negate_is_inv) : typeclass_instances.
Hint Extern 0 (LeftDistribute  (.*.) (+) _) => eapply @plus_mult_distr_l : typeclass_instances.
Hint Extern 0 (RightDistribute (.*.) (+) _) => eapply @plus_mult_distr_r : typeclass_instances.
Hint Extern 0 (LeftAbsorb  (.*.) _ _) => eapply @mult_0_l : typeclass_instances.
Hint Extern 0 (RightAbsorb (.*.) _ _) => eapply @mult_0_r : typeclass_instances.

Hint Extern 4 (1 ∊ _ ₀) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 4  (_ * _ ∊ _ ₀) => eapply @intdom_nozeroes : typeclass_instances.
Hint Extern 10 (Closed (?D ₀ ⇀ ?D ₀ ⇀ ?D ₀) (.*.)) => eapply @intdom_nozeroes : typeclass_instances.

Hint Extern 5 (Strong_Binary_Morphism _ _ _ (+)  ) => class_apply @strong_rng_ops_plus : typeclass_instances.
Hint Extern 5 (Strong_Binary_Morphism _ _ _ (.*.)) => class_apply @strong_rng_ops_mult : typeclass_instances.
Hint Extern 6 (Morphism _ (⁻¹)) => class_apply @field_inv_proper : typeclass_instances.
Hint Extern 2 (LeftInverse (.*.) _ _ _) => class_apply @field_inv_l : typeclass_instances.

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
  ; sgmor_subsetmor :>> Morphism (S ⇒ T) f
  ; sgmor_preserves_sg_op `{x ∊ S} `{y ∊ S} : f (x & y) = f x & f y
  }.
Definition preserves_sg_op `{S:Subset} `{T:Subset} {f : S ⇀ T}
  `{SemiGroup_Morphism _ _ (S:=S) (T:=T) (f:=f)} x `{x ∊ S} y `{y ∊ S} := sgmor_preserves_sg_op (x:=x) (y:=y).

Class JoinSemiLattice_Morphism {A B Ajoin Bjoin Ae Be} L K f :=
  { join_slmor_a : @SemiLattice A (@join_is_sg_op _ Ajoin) Ae L
  ; join_slmor_b : @SemiLattice B (@join_is_sg_op _ Bjoin) Be K
  ; join_slmor_sgmor :>> @SemiGroup_Morphism A B join_is_sg_op join_is_sg_op Ae Be L K f
  }.

Class MeetSemiLattice_Morphism {A B Ameet Bmeet Ae Be} L K f :=
  { meet_slmor_a : @SemiLattice A (@meet_is_sg_op _ Ameet) Ae L
  ; meet_slmor_b : @SemiLattice B (@meet_is_sg_op _ Bmeet) Be K
  ; meet_slmor_sgmor :>> @SemiGroup_Morphism A B meet_is_sg_op meet_is_sg_op Ae Be L K f
  }.

Class Monoid_Morphism {A B Aop Bop Aunit Bunit Ae Be} M N f :=
  { monmor_a : @Monoid A Aop Aunit Ae M
  ; monmor_b : @Monoid B Bop Bunit Be N
  ; monmor_sgmor :>> SemiGroup_Morphism M N f
  ; monmor_preserves_mon_unit : f mon_unit = mon_unit
  }.
Definition preserves_mon_unit `{M:Subset} `{N:Subset} {f : M ⇀ N}
  `{Monoid_Morphism _ _ (M:=M) (N:=N) (f:=f)} := monmor_preserves_mon_unit.

Class BoundedJoinSemiLattice_Morphism {A B Ajoin Bjoin Abottom Bbottom Ae Be} L K f :=
  { bounded_join_slmor_a : @BoundedSemiLattice A (@join_is_sg_op _ Ajoin) (@bottom_is_mon_unit _ Abottom) Ae L
  ; bounded_join_slmor_b : @BoundedSemiLattice B (@join_is_sg_op _ Bjoin) (@bottom_is_mon_unit _ Bbottom) Be K
  ; bounded_join_slmor_monmor :>> @Monoid_Morphism A B join_is_sg_op join_is_sg_op bottom_is_mon_unit bottom_is_mon_unit Ae Be L K f
  }.

Class BoundedMeetSemiLattice_Morphism {A B Ameet Bmeet Atop Btop Ae Be} L K f :=
  { bounded_meet_slmor_a : @BoundedSemiLattice A (@meet_is_sg_op _ Ameet) (@top_is_mon_unit _ Atop) Ae L
  ; bounded_meet_slmor_b : @BoundedSemiLattice B (@meet_is_sg_op _ Bmeet) (@top_is_mon_unit _ Btop) Be K
  ; bounded_meet_slmor_monmor :>> @Monoid_Morphism A B meet_is_sg_op meet_is_sg_op top_is_mon_unit top_is_mon_unit Ae Be L K f
  }.

Class Lattice_Morphism {A B Ajoin Bjoin Ameet Bmeet Ae Be} L K f :=
  { latticemor_a : @Lattice A Ajoin Ameet Ae L
  ; latticemor_b : @Lattice B Bjoin Bmeet Be K
  ; latticemor_join_mor :>> JoinSemiLattice_Morphism L K f
  ; latticemor_meet_mor :>> MeetSemiLattice_Morphism L K f
  }.

Notation AdditiveSemiGroup_Morphism := (SemiGroup_Morphism (Aop:=plus_is_sg_op) (Bop:=plus_is_sg_op)).
Notation AdditiveMonoid_Morphism := (Monoid_Morphism (Aop:=plus_is_sg_op) (Bop:=plus_is_sg_op) (Aunit:=zero_is_mon_unit) (Bunit:=zero_is_mon_unit)).
Notation MultiplicativeSemiGroup_Morphism := (SemiGroup_Morphism (Aop:=mult_is_sg_op) (Bop:=mult_is_sg_op)).

Section ring_morphism_classes.
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
End ring_morphism_classes.
Definition preserves_1 `{SemiRing (R:=R1)} `{SemiRing (R:=R2)} {f : R1 ⇀ R2} `{!SemiRing_Morphism R1 R2 f} := sringmor_preserves_1.

Section jections.
  Context {A B} {Ae:Equiv A} {Aue:UnEq A} {Be:Equiv B} {Bue:UnEq B}.
  Context (S:@Subset A) (T:@Subset B) (f : A → B) {inv : Inverse (f : S ⇀ T)}.

  Open Scope mc_fun_scope.

  Class StrongInjective : Prop :=
    { strong_injective `{x ∊ S} `{y ∊ S} : x ≠ y → f x ≠ f y
    ; strong_injective_mor : Strong_Morphism S T f
    }.

  Class Injective : Prop :=
    { injective_def `{x ∊ S} `{y ∊ S} : f x = f y → x = y
    ; injective_mor : Morphism (S ⇒ T) f
    }.

  Class Surjective : Prop :=
    { surjective : (f : S ⇀ T) ∘ f⁻¹ = id (* a.k.a. "split-epi" *)
    ; surjective_mor : Morphism (S ⇒ T) f
    ; surjective_closed : Closed (T ⇀ S) (f⁻¹)
    }.

  Class Bijective : Prop :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective
    }.
End jections.
Arguments strong_injective {A B Aue Bue S T} f {_} x {_} y {_} _.
Arguments strong_injective_mor {A B Aue Bue S T} f {_}.
(* Arguments injective {A B Ae Be S T} f {_} x {_} y {_} _. *)
Arguments injective_mor {A B Ae Be S T} f {_} _ _ _.
Arguments surjective {A B Ae Be S T} f {_} {_} _ _ _.
Arguments surjective_mor {A B Ae Be S T} f {_} {_} _ _ _.
Arguments surjective_closed {A B Ae Be S T} f {_} {_} _ {_}.

Definition injective `{S:Subset} `{T:Subset} `{Equiv S} `{Equiv T}
  (f : S ⇀ T) `{!Injective S T f} x `{x ∊ S} y `{y ∊ S} := injective_def S T f (x:=x) (y:=y).

Hint Extern 5 (inverse _ _ ∊ _) => eapply @surjective_closed : typeclass_instances.
