Require Import abstract_algebra.

Class Dot A B := dot : A → B → B.
Instance: Params (@dot) 3.
Infix "·" := dot (at level 40).
Notation "(·)" := dot (only parsing).
Notation "( x ·)" := (dot x) (only parsing).
Notation "(· x )" := (λ y, y · x) (only parsing).
Typeclasses Transparent Dot.

Class Bullet A B := bullet : A → B → A.
Instance: Params (@bullet) 3.
Infix "∙" := bullet (at level 40).
Notation "(∙)" := bullet (only parsing).
Notation "( x ∙)" := (bullet x) (only parsing).
Notation "(∙ x )" := (λ y, y ∙ x) (only parsing).
Typeclasses Transparent Bullet.

Hint Extern 20 (Dot    ?A ?A) => eexact (@mult A _) : typeclass_instances.
Hint Extern 20 (Bullet ?A ?A) => eexact (@mult A _) : typeclass_instances.

Section modules.
  Context {A} {Aplus:Plus A} {Amult:Mult A} {Azero:Zero A} {Aone:One A} {Anegate:Negate A} {Ae:Equiv A}.
  Context {B} {Bplus:Plus B} {Bzero:Zero B} {Bnegate:Negate B} {Be:Equiv B}.
  Context {C} {Cplus:Plus C} {Cmult:Mult C} {Czero:Zero C} {Cone:One C} {Cnegate:Negate C} {Ce:Equiv C}.
  Context {ABdot : Dot A B}.
  Context {BCbullet : Bullet B C}.

  Context (R:@set A) (M:@set B) (S:@set C).

  Class LeftRngModule : Prop :=
  { lm_rng :>> Rng R
  ; lm_abgroup :>> AdditiveGroup M
  ; lm_dot_proper : Morphism (R ⇒ M ⇒ M) (·)
  ; lm_distr_l : LeftHeteroDistribute  (·) (+) (+) R M
  ; lm_distr_r : RightHeteroDistribute (·) (+) (+) R M
  ; lm_assoc : HeteroAssociative (·) (·) (·) (.*.) R R M
  }.

  Class LeftModule : Prop :=
  { lm_lrm :> LeftRngModule
  ; lm_ring :>> Ring R
  ; lm_identity : LeftIdentity (·) 1 M
  }.

  Class RightRngModule : Prop :=
  { rm_rng :>> Rng S
  ; rm_abgroup :>> AdditiveGroup M
  ; rm_bullet_proper : Morphism (M ⇒ S ⇒ M) (∙)
  ; rm_distr_l : LeftHeteroDistribute  (∙) (+) (+) M S
  ; rm_distr_r : RightHeteroDistribute (∙) (+) (+) M S
  ; rm_assoc : HeteroAssociative (∙) (.*.) (∙) (∙) M S S
  }.

  Class RightModule : Prop :=
  { rm_rrm :> RightRngModule
  ; rm_ring :>> Ring S
  ; rm_identity : RightIdentity (∙) 1 M
  }.

  Class BiModule : Prop :=
  { bm_lm :>> LeftModule
  ; bm_rm :>> RightModule
  ; bm_assoc : HeteroAssociative (·) (∙) (∙) (·) R M S
  }.
End modules.

Notation Module := LeftModule.

Hint Extern 2 (Morphism _ (·)) => eapply @lm_dot_proper : typeclass_instances.
Hint Extern 2 (Morphism _ (∙)) => eapply @rm_bullet_proper : typeclass_instances.

Hint Extern 2 (LeftHeteroDistribute (·) (+) (+) _ _)      => eapply @lm_distr_l : typeclass_instances.
Hint Extern 2 (RightHeteroDistribute (·) (+) (+) _ _)     => eapply @lm_distr_r : typeclass_instances.
Hint Extern 2 (HeteroAssociative (·) (·) (·) (.*.) _ _ _) => eapply @lm_assoc   : typeclass_instances.
Hint Extern 2 (LeftIdentity (·) 1 _)                      => eapply @lm_identity: typeclass_instances.
Hint Extern 2 (LeftHeteroDistribute  (∙) (+) (+) _ _)     => eapply @rm_distr_l : typeclass_instances.
Hint Extern 2 (RightHeteroDistribute (∙) (+) (+) _ _)     => eapply @rm_distr_r : typeclass_instances.
Hint Extern 2 (HeteroAssociative (∙) (.*.) (∙) (∙) _ _ _) => eapply @rm_assoc   : typeclass_instances.
Hint Extern 2 (RightIdentity (∙) 1 _)                     => eapply @rm_identity: typeclass_instances.
Hint Extern 2 (HeteroAssociative (·) (∙) (∙) (·) _ _ _)   => eapply @bm_assoc   : typeclass_instances.

Arguments lm_distr_l  {A _ _ _ _ _   B _ _ _ _                _   R M   _} x {_} y {_} z {_}.
Arguments lm_distr_r  {A _ _ _ _ _   B _ _ _ _                _   R M   _} x {_} y {_} z {_}.
Arguments lm_assoc    {A _ _ _ _ _   B _ _ _ _                _   R M   _} x {_} y {_} z {_}.
Arguments lm_identity {A _ _ _ _ _ _ B _ _ _ _                _   R M   _} y {_}.
Arguments rm_distr_l  {              B _ _ _ _ C _ _ _ _ _      _   M S _} x {_} y {_} z {_}.
Arguments rm_distr_r  {              B _ _ _ _ C _ _ _ _ _      _   M S _} x {_} y {_} z {_}.
Arguments rm_assoc    {              B _ _ _ _ C _ _ _ _ _      _   M S _} x {_} y {_} z {_}.
Arguments rm_identity {              B _ _ _ _ C _ _ _ _ _ _    _   M S _} x {_}.
Arguments bm_assoc    {A _ _ _ _ _ _ B _ _ _ _ C _ _ _ _ _ _  _ _ R M S _} x {_} y {_} z {_}.

Section associative_algebras.
  Context {B} {Bplus:Plus B} {Bmult:Mult B} {Bzero:Zero B} {Bone:One B} {Bnegate:Negate B} {Be:Equiv B}.
  Context {T} {Tplus:Plus T} {Tmult:Mult T} {Tzero:Zero T} {Tone:One T} {Tnegate:Negate T} {Te:Equiv T}.
  Context {BTdot : Dot B T}.

  Context (R:@set B) (A:@set T).

  (* Redundant axioms, but conveninet instance declarations. *)
  Class AssociativeAlgebra : Prop :=
  { aa_module :>> Module R A
  ; aa_comm_ring :>> CommutativeRing R
  ; aa_rng :>> Rng A
  ; aa_linear_l : HeteroAssociative (·) (.*.) (.*.) (·) R A A
  ; aa_linear_r : HeteroAssociative (.*.) (λ x r, r · x) (λ x r, r · x) (.*.) A A R
  }.

  Class CommutativeAlgebra : Prop :=
  { ca_aa :>> AssociativeAlgebra
  ; ca_comm : Commutative (.*.) A
  }.

  Class UnitalAssociativeAlgebra : Prop :=
  { uaa_aa :>> AssociativeAlgebra
  ; uaa_ring :>> Ring A
  }.

  Class UnitalCommutativeAlgebra : Prop :=
  { uca_aa :>> AssociativeAlgebra
  ; uca_commring :>> CommutativeRing A
  }.
End associative_algebras.
Hint Extern 2 (HeteroAssociative (·) (.*.) (.*.) (·) ?R ?A ?A) => eapply @aa_linear_l : typeclass_instances.
Hint Extern 2 (HeteroAssociative (.*.) (λ x r, r · x) (λ x r, r · x) (.*.) ?A ?A ?R) => eapply @aa_linear_r : typeclass_instances.

Arguments aa_linear_l {B _ _ _ _ _ _ T _ _ _ _ _ _ R A _} _ {_} _ {_} _ {_}.
Arguments aa_linear_r {B _ _ _ _ _ _ T _ _ _ _ _ _ R A _} _ {_} _ {_} _ {_}.

Section module_morphism_classes.
  Context {A} {Aplus:Plus A} {Amult:Mult A} {Azero:Zero A} {Aone:One A} {Anegate:Negate A} {Ae:Equiv A}.
  Context {C} {Cplus:Plus C} {Cmult:Mult C} {Czero:Zero C} {Cone:One C} {Cnegate:Negate C} {Ce:Equiv C}.

  Context {B1 B2} {B1e:Equiv B1} {B2e:Equiv B2}.
  Context {B1plus:Plus B1} {B2plus:Plus B2}.
  Context {B1zero:Zero B1} {B2zero:Zero B2}.
  Context {B1negate:Negate B1} {B2negate:Negate B2}.

  Context {AB1dot : Dot A B1} {AB2dot : Dot A B2}.
  Context {B1Cbullet : Bullet B1 C} {B2Cbullet : Bullet B2 C}.

  Class Module_Morphism R M₁ M₂ f :=
    { modmor_a : LeftRngModule (A:=A) (B:=B1) R M₁
    ; modmor_b : LeftRngModule (A:=A) (B:=B2) R M₂
    ; modmor_plus_mor :>> AdditiveSemiGroup_Morphism M₁ M₂ f
    ; modmor_preserves_dot `{r ∊ R} `{x ∊ M₁} : f (r · x) = r · f x 
    }.

  Class RightModule_Morphism M₁ M₂ S f :=
    { rmodmor_a : RightRngModule (B:=B1) (C:=C) M₁ S
    ; rmodmor_b : RightRngModule (B:=B2) (C:=C) M₂ S
    ; rmodmor_plus_mor :>> AdditiveSemiGroup_Morphism M₁ M₂ f
    ; rmodmor_preserves_bullet `{x ∊ M₁} `{r ∊ S} : f (x ∙ r) = f x ∙ r
    }.

  Class BiModule_Morphism R M₁ M₂ S f :=
    { bimodmor_l :>>      Module_Morphism R M₁ M₂   f
    ; bimodmor_r :>> RightModule_Morphism   M₁ M₂ S f
    }.

End module_morphism_classes.

Definition preserves_dot `{M₁:set} `{M₂:set} {f : M₁ ⇀ M₂}
  `{Module_Morphism (B1:=_) (B2:=_) (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=f)}
  r `{r ∊ R} x `{x ∊ M₁} := modmor_preserves_dot (r:=r) (x:=x).

Definition preserves_bullet `{M₁:set} `{M₂:set} {f : M₁ ⇀ M₂} `{S:set}
  `{RightModule_Morphism (B1:=_) (B2:=_) (C:=_) (M₁:=M₁) (M₂:=M₂) (S:=S) (f:=f)}
  x `{x ∊ M₁} r `{r ∊ S} := rmodmor_preserves_bullet (x:=x) (r:=r).
