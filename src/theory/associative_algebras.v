Require Import
  abstract_algebra interfaces.modules theory.setoids theory.products
  theory.common_props theory.jections
  theory.groups theory.rings theory.modules.

(** Properness of structure predicates *)

Local Hint Extern 20 (Subset ?X ?Y) =>
  match goal with E : X = Y |- _ => rewrite E
                | E : Y = X |- _ => rewrite E
  end : typeclass_instances.

Lemma assoc_alg_proper: Find_Proper_Signature (@AssociativeAlgebra) 0
  (∀ B Bplus Bmult Bzero Bone Bnegate Be
     T Tplus Tmult Tzero      Tnegate Te
     BTdot, Proper ((=)==>(=)==>impl)
       (@AssociativeAlgebra B Bplus Bmult Bzero Bone Bnegate Be
                            T Tplus Tmult Tzero      Tnegate Te
                            BTdot)).
Proof with apply _. red; intros. intros R1 R2 ER A1 A2 EA ?. split.
+ rewrite <-ER,<-EA...
+ rewrite <-ER...
+ rewrite <-EA...
+ rewrite <-ER, <-EA...
+ rewrite <-ER, <-EA...
Qed.
Hint Extern 0 (Find_Proper_Signature (@AssociativeAlgebra) 0 _) => eexact assoc_alg_proper : typeclass_instances.

Lemma comm_alg_proper: Find_Proper_Signature (@CommutativeAlgebra) 0
  (∀ B Bplus Bmult Bzero Bone Bnegate Be
     T Tplus Tmult Tzero      Tnegate Te
     BTdot, Proper ((=)==>(=)==>impl)
       (@CommutativeAlgebra B Bplus Bmult Bzero Bone Bnegate Be
                            T Tplus Tmult Tzero      Tnegate Te
                            BTdot)).
Proof with apply _. red; intros. intros R1 R2 ER A1 A2 EA ?. split.
+ rewrite <-ER,<-EA...
+ rewrite <-EA. exact (ca_comm _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeAlgebra) 0 _) => eexact comm_alg_proper : typeclass_instances.

Lemma unital_assoc_alg_proper: Find_Proper_Signature (@UnitalAssociativeAlgebra) 0
  (∀ B Bplus Bmult Bzero Bone Bnegate Be
     T Tplus Tmult Tzero Tone Tnegate Te
     BTdot, Proper ((=)==>(=)==>impl)
       (@UnitalAssociativeAlgebra B Bplus Bmult Bzero Bone Bnegate Be
                                  T Tplus Tmult Tzero Tone Tnegate Te
                                  BTdot)).
Proof with apply _. red; intros. intros R1 R2 ER A1 A2 EA ?. split.
+ rewrite <-ER,<-EA...
+ rewrite <-EA...
Qed.
Hint Extern 0 (Find_Proper_Signature (@UnitalAssociativeAlgebra) 0 _) => eexact unital_assoc_alg_proper : typeclass_instances.

Lemma unital_comm_alg_proper: Find_Proper_Signature (@UnitalCommutativeAlgebra) 0
  (∀ B Bplus Bmult Bzero Bone Bnegate Be
     T Tplus Tmult Tzero Tone Tnegate Te
     BTdot, Proper ((=)==>(=)==>impl)
       (@UnitalCommutativeAlgebra B Bplus Bmult Bzero Bone Bnegate Be
                                  T Tplus Tmult Tzero Tone Tnegate Te
                                  BTdot)).
Proof with apply _. red; intros. intros R1 R2 ER A1 A2 EA ?. split.
+ rewrite <-ER,<-EA...
+ rewrite <-EA...
Qed.
Hint Extern 0 (Find_Proper_Signature (@UnitalCommutativeAlgebra) 0 _) => eexact unital_comm_alg_proper : typeclass_instances.

(* Build structures from fewer axioms *)
Section alt_build.
  Context {B} {Bplus:Plus B} {Bmult:Mult B} {Bzero:Zero B} {Bone:One B} {Bnegate:Negate B} {Be:Equiv B}.
  Context {T} {Tplus:Plus T} {Tmult:Mult T} {Tzero:Zero T} {Tone:One T} {Tnegate:Negate T} {Te:Equiv T}.
  Context {BTdot : Dot B T}.

  Context {R:@set B} {A:@set T}.

  Lemma assoc_alg_from_module :
    Module R A
  → Commutative (.*.) R
  → Morphism (A ⇒ A ⇒ A) (.*.)
  → Associative (.*.) A
  → (∀ `{x ∊ A}, Module_Morphism R A A (x *.))
  → (∀ `{y ∊ A}, Module_Morphism R A A (.* y))
  → AssociativeAlgebra R A.
  Proof. intros.
    assert (∀ `{x ∊ A} `{y ∊ A}, x*y ∊ A) by now apply binary_morphism_closed.
    intros. split; try apply _. now apply (comring_from_ring).
    split; try apply _. split; try apply _.
  + intros x ? y ? z ?. exact (preserves_plus _ _).
  + intros x ? y ? z ?. exact (preserves_plus (f:=(.* z)) _ _).
  + intros r ? x ? y ?. subsymmetry. exact (preserves_dot (f:=(.* y)) _ _).
  + intros x ? y ? r ?. exact (preserves_dot _ _).
  Qed.

  Lemma unital_assoc_alg_from_module :
    Module R A
  → Commutative (.*.) R
  → Morphism (A ⇒ A ⇒ A) (.*.)
  → Associative (.*.) A
  → (∀ `{x ∊ A}, Module_Morphism R A A (x *.))
  → (∀ `{y ∊ A}, Module_Morphism R A A (.* y))
  → 1 ∊ A
  → LeftIdentity (.*.) 1 A
  → RightIdentity (.*.) 1 A
  → UnitalAssociativeAlgebra R A.
  Proof. intros. assert (AssociativeAlgebra R A) by now apply assoc_alg_from_module.
    do 2 split; try apply _.
  Qed.

  Lemma unital_assoc_alg_from_ring 
    `{!CommutativeRing R} `{!Ring A} (f:R ⇀ A) `{!SemiRing_Morphism R A f} :
    Morphism (R ⇒ A ⇒ A) (·)
  → (∀ `{r ∊ R} `{x ∊ A}, f r * x = x * f r)
  → (∀ `{r ∊ R} `{x ∊ A}, r · x = f r * x)
  → UnitalAssociativeAlgebra R A.
  Proof. intros ? comm dotdef.
    assert (∀ `{r ∊ R} `{x ∊ A}, r · x ∊ A) by now apply binary_morphism_closed.
    assert (Proper ((R,=)==>(A,=)==>(A,=)) (·)) by now apply binary_morphism_proper.
    do 2 split; try apply _. split; try apply _. split; try apply _.
  + intros r ? x ? y ?. rewrite 3!(_ $ dotdef _ _ _ _). exact (plus_mult_distr_l _ _ _).
  + intros r ? s ? x ?. rewrite 3!(_ $ dotdef _ _ _ _), (_ $ preserves_plus _ _). exact (plus_mult_distr_r _ _ _).
  + intros r ? s ? x ?. rewrite 3!(_ $ dotdef _ _ _ _), (_ $ preserves_mult _ _). exact (associativity (.*.) _ _ _).
  + intros x ?. rewrite (_ $ dotdef _ _ _ _), (_ $ preserves_1). exact (mult_1_l _).
  + intros r ? x ? y ?. rewrite 2!(_ $ dotdef _ _ _ _). exact (associativity (.*.) _ _ _).
  + intros x ? y ? r ?. rewrite 2!(_ $ dotdef _ _ _ _), 2!(_ $ associativity (.*.) _ _ _).
    now rewrite (_ $ comm r _ x _).
  Qed.

  Lemma unital_comm_alg_from_ring 
    `{!CommutativeRing R} `{!CommutativeRing A} (f:R ⇀ A) `{!SemiRing_Morphism R A f} :
    Morphism (R ⇒ A ⇒ A) (·)
  → (∀ `{r ∊ R} `{x ∊ A}, r · x = f r * x)
  → UnitalCommutativeAlgebra R A.
  Proof. intros. split; try apply _. cut (UnitalAssociativeAlgebra R A). intro. apply _.
    apply (unital_assoc_alg_from_ring f); trivial.
    intros r ? x ?. exact (commutativity (.*.) _ _).
  Qed.

End alt_build.

(* Deducible instances *)

Instance unital_comm_alg_is_comm_alg `{UnitalCommutativeAlgebra (R:=R) (A:=A)}
  : CommutativeAlgebra R A := {}.

Instance unital_comm_alg_is_unital_assoc_alg `{UnitalCommutativeAlgebra (R:=R) (A:=A)}
  : UnitalAssociativeAlgebra R A := {}.

(* Commutative rings are unital commutative algebras over themselves *)

Lemma unital_comm_alg_self `{CommutativeRing (R:=R)} : UnitalCommutativeAlgebra R R.
Proof. apply (unital_comm_alg_from_ring id); unfold dot; try apply _. now intros. Qed.
Hint Extern 2 (UnitalCommutativeAlgebra ?R ?R) => eapply unital_comm_alg_self : typeclass_instances.
Hint Extern 2 (AssociativeAlgebra ?R ?R) => eapply uca_aa : typeclass_instances.

Section fun_ops.
  Context `{LeftModule (R:=R) (M:=M)}.

  Global Instance endo_mult : Mult (M ⇀ M) := (∘).
  Global Instance endo_one  : One  (M ⇀ M) := id.
End fun_ops.

Section endomorphism_ring.
  Context `{LeftModule (R:=R) (M:=M)}.
  Context `{!Commutative (.*.) R}.

  Notation End := (Module_Morphism R M M : @set (M ⇀ M)).

  Instance : Module R End := _.

  Instance : CommutativeRing R := comring_from_ring _.

  Ltac red_mor_els :=
    repeat match goal with H : _ ∊ Module_Morphism R M M |- _ => red in H end.

  Instance : 1 ∊ End := _ : Module_Morphism R M M id.

  Hint Extern 10 (Module_Morphism R M M ?f) => change (f ∊ End) : typeclass_instances.
  Instance: ∀ `{f ∊ End}, Morphism (M ⇒ M) f.
  Proof. intros f el. red in el. apply _. Qed.

  (*Hint Extern 50 (_ ∊ End) => red : typeclass_instances.*)

  Instance : ∀ `{f ∊ End} `{g ∊ End}, f*g ∊ End.
  Proof. intros f ? g ?. unfold mult, endo_mult. red. red_mor_els. apply _. Qed.

  Instance : Morphism (End ⇒ End ⇒ End) (.*.).
  Proof. eapply @binary_morphism_proper_back. apply _. apply _.
    intros g1 g2 Eg f1 f2 Ef. unfold_sigs. red_sig. red_mor_els. unfold mult, endo_mult.
    rewrite Ef, Eg. subreflexivity.
  Qed.

  Instance : Associative (.*.) End.
  Proof. intros f ? g ? h ?. unfold mult, endo_mult. subreflexivity. Qed.

  Instance : Ring End.
  Proof. split; try apply _. split; try apply _. split; try apply _.
  + intros f ? g ? h ? ? x Ex. unfold_sigs. red_sig. rewrite (_ $ Ex). red_mor_els.
    exact (preserves_plus (g x) (h x)).
  + intros f ? g ? h ? ? x Ex. unfold_sigs. red_sig. rewrite (_ $ Ex). red_mor_els.
    change (f (h x) + g (h x) = f (h x) + g (h x)). subreflexivity.
  + intros f ?. red_mor_els. change (f=f). subreflexivity.
  + intros f ?. red_mor_els. change (f=f). subreflexivity.
  Qed.

  Instance : SemiRing_Morphism R End (λ r, r · 1).
  Proof. apply (ring_morphism_alt _).
  + intros ?? E. unfold_sigs. red_sig.
    pose proof _ : Proper ((R,=)==>(End,=)==>(End,=)) dot. 
    rewrite (R $ E). subreflexivity.
  + intros r ? s ?. exact (lm_distr_r (M:=End) _ _ _).
  + intros r ? s ?.
    rewrite <-(End $ lm_assoc (M:=End) _ _ _).
    subreflexivity.
  + exact (lm_identity (M:=End) _).
  Qed.

  Global Instance endomorphism_algebra : UnitalAssociativeAlgebra R End.
  Proof. apply (unital_assoc_alg_from_ring (R:=R) (A:=End) (λ r, r · 1)). apply _.
  + intros r ? f ? ? x Ex. unfold_sigs. red_sig. rewrite (_ $ Ex). subsymmetry.
    red_mor_els. exact (preserves_dot _ _).
  + intros r ? f ?. subreflexivity.
  Qed.
End endomorphism_ring.
