Require Import
  abstract_algebra interfaces.modules theory.setoids theory.products theory.common_props theory.jections
  theory.groups theory.rings.

(** Operations are closed and proper *)

Lemma dot_closed `{LeftRngModule (R:=R) (M:=M)} : Closed (R ⇀ M ⇀ M) (·).
Proof. apply binary_morphism_closed. apply _. Qed.
Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (·)) => eapply @dot_closed : typeclass_instances.
Hint Extern 5 (_ · _ ∊ _) => eapply @dot_closed : typeclass_instances. 

Lemma bullet_closed `{RightRngModule (M:=M) (S:=R)} : Closed (M ⇀ R ⇀ M) (∙).
Proof. apply binary_morphism_closed. apply _. Qed.
Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (∙)) => eapply @bullet_closed : typeclass_instances.
Hint Extern 5 (_ ∙ _ ∊ _) => eapply @bullet_closed : typeclass_instances. 

Lemma dot_proper: Find_Proper_Signature (@dot) 0
  (∀ `{LeftRngModule (R:=R) (M:=M)}, Proper ((R,=)==>(M,=)==>(M,=)) (·)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@dot) 0 _) => eexact dot_proper : typeclass_instances.

Lemma bullet_proper: Find_Proper_Signature (@bullet) 0
  (∀ `{RightRngModule (M:=M) (S:=R)}, Proper ((M,=)==>(R,=)==>(M,=)) (∙)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@bullet) 0 _) => eexact dot_proper : typeclass_instances.

(** Properness of structure predicates *)

Local Hint Extern 20 (Subset ?X ?Y) =>
  match goal with E : X = Y |- _ => rewrite E
                | E : Y = X |- _ => rewrite E
  end : typeclass_instances.

Lemma leftrngmodule_proper: Find_Proper_Signature (@LeftRngModule) 0
  (∀ A Aplus Amult Azero Anegate Ae
     B Bplus Bzero Bnegate Be
     ABdot, Proper ((=)==>(=)==>impl)
       (@LeftRngModule A Aplus Amult Azero Anegate Ae
                       B Bplus Bzero Bnegate Be
                       ABdot)).
Proof with apply _. red; intros. intros R1 R2 ER M1 M2 EM ?. split.
+ rewrite <-ER...
+ rewrite <-EM...
+ rewrite <-(_:Subset (R1 ⇒ M1 ⇒ M1) (R2 ⇒ M2 ⇒ M2))...
+ rewrite <-ER, <-EM...
+ rewrite <-ER, <-EM...
+ rewrite <-ER, <-EM...
Qed.
Hint Extern 0 (Find_Proper_Signature (@LeftRngModule) 0 _) => eexact leftrngmodule_proper : typeclass_instances.

Lemma rightrngmodule_proper: Find_Proper_Signature (@RightRngModule) 0
  (∀ B Bplus Bzero Bnegate Be
     C Cplus Cmult Czero Cnegate Ce
     BCbullet, Proper ((=)==>(=)==>impl)
       (@RightRngModule B Bplus Bzero Bnegate Be
                        C Cplus Cmult Czero Cnegate Ce
                        BCbullet)).
Proof with apply _. red; intros. intros M1 M2 EM S1 S2 ES ?. split.
+ rewrite <-ES...
+ rewrite <-EM...
+ rewrite <-(_:Subset (M1 ⇒ S1 ⇒ M1) (M2 ⇒ S2 ⇒ M2))...
+ rewrite <-ES, <-EM...
+ rewrite <-ES, <-EM...
+ rewrite <-ES, <-EM...
Qed.
Hint Extern 0 (Find_Proper_Signature (@RightRngModule) 0 _) => eexact rightrngmodule_proper : typeclass_instances.

Lemma leftmodule_proper: Find_Proper_Signature (@LeftModule) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae
     B Bplus Bzero Bnegate Be
     ABdot, Proper ((=)==>(=)==>impl)
       (@LeftModule A Aplus Amult Azero Aone Anegate Ae
                    B Bplus Bzero Bnegate Be
                    ABdot)).
Proof with apply _. red; intros. intros R1 R2 ER M1 M2 EM ?. split.
+ rewrite <-ER, <-EM...
+ rewrite <-ER...
+ rewrite <-EM. exact lm_identity.
Qed.
Hint Extern 0 (Find_Proper_Signature (@LeftModule) 0 _) => eexact leftmodule_proper : typeclass_instances.

Lemma rightmodule_proper: Find_Proper_Signature (@RightModule) 0
  (∀ B Bplus Bzero Bnegate Be
     C Cplus Cmult Czero Cone Cnegate Ce
     BCbullet, Proper ((=)==>(=)==>impl)
       (@RightModule B Bplus Bzero Bnegate Be
                     C Cplus Cmult Czero Cone Cnegate Ce
                     BCbullet)).
Proof with apply _. red; intros. intros M1 M2 EM S1 S2 ES ?. split.
+ rewrite <-ES, <-EM...
+ rewrite <-ES...
+ rewrite <-EM. exact rm_identity.
Qed.
Hint Extern 0 (Find_Proper_Signature (@RightModule) 0 _) => eexact rightmodule_proper : typeclass_instances.

Lemma bimodule_proper: Find_Proper_Signature (@BiModule) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae
     B Bplus Bzero Bnegate Be
     C Cplus Cmult Czero Cone Cnegate Ce
     ABdot BCbullet, Proper ((=)==>(=)==>(=)==>impl)
       (@BiModule A Aplus Amult Azero Aone Anegate Ae
                  B Bplus Bzero Bnegate Be
                  C Cplus Cmult Czero Cone Cnegate Ce
                  ABdot BCbullet)).
Proof with apply _. red; intros. intros R1 R2 ER M1 M2 EM S1 S2 ES ?. split.
+ rewrite <-ER, <-EM...
+ rewrite <-ES, <-EM...
+ rewrite <-ER, <-EM, <-ES...
Qed.
Hint Extern 0 (Find_Proper_Signature (@BiModule) 0 _) => eexact bimodule_proper : typeclass_instances.

(* Rings are modules over themselves *)

Lemma leftrngmodule_self `{Rng (R:=R)} : LeftRngModule R R .
Proof. split; try apply _; unfold dot; apply _. Qed.
Hint Extern 2 (LeftRngModule ?R ?R) => eapply leftrngmodule_self : typeclass_instances.

Lemma leftmodule_self `{Ring (R:=R)} : LeftModule R R .
Proof. split; try apply _; unfold dot; apply _. Qed.
Hint Extern 2 (LeftModule ?R ?R) => eapply leftmodule_self : typeclass_instances.

Lemma rightrngmodule_self `{Rng (R:=R)} : RightRngModule R R .
Proof. split; try apply _; unfold bullet; apply _. Qed.
Hint Extern 2 (RightRngModule ?R ?R) => eapply rightrngmodule_self : typeclass_instances.

Lemma rightmodule_self `{Ring (R:=R)} : RightModule R R .
Proof. split; try apply _; unfold bullet; apply _. Qed.
Hint Extern 2 (RightModule ?R ?R) => eapply rightmodule_self : typeclass_instances.

Lemma bimodule_self `{Ring (R:=R)} : BiModule R R R.
Proof. split; try apply _; unfold dot,bullet; apply _. Qed.
Hint Extern 2 (BiModule ?R ?R ?R) => eapply bimodule_self : typeclass_instances.

Section left_rng_module_props.
  Context `{LeftRngModule (R:=R) (M:=M)}.

  Lemma dot_0_l x `{x ∊ M} : 0 · x = 0.
  Proof. apply (left_cancellation (+) (0 · x) M _ _).
    rewrite <-(_ $ lm_distr_r 0 0 x).
    now rewrite 2!(_ $ plus_0_r _).
  Qed.

  Lemma dot_0_r r `{r ∊ R} : r · 0 = 0.
  Proof. apply (left_cancellation (+) (r · 0) M _ _).
    rewrite <-(_ $ lm_distr_l r 0 0).
    now rewrite 2!(_ $ plus_0_r _).
  Qed.

  Lemma negate_dot_l r `{r ∊ R} x `{x ∊ M} : -(r · x) = (-r) · x .
  Proof. apply (left_cancellation (+) (r · x) M _ _).
    rewrite (_ $ plus_negate_r _).
    rewrite <-(_ $ lm_distr_r _ _ x).
    rewrite (_ $ plus_negate_r _).
    subsymmetry. exact (dot_0_l _).
  Qed.

  Lemma negate_dot_r r `{r ∊ R} x `{x ∊ M} : -(r · x) = r · (-x) .
  Proof. apply (left_cancellation (+) (r · x) M _ _).
    rewrite (_ $ plus_negate_r _).
    rewrite <-(_ $ lm_distr_l _ _ _).
    rewrite (_ $ plus_negate_r _).
    subsymmetry. exact (dot_0_r _).
  Qed.
End left_rng_module_props.

Section left_module_props.
  Context `{LeftModule (R:=R) (M:=M)}.

  Lemma negate_dot x `{x ∊ M} : -x = -1 · x.
  Proof. now rewrite <-(_ $ negate_dot_l _ _), (_ $ lm_identity _). Qed.

End left_module_props.

Lemma binary_morphism_op `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}
  (f:X ⇀ Y ⇀ Z) `{!Morphism (X ⇒ Y ⇒ Z) f} : Morphism (Y ⇒ X ⇒ Z) (λ y x, f x y).
Proof _ : Morphism (Y ⇒ X ⇒ Z) (curry ((uncurry f) ∘ (prod_swap : Y*X ⇀ X*Y))).

Section commutative_ring.
  Instance comring_right_rng_module `{LeftRngModule (R:=R) (M:=M)} `{!Commutative (.*.) R}
    : RightRngModule (BCbullet := (λ x r, r · x)) M R.
  Proof. split; try apply _; unfold bullet.
  + apply binary_morphism_op. apply _.
  + intros x ? r ? s ?. exact (lm_distr_r _ _ _).
  + intros x ? y ? r ?. exact (lm_distr_l _ _ _).
  + intros x ? r ? s ?. rewrite (_ $ commutativity (.*.) _ _).
    subsymmetry. exact (lm_assoc _ _ _).
  Qed.

  Instance comring_right_module `{LeftModule (R:=R) (M:=M)} `{!Commutative (.*.) R}
    : RightModule (BCbullet := (λ x r, r · x)) M R.
  Proof. split; try apply _; unfold bullet.
  + intros x ?. exact (lm_identity _).
  Qed.

  Instance comring_bi_module `{LeftModule (R:=R) (M:=M)} `{!Commutative (.*.) R}
    : BiModule (BCbullet := (λ x r, r · x)) R M R.
  Proof. split; try apply _; unfold bullet.
  + intros r ? x ? s ?. now rewrite 2!(_ $ lm_assoc _ _ _), (_ $ commutativity (.*.) r _).
  Qed.
End commutative_ring.

Section opposite_ring.

  Instance semirng_op `{SemiRng (R:=R)} : SemiRng (Amult := (λ r s, s * r)) R.
  Proof. split; [apply _ | unfold mult_is_sg_op | unfold mult at 1..].
         split; [apply _ | unfold sg_op..].
  + intros r ? s ? t ?. subsymmetry. exact (associativity (.*.) _ _ _).
  + apply binary_morphism_op. apply _.
  + intros r ? s ? t ?. exact (plus_mult_distr_r _ _ _).
  + intros r ? s ? t ?. exact (plus_mult_distr_l _ _ _).
  + intros r ?. exact (mult_0_r _).
  + intros r ?. exact (mult_0_l _).
  Qed.

  Instance semiring_op `{SemiRing (R:=R)} : SemiRing (Amult := (λ r s, s * r)) R.
  Proof. split; [apply _ | apply _ | unfold mult at 1..].
  + intros r ?. exact (mult_1_r _).
  + intros r ?. exact (mult_1_l _).
  Qed.

  Instance comsemiring_op `{CommutativeSemiRing (R:=R)} : CommutativeSemiRing (Amult := (λ r s, s * r)) R.
  Proof. apply comsemiring_from_semiring. unfold mult at 1.
  + intros r ? s ?. exact (commutativity (.*.) _ _).
  Qed.

  Instance rng_op `{Rng (R:=R)} : Rng (Amult := (λ r s, s * r)) R := {}.
  Instance ring_op `{Ring (R:=R)} : Ring (Amult := (λ r s, s * r)) R := {}.
  Instance comring_op `{CommutativeRing (R:=R)} : CommutativeRing (Amult := (λ r s, s * r)) R := {}.

  Instance left_rng_module_from_right `{RightRngModule (M:=M) (S:=R)}
    : LeftRngModule (Amult := (λ r s, s * r)) (ABdot := (λ r x, x ∙ r)) R M.
  Proof. split; unfold dot; try apply _.
  + apply binary_morphism_op. apply _.
  + intros r ? x ? y ?. exact (rm_distr_r _ _ _).
  + intros r ? s ? x ?. exact (rm_distr_l _ _ _).
  + intros r ? s ? x ?. subsymmetry. unfold mult at 1. exact (rm_assoc _ _ _).
  Qed.

  Instance left_module_from_right `{RightModule (M:=M) (S:=R)}
    : LeftModule (Amult := (λ r s, s * r)) (ABdot := (λ r x, x ∙ r)) R M.
  Proof. split; try apply _; unfold dot.
  + intros x ?. exact (rm_identity _).
  Qed.

End opposite_ring.

Section right_rng_module_props.
  Context `{RightRngModule (M:=M) (S:=R)}.

  Hint Extern 0 (Dot ?A ?B) => eexact (λ r x, x ∙ r) : typeclass_instances.
  Existing Instance left_rng_module_from_right.

  Lemma bullet_0_r x `{x ∊ M} : x ∙ 0 = 0 .
  Proof dot_0_l (Amult := (λ r s, s * r)) x.

  Lemma bullet_0_l r `{r ∊ R} : (@zero B _) ∙ r = 0.
  Proof dot_0_r (Amult := (λ r s, s * r)) r.

  Lemma negate_bullet_l x `{x ∊ M} r `{r ∊ R} : -(x ∙ r) = (-x) ∙ r .
  Proof negate_dot_r (Amult := (λ r s, s * r)) r x.

  Lemma negate_bullet_r x `{x ∊ M} r `{r ∊ R} : -(x ∙ r) = x ∙ (-r) .
  Proof negate_dot_l (Amult := (λ r s, s * r)) r x.

End right_rng_module_props.

Section right_module_props.
  Context `{RightModule (M:=M) (S:=R)}.

  Hint Extern 0 (Dot ?A ?B) => eexact (λ r x, x ∙ r) : typeclass_instances.
  Existing Instance left_module_from_right.

  Lemma negate_bullet x `{x ∊ M} : -x = x ∙ -1.
  Proof negate_dot (Amult := (λ r s, s * r)) x.

End right_module_props.



Section left_morphism_alt.
  Context `{M₁:set} `{M₂:set} (f:M₁ ⇀ M₂) .

  Context `{Module_Morphism (B1:=_) (B2:=_) (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=dummy)}.

  Lemma module_morphism_alt `{!LeftRngModule R M₁} `{!LeftRngModule R M₂}
  : Morphism (M₁ ⇒ M₂) f
  → (∀ `{x ∊ M₁} `{y ∊ M₁}, f (x + y) = f x + f y)
  → (∀ `{r ∊ R } `{x ∊ M₁}, f (r · x) = r · f x)
  → Module_Morphism R M₁ M₂ f.
  Proof. intros ? fplus fdot. split; try apply _; [ split; try apply _ |]; assumption. Qed.
End left_morphism_alt.

Section right_morphism_alt.
  Context `{M₁:set} `{M₂:set} (f:M₁ ⇀ M₂) .

  Context `{S:set} `{RightModule_Morphism (B1:=_) (B2:=_) (C:=_) (M₁:=M₁) (M₂:=M₂) (S:=S) (f:=dummy)}.

  Lemma right_module_morphism_alt `{!RightRngModule M₁ S} `{!RightRngModule M₂ S}
  : Morphism (M₁ ⇒ M₂) f
  → (∀ `{x ∊ M₁} `{y ∊ M₁}, f (x + y) = f x + f y)
  → (∀ `{x ∊ M₁} `{r ∊ S }, f (x ∙ r) = f x ∙ r)
  → RightModule_Morphism M₁ M₂ S f.
  Proof. intros ? fplus fbullet. split; try apply _; [ split; try apply _ |]; assumption. Qed.
End right_morphism_alt.

Section bi_morphism_alt.
  Context `{M₁:set} `{M₂:set} (f:M₁ ⇀ M₂) .

  Context `{S:set} `{BiModule_Morphism (B1:=_) (B2:=_) (C:=_) (R:=R) (M₁:=M₁) (M₂:=M₂) (S:=S) (f:=dummy)}.

  Lemma bimodule_morphism_alt `{One _} `{One _} `{!BiModule R M₁ S} `{!BiModule R M₂ S}
  : Morphism (M₁ ⇒ M₂) f
  → (∀ `{x ∊ M₁} `{y ∊ M₁}, f (x + y) = f x + f y)
  → (∀ `{r ∊ R } `{x ∊ M₁}, f (r · x) = r · f x)
  → (∀ `{x ∊ M₁} `{r ∊ S }, f (x ∙ r) = f x ∙ r)
  → BiModule_Morphism R M₁ M₂ S f.
  Proof. split. now apply (module_morphism_alt _). now apply (right_module_morphism_alt _). Qed.
End bi_morphism_alt.

Lemma module_morphism_proper: Find_Proper_Signature (@Module_Morphism) 0
  (∀ A Aplus Amult Azero Anegate Ae B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot R M1 M2,
   Proper ((@equiv (M1 ⇀ M2) _) ==> impl)
   (@Module_Morphism A Aplus Amult Azero Anegate Ae B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot R M1 M2)).
Proof. red; intros. intros f g E ?. pose proof modmor_a. pose proof modmor_b.
  assert (Morphism (M1 ⇒ M2) g) by (rewrite <-E; apply _).
  split; try apply _. rewrite <- E; apply _.
  intros r ? x ?. rewrite <-(E _ _ (_ : Proper (M1,=) (r · x))), <-(E _ _ (_ : Proper (M1,=) x)).
  exact (preserves_dot _ _). 
Qed.
Hint Extern 0 (Find_Proper_Signature (@Module_Morphism) 0 _) => eexact module_morphism_proper : typeclass_instances.

Lemma right_module_morphism_proper: Find_Proper_Signature (@RightModule_Morphism) 0
  (∀ C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate B1Cbullet B2Cbullet M1 M2 S,
   Proper ((@equiv (M1 ⇀ M2) _) ==> impl)
   (@RightModule_Morphism C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate B1Cbullet B2Cbullet M1 M2 S)).
Proof. red; intros. intros f g E ?. pose proof rmodmor_a. pose proof rmodmor_b.
  assert (Morphism (M1 ⇒ M2) g) by (rewrite <-E; apply _).
  split; try apply _. rewrite <- E; apply _.
  intros x ? r ?. rewrite <-(E _ _ (_ : Proper (M1,=) (x ∙ r))), <-(E _ _ (_ : Proper (M1,=) x)).
  exact (preserves_bullet _ _). 
Qed.
Hint Extern 0 (Find_Proper_Signature (@RightModule_Morphism) 0 _) => eexact right_module_morphism_proper : typeclass_instances.

Lemma bi_module_morphism_proper: Find_Proper_Signature (@BiModule_Morphism) 0
  (∀ A Aplus Amult Azero Anegate Ae C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot B1Cbullet B2Cbullet R M1 M2 S,
   Proper ((@equiv (M1 ⇀ M2) _) ==> impl)
   (@BiModule_Morphism A Aplus Amult Azero Anegate Ae C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot B1Cbullet B2Cbullet R M1 M2 S)).
Proof. red; intros. intros f g E ?. split; rewrite <-E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@BiModule_Morphism) 0 _) => eexact bi_module_morphism_proper : typeclass_instances.

Lemma module_morphism_proper2: Find_Proper_Signature (@Module_Morphism) 1
  (∀ A Aplus Amult Azero Anegate Ae B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot,
   Proper ((=)==>(=)==>(=)==>eq==> impl)
   (@Module_Morphism A Aplus Amult Azero Anegate Ae B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot)).
Proof. red; intros. intros R1 R2 ER M1 M1' E1 M2 M2' E2 f ? Ef ?. rewrite <-Ef.
  pose proof _ : Subset R2 R1.
  pose proof _ : Subset M1' M1.
  pose proof _ : Subset M2' M2.
  split. rewrite <-ER, <-E1. exact modmor_a. rewrite <-ER, <-E2. exact modmor_b.
  rewrite <-E1, <-E2. apply _.
  intros r ? x ?. exact (preserves_dot _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Module_Morphism) 1 _) => eexact module_morphism_proper2 : typeclass_instances.

Lemma right_module_morphism_proper2: Find_Proper_Signature (@RightModule_Morphism) 1
  (∀ C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate B1Cbullet B2Cbullet,
   Proper ((=)==>(=)==>(=)==>eq==>impl)
   (@RightModule_Morphism C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate B1Cbullet B2Cbullet)).
Proof. red; intros. intros M1 M1' E1 M2 M2' E2 S1 S2 ES  f ? Ef ?. rewrite <-Ef.
  pose proof _ : Subset S2 S1.
  pose proof _ : Subset M1' M1.
  pose proof _ : Subset M2' M2.
  split. rewrite <-ES, <-E1. exact rmodmor_a. rewrite <-ES, <-E2. exact rmodmor_b.
  rewrite <-E1, <-E2. apply _.
  intros x ? r ?. exact (preserves_bullet _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@RightModule_Morphism) 1 _) => eexact right_module_morphism_proper2 : typeclass_instances.

Lemma bi_module_morphism_proper2: Find_Proper_Signature (@BiModule_Morphism) 1
  (∀ A Aplus Amult Azero Anegate Ae C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot B1Cbullet B2Cbullet,
   Proper ((=)==>(=)==>(=)==>(=)==>eq==>impl)
   (@BiModule_Morphism A Aplus Amult Azero Anegate Ae C Cplus Cmult Czero Cnegate Ce B1 B2 B1e B2e B1plus B2plus B1zero B2zero B1negate B2negate AB1dot AB2dot B1Cbullet B2Cbullet)).
Proof. red; intros. intros R1 R2 ER M1 M1' E1 M2 M2' E2 S1 S2 ES  f ? Ef ?. rewrite <-Ef.
  split. rewrite <-ER,<-E1,<-E2. apply _. rewrite <-E1,<-E2,<-ES. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@BiModule_Morphism) 1 _) => eexact bi_module_morphism_proper2 : typeclass_instances.

Lemma id_module_mor `(S:set) M `{!Subset S M} `{LeftRngModule (B:=_) (R:=R) (M:=M)} `{!LeftRngModule R S} : Module_Morphism R S M id.
Proof. split; try apply _. now intros. Qed.
Hint Extern 4 (Module_Morphism _ _ _ id) => eapply @id_module_mor : typeclass_instances.

Lemma id_rmodule_mor `(S:set) M `{!Subset S M} `{RightRngModule (B:=_) (M:=M) (S:=R)} `{!RightRngModule S R} : RightModule_Morphism S M R id.
Proof. split; try apply _. now intros. Qed.
Hint Extern 4 (RightModule_Morphism _ _ _ id) => eapply @id_rmodule_mor : typeclass_instances.

Lemma id_bimodule_mor `(S:set) M `{!Subset S M} `{BiModule (B:=_) (R:=R) (M:=M) (S:=R')} `{!BiModule R S R'} : BiModule_Morphism R S M R' id.
Proof. split; try apply _. Qed.
Hint Extern 4 (BiModule_Morphism _ _ _ _ id) => eapply @id_bimodule_mor : typeclass_instances.

Section compose_mor1.
  Context `{M₁:@set B1} `{M₂:@set B2} `{M₃:@set B3} (f:M₁ ⇀ M₂) (g:M₂ ⇀ M₃).
  Context `{Module_Morphism (B1:=_) (B2:=_) (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=f)}.
  Context {B3e : Equiv B3} {B3plus: Plus B3} {B3zero: Zero B3} {B3negate: Negate B3} {AB3dot : Dot A B3}.
  Context `{!Module_Morphism R M₂ M₃ g}.

  Lemma compose_module_morphism : Module_Morphism R M₁ M₃ (g ∘ f).
  Proof.
    pose proof modmor_a : LeftRngModule R M₁ .
    pose proof modmor_a : LeftRngModule R M₂ .
    pose proof modmor_b : LeftRngModule R M₃ .
    split; try apply _.
    intros r ? x ?. unfold compose. now rewrite 2!(_ $ preserves_dot _ _).
  Qed.
End compose_mor1.
Hint Extern 4 (Module_Morphism _ _ _ (_ ∘ _)) => class_apply @compose_module_morphism : typeclass_instances.

Section compose_mor2.
  Context `{M₁:@set B1} `{M₂:@set B2} `{M₃:@set B3} (f:M₁ ⇀ M₂) (g:M₂ ⇀ M₃).
  Context `{RightModule_Morphism (B1:=_) (B2:=_) (M₁:=M₁) (M₂:=M₂) (S:=R) (f:=f)}.
  Context {B3e : Equiv B3} {B3plus: Plus B3} {B3zero: Zero B3} {B3negate: Negate B3} {B3Cbullet : Bullet B3 C}.
  Context `{!RightModule_Morphism M₂ M₃ R g}.

  Lemma compose_right_module_morphism : RightModule_Morphism M₁ M₃ R (g ∘ f).
  Proof.
    pose proof rmodmor_a : RightRngModule M₁ R.
    pose proof rmodmor_a : RightRngModule M₂ R.
    pose proof rmodmor_b : RightRngModule M₃ R.
    split; try apply _.
    intros x ? r ?. unfold compose. now rewrite 2!(_ $ preserves_bullet _ _).
  Qed.
End compose_mor2.
Hint Extern 4 (RightModule_Morphism _ _ _ (_ ∘ _)) => class_apply @compose_right_module_morphism : typeclass_instances.

Section compose_mor3.
  Context `{M₁:@set B1} `{M₂:@set B2} `{M₃:@set B3} (f:M₁ ⇀ M₂) (g:M₂ ⇀ M₃).
  Context `{BiModule_Morphism (B1:=_) (B2:=_) (R:=R) (M₁:=M₁) (M₂:=M₂) (S:=R') (f:=f)}.
  Context {B3e : Equiv B3} {B3plus: Plus B3} {B3zero: Zero B3} {B3negate: Negate B3} {AB3dot : Dot A B3} {B3Cbullet : Bullet B3 C}.
  Context `{!BiModule_Morphism R M₂ M₃ R' g}.

  Instance compose_bi_module_morphism : BiModule_Morphism R M₁ M₃ R' (g ∘ f) := {}.
End compose_mor3.
Hint Extern 4 (BiModule_Morphism _ _ _ (_ ∘ _)) => class_apply @compose_bi_module_morphism : typeclass_instances.

Section fun_ops.
  Context `{Module_Morphism (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=dummy)}.

  Global Instance fun_zero   : Zero   (M₁ ⇀ M₂) := λ _, 0.
  Global Instance fun_plus   : Plus   (M₁ ⇀ M₂) := λ f g x, f x + g x.
  Global Instance fun_negate : Negate (M₁ ⇀ M₂) := λ f x, - f x.
  Global Instance fun_dot    : Dot  _ (M₁ ⇀ M₂) := λ r f x, r · f x.
End fun_ops.

Hint Extern 2 (Equiv (elt_type (Module_Morphism _ ?M₁ ?M₂))) => exact (@equiv (M₁ ⇀ M₂) _) : typeclass_instances.

Section fun_rng_module.
  Context `{Module_Morphism (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=dummy)}.

  Context `{!LeftRngModule R M₁} `{!LeftRngModule R M₂}.
  Context `{!Commutative (.*.) R}.

  Notation L := (Module_Morphism R M₁ M₂ : @set (M₁ ⇀ M₂)).

  Instance :  Module_Morphism R M₁ M₂ (0:M₁ ⇀ M₂).
  Proof. unfold "0", fun_zero. split; try apply _. split; try apply _.
  + intros x ? y ?. subsymmetry. exact (plus_0_l _).
  + intros r ? x ?. subsymmetry. exact (dot_0_r _).
  Qed.

  Ltac red_mor_els :=
    repeat match goal with H : _ ∊ Module_Morphism R M₁ M₂ |- _ => red in H end.

  Instance: ∀ `{f ∊ L}, Module_Morphism R M₁ M₂ (-f).
  Proof. intros. unfold negate, fun_negate. red_mor_els. apply (module_morphism_alt _).
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros x ? y ?. rewrite (_ $ preserves_plus _ _). exact (negate_plus_distr _ _).
  + intros r ? x ?. rewrite (_ $ preserves_dot _ _). exact (negate_dot_r _ _).
  Qed.

  Instance: ∀ `{r ∊ R} `{f ∊ L}, Module_Morphism R M₁ M₂ (r · f).
  Proof. intros. unfold dot, fun_dot. red_mor_els. apply (module_morphism_alt _).
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros x ? y ?. rewrite (_ $ preserves_plus _ _). exact (lm_distr_l _ _ _).
  + intros s ? x ?. rewrite (_ $ preserves_dot _ _), 2!(_ $ lm_assoc _ _ _).
    now rewrite (_ $ commutativity _ r s).
  Qed.

  Instance: ∀ `{f ∊ L} `{g ∊ L}, Module_Morphism R M₁ M₂ (f + g).
  Proof. intros. unfold plus, fun_plus. red_mor_els. apply (module_morphism_alt _).
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros x ? y ?. change (f (x+y) + g (x+y) = f x + g x + (f y + g y)).
    rewrite 2!(_ $ preserves_plus _ _).
    rewrite <-(_ $ associativity (+) (f x) (f y) _).
    rewrite   (_ $ associativity (+) (f y) (g x) _).
    rewrite   (_ $ commutativity (+) (f y) (g x)).
    rewrite <-(_ $ associativity (+) (g x) (f y) _).
    now rewrite   (_ $ associativity (+) (f x) (g x) _).
  + intros r ? x ?. now rewrite 2!(_ $ preserves_dot _ _), (_ $ lm_distr_l _ _ _).
  Qed.

  Hint Extern 2 (_ ∊ L) => red : typeclass_instances.
  (*Hint Extern 2 (Equiv (elt_type L)) => exact (@equiv (M₁ ⇀ M₂) _) : typeclass_instances.*)

  Instance : L ⊆  M₁ ⇒ M₂ .
  Proof. apply subsetoid_alt. apply _.
      intros f g E P. red in P. red. unfold_sigs. now rewrite E in P. 
    intros ? P. red in P. apply _.
  Qed.

  Global Instance : Setoid L.
  Proof subsetoid_a.

  Instance : Morphism (L ⇒ L) (-).
  Proof. intros f g E. unfold_sigs. red_mor_els. red_sig.
    intros ? x Ex. unfold_sigs. red_sig. rewrite (_ $ Ex).
    change (- (f x) = - (g x)). now rewrite (E _ _ (_:Proper (M₁,=) x)).
  Qed.

  Instance : Morphism (R ⇒ L ⇒ L) (·).
  Proof. eapply @binary_morphism_proper_back. apply _. apply _.
    intros r s Er f g E.
    change (elt_type (M₁ ⇀ M₂)) in f.
    change (elt_type (M₁ ⇀ M₂)) in g.
    unfold_sigs. red_mor_els. red_sig.
    intros x y Ex. unfold_sigs. red_sig. rewrite (_ $ Ex).
    unfold dot, fun_dot.
    now rewrite (_ $ Er), (E _ _ (_:Proper (M₁,=) y)).
  Qed.

  Instance : Morphism (L ⇒ L ⇒ L) (+).
  Proof. eapply @binary_morphism_proper_back. apply _. apply _.
    intros f1 f2 Ef g1 g2 Eg.
    change (elt_type (M₁ ⇀ M₂)) in g1.
    change (elt_type (M₁ ⇀ M₂)) in g2.
    unfold_sigs. red_mor_els. red_sig.
    intros x y Ex. unfold_sigs. red_sig. rewrite (_ $ Ex).
    unfold plus, fun_plus.
    now rewrite (Ef _ _ (_:Proper (M₁,=) y)), (Eg _ _ (_:Proper (M₁,=) y)).
  Qed.

  Ltac helper := intros ? x E; unfold_sigs; red_mor_els; red_sig; rewrite (_ $ E).

  Instance : Associative (+) L.
  Proof. intros f ? g ? h ?; helper. exact (associativity (+) (f x) (g x) (h x)). Qed.

  Instance : Commutative (+) L.
  Proof. intros f ? g ?; helper. exact (commutativity (+) (f x) (g x)). Qed.

  Instance : LeftIdentity (+) 0 L.
  Proof. intros f ?; helper. exact (plus_0_l (f x)). Qed.

  Instance : LeftInverse (+) (-) 0 L.
  Proof. intros f ?; helper. exact (plus_negate_l (f x)). Qed.

  Instance : AdditiveGroup L.
  Proof. repeat (split; try apply _). Qed.

  Global Instance module_morphisms_rng_module : LeftRngModule R L.
  Proof. split; try apply _.
  + intros r ? f ? g ?. helper. exact (lm_distr_l r (f x) (g x)).
  + intros r ? s ? f ?. helper. exact (lm_distr_r r s (f x)).
  + intros r ? s ? f ?. helper. exact (lm_assoc r s (f x)).
  Qed.
End fun_rng_module.

Section fun_module.
  Context `{Module_Morphism (R:=R) (M₁:=M₁) (M₂:=M₂) (f:=dummy)}.

  Context `{Aone: One _} `{!LeftModule R M₁} `{!LeftModule R M₂}.
  Context `{!Commutative (.*.) R}.

  Notation L := (Module_Morphism R M₁ M₂ : @set (M₁ ⇀ M₂)).

  Hint Extern 2 (Module_Morphism R M₁ M₂ ?f) => change (f ∊ L) : typeclass_instances.
  Instance: ∀ `{f ∊ L}, Morphism (M₁ ⇒ M₂) f.
  Proof. intros f el. red in el. apply _. Qed.

  Global Instance module_morphisms_module : LeftModule R L.
  Proof. split. apply _. apply _.
    intros f fel ? x E. unfold_sigs. red_sig. rewrite (_ $ E).
    exact (lm_identity (f x)).
  Qed. 
End fun_module.
