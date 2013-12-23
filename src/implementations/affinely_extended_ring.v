Require Import
  abstract_algebra interfaces.orders interfaces.affine_extension
  theory.strong_setoids theory.rings theory.fields orders.fields.

Inductive AffineExtendT (A : Type) := 
  | Inject : A → AffineExtendT A
  | PosInfty : AffineExtendT A
  | NegInfty : AffineExtendT A
  | Undefined : AffineExtendT A.

Arguments Inject {A} _.
Arguments PosInfty {A}.
Arguments NegInfty {A}.
Arguments Undefined {A}.

Instance AE_infty {A} : Infty (AffineExtendT A) := PosInfty.

Definition AffineExtendImage `(R:set) : set := λ x,
  match x with | Inject y => y ∊ R | _ => False end.

Definition AffineExtendFull `(R:set) : set :=  λ x,
  match x with | Inject y => y ∊ R | _ => True end.

Hint Extern 10 (@set (AffineExtendT _)) => eapply @AffineExtendFull : typeclass_instances.

Definition AffineExtend `(R:set) : set :=  λ x,
  match x with
  | Inject y => y ∊ R
  | PosInfty => True
  | NegInfty => True
  | Undefined => False
  end.

Hint Extern 2 (Inject _ ∊ AffineExtendFull ?R) => do 2 red; apply _ : typeclass_instances.
Hint Extern 2 (Inject _ ∊ AffineExtend ?R) => do 2 red; apply _ : typeclass_instances.
Hint Extern 2 (Inject _ ∊ AffineExtendImage ?R) => do 2 red; apply _ : typeclass_instances.
Hint Extern 2 (NegInfty ∊ AffineExtendFull ?R) => exact I : typeclass_instances.
Hint Extern 2 (PosInfty ∊ AffineExtendFull ?R) => exact I : typeclass_instances.
Hint Extern 2 (Undefined ∊ AffineExtendFull ?R) => exact I : typeclass_instances.
Hint Extern 2 (infty ∊ AffineExtendFull ?R) => exact I : typeclass_instances.
Hint Extern 2 (NegInfty ∊ AffineExtend ?R) => exact I : typeclass_instances.
Hint Extern 2 (PosInfty ∊ AffineExtend ?R) => exact I : typeclass_instances.
Hint Extern 2 (infty ∊ AffineExtend ?R) => exact I : typeclass_instances.

Instance AE_cast `{R:set} : Cast R (AffineExtendImage R) := Inject.

Lemma AE_full_subset `(R:set) : Subset (AffineExtend R) (AffineExtendFull R).
Proof. unfold AffineExtend, AffineExtendFull. intros [y| | |] H; red in H; red; tauto. Qed.
Hint Extern 2 (Subset (AffineExtend ?R) (AffineExtendFull ?R)) => eapply @AE_full_subset : typeclass_instances.

Lemma AE_image_subset `(R:set) : Subset (AffineExtendImage R) (AffineExtend R).
Proof. unfold AffineExtend, AffineExtendImage. intros [y| | |] H; red in H; red; tauto. Qed.
Hint Extern 2 (Subset (AffineExtendImage ?R) (AffineExtend ?R)) => eapply @AE_image_subset : typeclass_instances.

Lemma AE_image_subset2 `(R:set) : Subset (AffineExtendImage R) (AffineExtendFull R).
Proof. transitivity (AffineExtend R); apply _. Qed.
Hint Extern 2 (Subset (AffineExtendImage ?R) (AffineExtendFull ?R)) => eapply @AE_image_subset2 : typeclass_instances.

Lemma AE_image_back `{R:set} x `{el:x ∊ AffineExtendImage R} : ∃ `{a ∊ R}, x ≡ Inject a.
Proof. destruct x as [a| | |]; [ exists a; now exists el | ..]; now do 2 red in el. Qed.

Section ops.
  Context `{Ring A (R:=R)}.

  Local Notation A' := (AffineExtendT A).

  Definition AE_equiv : Equiv A' := λ x y,
    match x with
    | Inject x  => match y with | Inject y => x=y | _ => False end
    | PosInfty  => match y with | PosInfty => True | _ => False end
    | NegInfty  => match y with | NegInfty => True | _ => False end
    | Undefined => match y with | Undefined => True | _ => False end
    end.

  Definition AE_uneq `{UnEq A} : UnEq A' := λ x y,
    match x with
    | Inject x => match y with | Inject y => x≠y | _ => True end
    | PosInfty => match y with | PosInfty => False | _ => True end
    | NegInfty => match y with | NegInfty => False | _ => True end
    | Undefined => match y with | Undefined => False | _ => True end
    end.

  Definition AE_le `{Le A} : Le A' := λ x y,
    match x with
    | Inject x => match y with | Inject y => x ≤ y | PosInfty => True | _ => False end
    | PosInfty => match y with | PosInfty => True | _ => False end
    | NegInfty => match y with | Undefined => False | _ => True end
    | Undefined => match y with | Undefined => True | _ => False end
    end.

  Definition AE_lt `{Lt A} : Lt A' := λ x y,
    match x with
    | Inject x => match y with | Inject y => x < y | PosInfty => True | _ => False end
    | PosInfty => False
    | NegInfty => match y with | NegInfty => False | Undefined => False | _ => True end
    | _ => False
    end.

  Instance AE_zero : Zero A' := Inject 0.
  Instance AE_one  : One  A' := Inject 1.

  Definition AE_plus : Plus A' := λ x y,
    match x with
    | Inject x => match y with | Inject y => Inject (x+y) | _ => y end
    | PosInfty => match y with | (NegInfty | Undefined) => Undefined |_ => PosInfty end
    | NegInfty => match y with | (PosInfty | Undefined) => Undefined |_ => NegInfty end
    | _ => Undefined
    end.

  Instance AE_negate : Negate A' := λ x,
    match x with
    | Inject x => Inject (-x)
    | PosInfty => NegInfty
    | NegInfty => PosInfty
    | _ => Undefined
    end.

  Definition AE_mult `{Lt A} `{!StrongSubDecision R R (<)} : Mult A' := λ x y,
    match x with
    | Inject x => match y with
      | Inject y => Inject (x*y)
      | _ => if decide_sub_strong (<) 0 x then y
             else if decide_sub_strong (<) x 0 then -y else Undefined
      end
    | (PosInfty|NegInfty) => match y with
      | Inject y => if decide_sub_strong (<) 0 y then x
               else if decide_sub_strong (<) y 0 then -x else Undefined
      | PosInfty => x
      | NegInfty => -x
      | _ => Undefined
      end
    | _ => Undefined
    end.

  Definition AE_inv `{Inv A} `{!StrongSubDecision R R (=)} : Inv A' := λ x,
    match x with
    | Inject x => if decide_sub_strong (=) x 0 then Undefined else Inject (inv x)
    | (PosInfty|NegInfty) => 0
    | _ => Undefined
    end.
End ops.

Hint Extern 0 (Equiv   (AffineExtendT _)) => eapply @AE_equiv  : typeclass_instances.
Hint Extern 0 (Equiv   (elt_type (AffineExtendFull _))) => eapply @AE_equiv  : typeclass_instances.
Hint Extern 0 (Equiv   (elt_type (AffineExtend _))) => eapply @AE_equiv  : typeclass_instances.
Hint Extern 0 (Equiv   (elt_type (AffineExtendImage _))) => eapply @AE_equiv  : typeclass_instances.
Hint Extern 0 (UnEq    (AffineExtendT _)) => eapply @AE_uneq  : typeclass_instances.
Hint Extern 0 (UnEq    (elt_type (AffineExtendFull _))) => eapply @AE_uneq  : typeclass_instances.
Hint Extern 0 (UnEq    (elt_type (AffineExtend _))) => eapply @AE_uneq  : typeclass_instances.
Hint Extern 0 (UnEq    (elt_type (AffineExtendImage _))) => eapply @AE_uneq  : typeclass_instances.
Hint Extern 0 (Le      (AffineExtendT _)) => eapply @AE_le     : typeclass_instances.
Hint Extern 0 (Lt      (AffineExtendT _)) => eapply @AE_lt     : typeclass_instances.
Hint Extern 0 (Zero    (AffineExtendT _)) => eapply @AE_zero   : typeclass_instances.
Hint Extern 0 (One     (AffineExtendT _)) => eapply @AE_one    : typeclass_instances.
Hint Extern 0 (Plus    (AffineExtendT _)) => eapply @AE_plus   : typeclass_instances.
Hint Extern 0 (Mult    (AffineExtendT _)) => eapply @AE_mult   : typeclass_instances.
Hint Extern 0 (Negate  (AffineExtendT _)) => eapply @AE_negate : typeclass_instances.
Hint Extern 0 (Inv     (AffineExtendT _)) => eapply @AE_inv    : typeclass_instances.

Hint Extern 2 (PosInfty ∊ (AffineExtend ?R)⁺) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (PosInfty ∊ (AffineExtend ?R)₊) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (NegInfty ∊ (AffineExtend ?R)⁻) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (NegInfty ∊ (AffineExtend ?R)₋) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (-infty ∊ AffineExtendFull ?R) => exact I : typeclass_instances.
Hint Extern 2 (-infty ∊ AffineExtend ?R) => exact I : typeclass_instances.
Hint Extern 2 (infty ∊ (AffineExtend ?R)⁺) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (infty ∊ (AffineExtend ?R)₊) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (-infty ∊ (AffineExtend ?R)⁻) => exact (conj I I) : typeclass_instances.
Hint Extern 2 (-infty ∊ (AffineExtend ?R)₋) => exact (conj I I) : typeclass_instances.

Hint Extern 2 (AffExtFull (AffineExtendImage ?R)) => exact (AffineExtendFull R) : typeclass_instances.
Hint Extern 2 (AffExt     (AffineExtendImage ?R)) => exact (AffineExtend     R) : typeclass_instances.

Section contents.
  Context `{R:@set A}.

  Local Notation A' := (AffineExtendT A).
  Local Notation R' := (AffineExtendImage R).
  Local Notation "R∞" := (AffineExtend R).
  Local Notation T := (AffineExtendFull R).

  Local Ltac destr_R' x a :=
    let Ex := fresh "Ex" in
    destruct (AE_image_back x) as [a [? Ex]]; rewrite Ex; clear dependent x.

  Local Ltac intro_R' x := let a := fresh "a" in intros a ?; destr_R' a x.

  Section setoid.
    Context `{Equiv A} `{!Setoid R}.

    (*
    Instance: ∀ `{Inject a ∊ R∞}, a ∊ R | 10.
    Proof. intros ? el. now do 2 red in el. Qed.

    Instance: ∀ `{Inject a ∊ R'}, a ∊ R | 10.
    Proof. intros ? el. now do 2 red in el. Qed.
    *)

    Instance AEF_setoid : Setoid T.
    Proof. split; unfold equiv, AE_equiv.
    + intros x el; do 2 red in el; now destruct x.
    + intros x el1 y el2; do 2 red in el1,el2. destruct x,y; try tauto. intro. subsymmetry.
    + intros x el1 y el2 z el3; do 2 red in el1,el2,el3.
      destruct x,y as [y' | | |],z; try tauto. intros ??. subtransitivity y'.
    Qed.

    Instance AEF_subsetoid : SubSetoid R∞ T.
    Proof. apply subsetoid_alt; try apply _. intros x y E el. unfold_sigs.
      destruct x,y; try tauto; try apply _.
    Qed.

    Instance AE_setoid : Setoid R∞ := subsetoid_a (T:=T).

    Instance AE_subsetoid : SubSetoid R' R∞.
    Proof. apply subsetoid_alt; try apply _. intros x y E el. unfold_sigs.
      generalize E. destr_R' x a. destruct y; now do 2 red.
    Qed.

    Instance AEI_setoid : Setoid R' := subsetoid_a (T:=R∞).

    Instance AE_inj_mor : Morphism (R ⇒ R') (cast R R').
    Proof. intros ?? E. unfold_sigs. unfold cast, AE_cast. split.
      split; now do 2 red. tauto.
    Qed.

    Instance AE_inj_inj : Injective R R' (cast R R').
    Proof. split; try apply _. tauto. Qed.

    Context `{UnEq A} `{!StrongSetoid R}.

    Instance AEF_strongsetoid : StrongSetoid T.
    Proof. split. split; unfold uneq, AE_uneq.
    + intros x el; do 2 red in el. destruct x; try tauto. exact (irreflexivity _ _).
    + intros x e1 y e2. do 2 red in e1,e2. destruct x, y; try tauto. intro. subsymmetry.
    + intros x e1 y e2. do 2 red in e1,e2. destruct x, y;
      intros E z el; do 2 red in el; destruct z; try tauto.
      apply (cotransitivity E _).
    + intros x e1 y e2. do 2 red in e1,e2. unfold uneq, AE_uneq, equiv, AE_equiv.
      destruct x,y; try tauto. exact (tight_apart _ _).
    Qed.

    Instance AE_strongsetoid : StrongSetoid R∞.
    Proof. rewrite (_:Subset R∞ T). apply _. Qed.

    Instance AEI_strongsetoid : StrongSetoid R'.
    Proof. rewrite (_:Subset R' R∞). apply _. Qed.

    Instance AE_inj_smor : Strong_Morphism R R' (cast R R').
    Proof. split. apply _. intros ???? E. exact E. Qed.

    Instance AE_inj_sinj : StrongInjective R R' (cast R R').
    Proof. split. intros ???? E. exact E. apply _. Qed.

    Instance AE_denial_inequality `{!DenialInequality R} : DenialInequality R'.
    Proof.
      intros [x| | |] e1 [y| | |] e2; do 2 red in e1,e2; try tauto.
      exact (denial_inequality x y).
    Qed.

    Program Instance AE_eq_str_sub_dec `{Le A} `{!StrongSubDecision R R (=)} : StrongSubDecision T T (=)
      := λ x y,
      match x with
      | Inject a => match y with
                    | Inject b => if decide_sub_strong (=) a b then in_left else in_right
                    | _ => in_right
                    end
      | PosInfty => match y with | PosInfty => in_left | _ => in_right end
      | NegInfty => match y with | NegInfty => in_left | _ => in_right end
      | Undefined => match y with | Undefined => in_left | _ => in_right end
      end.
    Next Obligation. unfold equiv, AE_equiv. destruct y as [b| | |]; try tauto.
      match goal with H : ∀ x, Inject x ≢ Inject b |- _ => pose proof (H b) as E end.
      now contradict E.
    Qed.
    Next Obligation. unfold equiv, AE_equiv. destruct y as [b| | |]; try tauto. Qed.
    Next Obligation. unfold equiv, AE_equiv. destruct y as [b| | |]; try tauto. Qed.
    Next Obligation. unfold equiv, AE_equiv. destruct y as [b| | |]; try tauto. Qed.

    Program Instance AE_le_str_sub_dec `{Le A} `{!StrongSubDecision R R (≤)} : StrongSubDecision T T (≤)
      := λ x y,
      match x with
      | Inject a => match y with
                    | Inject b => if decide_sub_strong (≤) a b then in_left else in_right
                    | PosInfty => in_left | _ => in_right
                    end
      | PosInfty => match y with | PosInfty => in_left | _ => in_right end
      | NegInfty => match y with | Undefined => in_right | _ => in_left end
      | Undefined => match y with | Undefined => in_left | _ => in_right end
      end.
    Next Obligation. unfold le, AE_le. destruct y as [b| | |]; try tauto.
      match goal with H : ∀ x, Inject x ≢ Inject b |- _ => pose proof (H b) as E end.
      now contradict E.
    Qed.
    Next Obligation. intuition; discriminate. Qed.
    Next Obligation. intuition; discriminate. Qed.
    Next Obligation. unfold le, AE_le. destruct y as [b| | |]; try tauto. Qed.
    Next Obligation. unfold le, AE_le. destruct y as [b| | |]; try tauto. Qed.
    Next Obligation. unfold le, AE_le. destruct y as [b| | |]; try tauto. Qed.

    Instance: ∀ `{x ∊ R'}, x ∊ T.    Proof. apply AE_image_subset2. Qed.

    Program Instance AE_im_str_sub_dec `{!StrongSubDecision T T rel} : StrongSubDecision R' R' rel
      := λ x y, if (decide_sub_strong rel x y) then in_left else in_right.
    Next Obligation. match goal with H : _ -> _ -> rel _ _ |- _ => exact (H _ _) end. Qed.
    Next Obligation. match goal with H : _ -> _ -> ¬ rel _ _ |- _ => exact (H _ _) end. Qed.

  End setoid.

  Existing Instance AEF_setoid.
  Existing Instance AEF_subsetoid.
  Existing Instance AE_setoid.
  Existing Instance AE_subsetoid.
  Existing Instance AEI_setoid.
  Existing Instance AE_inj_mor.
  Existing Instance AE_inj_inj.
  Existing Instance AEF_strongsetoid.
  Existing Instance AE_strongsetoid.
  Existing Instance AEI_strongsetoid.
  Existing Instance AE_inj_smor.
  Existing Instance AE_inj_sinj.
  Existing Instance AE_denial_inequality.

  Section ring.
    Context `{CommutativeRing A (R:=R)}.

    Instance AE_cast_inv: Inverse (cast R R') := λ x,
      match x with Inject a => a | _ => 0 end.

    Instance AE_cast_inv_mor: Morphism (R' ⇒ R) (inverse (cast R R')).
    Proof. intros x y E. unfold_sigs. generalize E. destr_R' x a. destr_R' y b.
      unfold inverse, AE_cast_inv. intro E.
      unfold equiv, AE_equiv in E; try tauto; now red_sig.
    Qed.

    Instance AE_cast_bij: Bijective R R' (cast R R').
    Proof. split. apply _. split; try apply _.
      intros x y E. unfold_sigs. generalize E. destr_R' x a. destr_R' y b.
      intro E. unfold compose, inverse, AE_cast_inv, cast, AE_cast, id.
      now red_sig.
    Qed.

    Instance AE_plus_ass : Associative (+) R∞.
    Proof. intros [?| | |] el [?| | |] el2 [?| | |] el3;
      unfold plus, AE_plus, equiv, AE_equiv; try tauto.
      do 2 red in el, el2, el3. exact (associativity _ _ _ _).
    Qed.

    Instance AE_plus_comm : Commutative (+) T.
    Proof. intros [?| | |] el [?| | |] el2;
      unfold plus, AE_plus, equiv, AE_equiv; try tauto.
      do 2 red in el, el2. exact (commutativity _ _ _).
    Qed.

    Instance: Closed (R' ⇀ R' ⇀ R') (+).
    Proof. intro_R' x. intro_R' y. unfold plus, AE_plus. apply _. Qed.

    Instance: 0 ∊ R'. Proof. unfold zero, AE_zero. apply _. Qed.
    Instance: 1 ∊ R'. Proof. unfold one, AE_one. apply _. Qed.

    Instance: Closed (R' ⇀ R') (-).
    Proof. intro_R' x. unfold negate, AE_negate. apply _. Qed.

    Context `{Lt A} `{!StrongSubDecision R R (<)}.

    Instance: Closed (R' ⇀ R' ⇀ R') (.*.).
    Proof. intro_R' x. intro_R' y. unfold mult, AE_mult. apply _. Qed.

    Instance AE_ring: CommutativeRing R'.
    Proof. apply (projected_com_ring (inverse (cast R R'))); unfold inverse, AE_cast_inv.
    + intro_R' x. intro_R' y. now unfold plus at 1, AE_plus.
    + intro_R' x. intro_R' y. now unfold mult at 1, AE_mult.
    + now unfold zero at 1, AE_zero.
    + now unfold one at 1, AE_one.
    + intro_R' x. now unfold negate at 1, AE_negate.
    Qed.

    Hint Extern 5 (@set A') => eexact R' : typeclass_instances.

    Instance AE_cast_ring_mor: SemiRing_Morphism R R' (cast R R').
    Proof. apply (ring_morphism_alt (cast R R')); try apply _;
      unfold cast, AE_cast; intros.
      now unfold plus at 2, AE_plus.
      now unfold mult at 2, AE_mult.
      now unfold one at 2, AE_one.
    Qed.

    (*
    Instance AE_negate_mor: Morphism (R∞ ⇒ R∞) (-).
    Proof. intros [?| | |] [?| | |] [[el1 el2] E]; do 2 red in el1,el2,E;
      unfold negate, AE_negate; try tauto; red_sig; try tauto.
      unfold equiv, AE_equiv. now rewrite (R$ E).
    Qed.
    *)

    Context `{Le A} `{UnEq A} `{!FullPseudoSemiRingOrder R}.

    Existing Instance pseudo_order_setoid.

    Instance AE_cast_inv_smor: Strong_Morphism R' R (inverse (cast R R')).
    Proof. split. apply _. intro_R' x. intro_R' y. tauto. Qed.

    Instance AE_cast_inv_sinj: StrongInjective R' R (inverse (cast R R')).
    Proof. split; [| apply _]. intro_R' x. intro_R' y. tauto. Qed.

    Instance AEI_order : FullPseudoSemiRingOrder R'.
    Proof. apply projected_full_pseudo_ring_order with (inverse (cast R R')); try apply _;
      intro_R' x; intro_R' y; tauto.
    Qed.

    Instance AE_order : FullPseudoOrder R∞.
    Proof. split. split. apply _.
      Local Ltac do_intros := intros [a| | |] el1 [b| | |] el2; do 2 red in el1,el2;
        unfold lt, AE_lt; try tauto.
    + do_intros. exact (pseudo_order_antisym _ _).
    + do_intros; intros E [c| | |] el3; do 2 red in el3;
      try tauto. exact (cotransitivity E _).
    + do_intros. unfold uneq, AE_uneq. exact (apart_iff_total_lt _ _).
    + do_intros. unfold le, AE_le. exact (le_iff_not_lt_flip _ _).
    Qed.

    Instance AEF_order : FullPartialOrder T.
    Proof. split. apply _. split. apply _.
    + intros [a| | |] [b| | |] [[el1 el2] E1]; do 2 red in el1,el2; do 2 red in E1; try tauto;
      intros [c| | |] [d| | |] [[el3 el4] E2]; do 2 red in el3,el4; do 2 red in E2; try tauto;
      intro E; try tauto. do 2 red in E. do 2 red. now rewrite <-(R $ E1), <-(R $ E2).
    + intros [a| | |] el1; do 2 red in el1; try tauto. now do 2 red.
    + intros [a| | |] el1 [b| | |] el2 [c| | |] el3; do 2 red in el1,el2,el3; try tauto;
      intros E1 E2; do 2 red in E1,E2; try tauto. do 2 red. subtransitivity b.
    + intros [a| | |] el1 [b| | |] el2; do 2 red in el1,el2; try tauto.
      intros E1 E2; do 2 red in E1,E2. do 2 red. now apply (antisymmetry le).
    + intros [a| | |] el1 [b| | |] el2 [c| | |] el3; do 2 red in el1,el2,el3; try tauto;
      intros E1 E2; do 2 red in E1,E2; try tauto. do 2 red. subtransitivity b.
    + intros [a| | |] el1 [b| | |] el2; do 2 red in el1,el2; try tauto.
      exact (lt_iff_le_apart a b).
    Qed.

    Instance: Undefined ∊ ae_undef R'.  Proof. lazy. tauto. Qed.
    Lemma AE_undef x `{el : x ∊ ae_undef R'} : x ≡ Undefined.
    Proof. lazy in el. destruct x; tauto. Qed.

    Instance: Morphism (T ⇒ T) (-).
    Proof.
      intros [?| | |] [?| | |] [[e1 e2] E1]; do 2 red in e1,e2,E1; try tauto;
      [| lazy;tauto..]. unfold "-", AE_negate. red_sig. do 2 red. now rewrite (R $ E1).
    Qed.

    Instance: Morphism (T ⇒ T ⇒ T) (+).
    Proof. apply binary_morphism_proper_back.
      intros [?| | |] [?| | |] [[e1 e2] E1]; do 2 red in e1,e2,E1; try tauto;
      intros [?| | |] [?| | |] [[e3 e4] E2]; do 2 red in e3,e4,E2; try tauto;
      [| lazy;tauto..]. unfold "+", AE_plus. red_sig. do 2 red. now rewrite (R $ E1), (R $ E2).
    Qed.

    Instance: Closed (T ⇀ T ⇀ T) (.*.).
    Proof. intros [?| | |] e1; unfold mult, AE_mult; [|..| intros ??; exact I];
      intros [?| | |] e2; try exact I; do 2 red in e1,e2; [do 2 red; apply _ |..];
      repeat match goal with
      |- context [ decide_sub_strong lt ?a ?b ] => destruct (decide_sub_strong lt a b)
      end; exact I.
    Qed.

    Instance: Commutative (.*.) T.
    Proof. intros [?| | |] el [?| | |] el2; do 2 red in el,el2;
      unfold mult, AE_mult, equiv, AE_equiv, negate, AE_negate; try tauto;
      [exact (commutativity _ _ _) |..];
      repeat match goal with
      |- context [ decide_sub_strong lt ?a ?b ] => destruct (decide_sub_strong lt a b)
      end; exact I.
    Qed.

    Instance: Strong_Binary_Morphism T T T (.*.).
    Proof. apply (strong_binary_morphism_commutative (.*.)). apply _.
      intros [?| | |] el; do 2 red in el; (split; [
    apply (_ : Closed (T ⇀ T ⇀ T) (.*.)); exact el |]);
    intros [?| | |] el2; do 2 red in el2;
    unfold mult, AE_mult, uneq, AE_uneq, negate, AE_negate; try tauto;
    intros [?| | |] el3; do 2 red in el3; try tauto;
    [exact (strong_extensionality ( _ *.)) |..];
    repeat match goal with
    |- context [ decide_sub_strong lt ?a ?b ] =>
       destruct (decide_sub_strong lt a b) as [P|P];
       pose proof (P _ _); clear P
    end; try tauto; intros _;
    try match goal with | H : 0 < ?x |- ?x ≠ _ => subsymmetry end;
    try match goal with | H : ?x < 0 |- _ ≠ ?x => subsymmetry end;
    apply (lt_apart _ _);
    try match goal with | _ : ?x < 0, _ : 0 < ?y |- ?x < ?y => subtransitivity 0 end;
    try match goal with | _ : 0 < ?x |- _ < ?x => apply (le_lt_trans _ 0 _); [ apply (not_lt_le_flip _ _) |] end; trivial;
    try match goal with | _ : ?x < 0 |- ?x < _ => apply (lt_le_trans _ 0 _); [| apply (not_lt_le_flip _ _) ] end; trivial.
    Qed.

    Ltac mult_tac := 
        unfold zero, AE_zero; unfold mult, AE_mult, infty, AE_infty, equiv, AE_equiv, negate, AE_negate;
        repeat match goal with
        |- context [ decide_sub_strong lt ?a ?b ] =>
             destruct (decide_sub_strong lt a b) as [P|P];
             pose proof (P _ _); clear P
        end.

    Instance AE_ae_ring : AffinelyExtendedRing R'.
    Proof. split; unfold aff_ext, aff_ext_full;
      try solve [ apply _ | tauto | exact I
    | intros [?| | |]; lazy; tauto 
    | intros [x| | |]; try (lazy; tauto); intros [el E]; do 2 red in el;
        unfold "0",AE_zero in E; do 3 red in E;
        mult_tac; solve [ tauto | destruct (lt_antisym x 0); now split ]
    | mult_tac; solve [ apply _ | now destruct (irreflexivity (<) 0) ]
    ].
    + apply SubSetoid_trans with R∞; apply _.
    + intros [?| | |]; lazy; try tauto. intros _ [?| | |]; tauto.
    + intros [?| | |]; lazy; try tauto. intros _ [?| | |]; tauto.
    + intros [?| | |] ? [?| | |] ? ?; try tauto; now split.
    + intros y ? x ?. rewrite (AE_undef x). destruct y; exact (_ : Undefined ∊ ae_undef R').
    + intros y ? x ?. rewrite (AE_undef x). pose proof (I : Undefined ∊ T).
      destruct y; try exact (_ : Undefined ∊ ae_undef R').
      unfold mult, AE_mult. destruct (decide_sub_strong (<) 0 a). apply _.
      destruct (decide_sub_strong (<) a 0); apply _.
    Qed.

    Context `{Inv A} `{!Field R}.
    Context `{!DenialInequality R} `{!StrongSubDecision R R (=)}.

    Instance: 0 ∊ T := _ : 0 ∊ R.

    Instance: Morphism (T ⇒ T) (inv).
    Proof.
      intros [x| | |] [y| | |] [[e1 e2] E1]; do 2 red in e1,e2,E1; try tauto;
      unfold inv, AE_inv;
      [| now red_sig..].
      destruct (decide_sub_strong (=) x 0) as [P|P]; pose proof (P _ _) as Ex; clear P;
      destruct (decide_sub_strong (=) y 0) as [P|P]; pose proof (P _ _) as Ey; clear P.
      now red_sig.
      contradict Ey. subtransitivity x. subsymmetry.
      contradict Ex. subtransitivity y.
      assert (x ∊ R ₀). split. apply _. red. now rewrite (denial_inequality x 0).
      assert (y ∊ R ₀). split. apply _. red. now rewrite (denial_inequality y 0).
      split. split; red; red; apply _. do 2 red. now rewrite (R ₀ $ E1).
    Qed.

    Instance: Morphism (R' ₀ ⇒ R' ₀) (inv).
    Proof.
      intros [x| | |] [y| | |] [[[e1 ez1] [e2 ez2]] E1]; do 2 red in e1,e2,E1; try tauto;
      unfold inv, AE_inv;
      [| now red_sig..].
      unfold "0", AE_zero in ez1,ez2. do 3 red in ez1,ez2.
      pose proof (uneq_ne x 0 ez1); pose proof (uneq_ne _ _ ez2).
      destruct (decide_sub_strong (=) x 0) as [P|P]; pose proof (P _ _) as Ex; clear P;
      destruct (decide_sub_strong (=) y 0) as [P|P]; pose proof (P _ _) as Ey; clear P;
      try contradiction.
      assert (x ∊ R ₀) by now split.
      assert (y ∊ R ₀) by now split.
      destruct (_ : inv x ∊ R ₀).
      destruct (_ : inv y ∊ R ₀).
      split. now split; split. do 2 red. now rewrite (R ₀ $ E1).
    Qed.

    Instance: SubDecision R' R' (=).
    Proof.
      intros [x| | |] e1 [y| | |] e2; do 2 red in e1,e2; try tauto.
      exact (decide_sub (=) x y).
    Qed.

    Instance: Subset (R' ₀) T. Proof. transitivity R'; apply _. Qed.

    Instance: Field R'.
    Proof. apply dec_field. apply _.
    + split. apply _. unfold "0", AE_zero, "1", AE_one. now destruct field_nontrivial.
    + intros [x| | |] [e1 ez1]; do 2 red in e1; try tauto.
      unfold "0", AE_zero in ez1. do 3 red in ez1.
      pose proof (uneq_ne x 0 ez1).
      assert (x ∊ R ₀) by now split.
      unfold inv, AE_inv.
      destruct (decide_sub_strong (=) x 0) as [P|P]; pose proof (P _ _) as Ex; clear P; try contradiction.
      unfold mult, AE_mult.
      exact (field_inv_l x).
    Qed.

    Instance AE_ae_field : AffinelyExtendedField R'.
    Proof. split; try first [ apply _ | now change (0=0) ].
    + unfold "0", AE_zero, inv, AE_inv.
      destruct (decide_sub_strong (=) 0 0) as [P|P]; pose proof (P _ _) as Ex; clear P. apply _.
      now contradict Ex.
    + intros x ?. rewrite (AE_undef x). exact (_ : Undefined ∊ ae_undef R').
    Qed.

  End ring.
  
End contents.

Hint Extern 2 (AffinelyExtendedRing  (AffineExtendImage _)) => eapply @AE_ae_ring  : typeclass_instances.
Hint Extern 2 (AffinelyExtendedField (AffineExtendImage _)) => eapply @AE_ae_field : typeclass_instances.
Hint Extern 2 (DenialInequality (AffineExtendImage _)) => eapply @AE_denial_inequality  : typeclass_instances.
Hint Extern 2 (StrongSubDecision (AffineExtendFull _) (AffineExtendFull _) (=)) => eapply @AE_eq_str_sub_dec : typeclass_instances.
Hint Extern 2 (StrongSubDecision (AffineExtendFull _) (AffineExtendFull _) (≤)) => eapply @AE_le_str_sub_dec : typeclass_instances.
Hint Extern 2 (StrongSubDecision (AffineExtendImage _) (AffineExtendImage _) _) => eapply @AE_im_str_sub_dec : typeclass_instances.
Hint Extern 2 (Inverse (cast ?R (AffineExtendImage ?R))) => eapply @AE_cast_inv : typeclass_instances.
Hint Extern 2 (Bijective _ _ (cast ?R (AffineExtendImage ?R))) => eapply @AE_cast_bij : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (cast ?R (AffineExtendImage ?R))) => eapply @AE_cast_ring_mor : typeclass_instances.
