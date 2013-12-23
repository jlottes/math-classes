Require Import
  abstract_algebra interfaces.orders orders.maps theory.setoids theory.lattices.

Ltac lattice_order_tac :=
    match goal with
      | |- ?x ⊓ _ ≤ ?x => apply (meet_lb_l x _)
      | |- _ ⊓ ?x ≤ ?x => apply (meet_lb_r _ x)
      | |- ?x ≤ ?x ⊔ _ => apply (join_ub_l x _)
      | |- ?x ≤ _ ⊔ ?x => apply (join_ub_r _ x)
      | |- ?x ⊔ _ ≤ ?x => apply (join_lub _ _ _); [ subreflexivity |]
      | |- _ ⊔ ?x ≤ ?x => apply (join_lub _ _ _); [| subreflexivity ]
      | |- ?x ≤ ?x ⊓ _ => apply (meet_glb _ _ _); [ subreflexivity |]
      | |- ?x ≤ _ ⊓ ?x => apply (meet_glb _ _ _); [| subreflexivity ]
    end.

(*
We prove that the algebraic definition of a lattice corresponds to the
order theoretic one.
*)
Section join_semilattice_order.
  Context `{JoinSemiLatticeOrder (L:=L)}.

  Instance: Setoid L := po_setoid.

  Existing Instance join_closed.
  Existing Instance closed_binary.

  Lemma join_ub_3_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x ⊔ y ⊔ z.
  Proof join_ub_r _ _.
  Lemma join_ub_3_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ x ⊔ y ⊔ z.
  Proof. subtransitivity (x ⊔ y); lattice_order_tac. Qed.
  Lemma join_ub_3_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ x ⊔ y ⊔ z.
  Proof. subtransitivity (x ⊔ y); lattice_order_tac. Qed.

  Lemma join_ub_3_assoc_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ x ⊔ (y ⊔ z).
  Proof join_ub_l _ _.
  Lemma join_ub_3_assoc_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ x ⊔ (y ⊔ z).
  Proof. subtransitivity (y ⊔ z); lattice_order_tac. Qed.
  Lemma join_ub_3_assoc_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x ⊔ (y ⊔ z).
  Proof. subtransitivity (y ⊔ z); lattice_order_tac. Qed.

  Instance: Morphism (L ⇒ L ⇒ L) (⊔).
  Proof with lattice_order_tac. apply binary_morphism_proper_back.
    intros ? ? E1 ? ? E2. unfold_sigs. red_sig.
    apply (antisymmetry (≤) _ _); apply (join_lub _ _ _).
    + rewrite (L $ E1)...
    + rewrite (L $ E2)...
    + rewrite <-(L $ E1)...
    + rewrite <-(L $ E2)...
  Qed.

  Global Instance join_sl_order_join_sl: JoinSemiLattice L.
  Proof. split. split. split; try apply _.
  + intros x ? y ? z ?. apply (antisymmetry (≤) _ _).
    * apply (join_lub _ _ _). 2: apply (join_lub _ _ _).
      - now apply join_ub_3_l.
      - now apply join_ub_3_m.
      - now apply join_ub_3_r.
    * apply (join_lub _ _ _). apply (join_lub _ _ _).
      - now apply join_ub_3_assoc_l.
      - now apply join_ub_3_assoc_m.
      - now apply join_ub_3_assoc_r.
  + change (Commutative (⊔) L). intros x ? y ?.
    apply (antisymmetry (≤) _ _); apply (join_lub _ _ _); lattice_order_tac.
  + change (BinaryIdempotent (⊔) L). intros x ?.
    apply (antisymmetry (≤) _ _); now lattice_order_tac.
  Qed.

  Lemma join_le_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x → z ≤ x ⊔ y.
  Proof. intros E. subtransitivity x. lattice_order_tac. Qed.
  Lemma join_le_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ y → z ≤ x ⊔ y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply join_le_compat_r. Qed.

  Lemma join_l x `{x ∊ L} y `{y ∊ L} : y ≤ x → x ⊔ y = x.
  Proof. intros E. apply (antisymmetry (≤) _ _); now lattice_order_tac. Qed.
  Lemma join_r x `{x ∊ L} y `{y ∊ L} : x ≤ y → x ⊔ y = y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply join_l. Qed.

  Lemma join_sl_le_spec x `{x ∊ L} y `{y ∊ L} : x ≤ y ↔ x ⊔ y = y.
  Proof. split; intros E. now apply join_r. rewrite <-(L $ E). lattice_order_tac. Qed.

  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (z ⊔).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply (join_lub _ _ _). lattice_order_tac. now apply  join_le_compat_l.
  Qed.
  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (⊔ z).
  Proof. intros. apply maps.order_preserving_flip. Qed.

  Lemma join_le_compat x₁ `{x₁ ∊ L} x₂ `{x₂ ∊ L} y₁ `{y₁ ∊ L} y₂ `{y₂ ∊ L}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ ⊔ y₁ ≤ x₂ ⊔ y₂.
  Proof.
    intros E1 E2. subtransitivity (x₁ ⊔ y₂).
     now apply (order_preserving (x₁ ⊔)).
    now apply (order_preserving (⊔ y₂)).
  Qed.

End join_semilattice_order.

Section bounded_join_semilattice.
  Context `{JoinSemiLatticeOrder (L:=L)} `{Bottom _} `{!BoundedJoinSemiLattice L}.

  Lemma above_bottom x `{x ∊ L} : ⊥ ≤ x.
  Proof. rewrite (join_sl_le_spec _ _). exact (join_bottom_l _). Qed.

  Lemma below_bottom x `{x ∊ L} : x ≤ ⊥ → x = ⊥.
  Proof. rewrite (join_sl_le_spec _ _). now rewrite (L $ join_bottom_r x). Qed.
End bounded_join_semilattice.

Section meet_semilattice_order.
  Context `{MeetSemiLatticeOrder (L:=L)}.

  Instance: Setoid L := po_setoid.

  Existing Instance meet_closed.
  Existing Instance closed_binary.

  Lemma meet_lb_3_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ y ⊓ z ≤ z.
  Proof meet_lb_r _ _.
  Lemma meet_lb_3_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ y ⊓ z ≤ y.
  Proof. subtransitivity (x ⊓ y); lattice_order_tac. Qed.
  Lemma meet_lb_3_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ y ⊓ z ≤ x.
  Proof. subtransitivity (x ⊓ y); lattice_order_tac. Qed.

  Lemma meet_lb_3_assoc_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ x.
  Proof meet_lb_l _ _.
  Lemma meet_lb_3_assoc_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ y.
  Proof. subtransitivity (y ⊓ z); lattice_order_tac. Qed.
  Lemma meet_lb_3_assoc_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ z.
  Proof. subtransitivity (y ⊓ z); lattice_order_tac. Qed.

  Instance: Morphism (L ⇒ L ⇒ L) (⊓).
  Proof with lattice_order_tac. apply binary_morphism_proper_back.
    intros ? ? E1 ? ? E2. unfold_sigs. red_sig.
    apply (antisymmetry (≤) _ _); apply (meet_glb _ _ _).
    + rewrite <-(L $ E1)...
    + rewrite <-(L $ E2)...
    + rewrite (L $ E1)...
    + rewrite (L $ E2)...
  Qed.

  Global Instance meet_sl_order_meet_sl: MeetSemiLattice L.
  Proof. split. split. split; try apply _.
  + intros x ? y ? z ?. apply (antisymmetry (≤) _ _).
    * apply (meet_glb _ _ _). apply (meet_glb _ _ _).
      - now apply meet_lb_3_assoc_l.
      - now apply meet_lb_3_assoc_m.
      - now apply meet_lb_3_assoc_r.
    * apply (meet_glb _ _ _). 2:apply (meet_glb _ _ _).
      - now apply meet_lb_3_l.
      - now apply meet_lb_3_m.
      - now apply meet_lb_3_r.
  + change (Commutative (⊓) L). intros x ? y ?.
    apply (antisymmetry (≤) _ _); apply (meet_glb _ _ _); lattice_order_tac.
  + change (BinaryIdempotent (⊓) L). intros x ?.
    apply (antisymmetry (≤) _ _); now lattice_order_tac.
  Qed.


  Lemma meet_le_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ z → x ⊓ y ≤ z.
  Proof. intros E. subtransitivity x. lattice_order_tac. Qed.
  Lemma meet_le_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ z → x ⊓ y ≤ z.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply meet_le_compat_r. Qed.

  Lemma meet_l x `{x ∊ L} y `{y ∊ L} : x ≤ y → x ⊓ y = x.
  Proof. intros E. apply (antisymmetry (≤) _ _); now lattice_order_tac. Qed.
  Lemma meet_r x `{x ∊ L} y `{y ∊ L} : y ≤ x → x ⊓ y = y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply meet_l. Qed.

  Lemma meet_sl_le_spec x `{x ∊ L} y `{y ∊ L} : x ≤ y ↔ x ⊓ y = x.
  Proof. split; intros E. now apply meet_l. rewrite <-(L $ E). lattice_order_tac. Qed.

  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (z ⊓).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply (meet_glb _ _ _). lattice_order_tac. now apply  meet_le_compat_l.
  Qed.
  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (⊓ z).
  Proof. intros. apply maps.order_preserving_flip. Qed.

  Lemma meet_le_compat x₁ `{x₁ ∊ L} x₂ `{x₂ ∊ L} y₁ `{y₁ ∊ L} y₂ `{y₂ ∊ L}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ ⊓ y₁ ≤ x₂ ⊓ y₂.
  Proof.
    intros E1 E2. subtransitivity (x₁ ⊓ y₂).
     now apply (order_preserving (x₁ ⊓)).
    now apply (order_preserving (⊓ y₂)).
  Qed.

End meet_semilattice_order.

Ltac lattice_order_simplify L :=
    repeat match goal with
      | E : ?x ≤ ?y |- context [ ?x ⊔ ?y ] => rewrite (L $ join_r _ _ E)
      | E : ?x ≤ ?y |- context [ ?y ⊔ ?x ] => rewrite (L $ join_l _ _ E)
      | E : ?x ≤ ?y |- context [ ?x ⊓ ?y ] => rewrite (L $ meet_l _ _ E)
      | E : ?x ≤ ?y |- context [ ?y ⊓ ?x ] => rewrite (L $ meet_r _ _ E)
      | |- context [ ?x ⊔ ?x ] => rewrite (L $ idempotency (⊔) x)
      | |- context [ ?x ⊓ ?x ] => rewrite (L $ idempotency (⊓) x)
    end.

Section lattice_order.
  Context `{LatticeOrder (L:=L)}.

  Instance: Absorption (⊓) (⊔) L L.
  Proof. intros x ? y ?. apply (antisymmetry (≤) _ _); repeat lattice_order_tac. Qed.

  Instance: Absorption (⊔) (⊓) L L.
  Proof. intros x ? y ?. apply (antisymmetry (≤) _ _); repeat lattice_order_tac. Qed.

  Global Instance lattice_order_lattice: Lattice L := {}.

  Lemma meet_join_distr_l_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z).
  Proof with try lattice_order_tac.
    apply (meet_glb _ _ _); apply (join_lub _ _ _)...
    subtransitivity y...
    subtransitivity z...
  Qed.

  Lemma join_meet_distr_l_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z).
  Proof with try lattice_order_tac.
    apply (meet_glb _ _ _); apply (join_lub _ _ _)...
    subtransitivity y...
    subtransitivity z...
  Qed.
End lattice_order.

Definition default_join_sl_le `{Equiv A} `{Join A} : Le A :=  λ x y, x ⊔ y = y.

Section join_sl_order_alt.
  Context {A} {L:@set A} `{Equiv A} `{Join A} `{!JoinSemiLattice L}.
  Context `{Le A} (le_correct : ∀ `{x ∊ L} `{y ∊ L}, x ≤ y ↔ x ⊔ y = y).

  Lemma alt_Build_JoinSemiLatticeOrder : JoinSemiLatticeOrder L.
  Proof. split. 2: apply _. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. rewrite !(le_correct _ _ _ _), (L $ E1), (L $ E2). now intro.
  + intros ??. rewrite !(le_correct _ _ _ _). exact (idempotency _ _).
  + intros ?? ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite <- (L $ E2), (L $ associativity _ _ _ _), (L $ E1).
  + intros ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite <- (L $ E1), (L $ commutativity _ _ _), <-(L $ E2) at 1.
  + intros ?? ??. now rewrite !(le_correct _ _ _ _), (L $ associativity _ _ _ _), (L $ idempotency _ _).
  + intros ?? ??. rewrite !(le_correct _ _ _ _), (L $ commutativity _ _ _).
    now rewrite <-(L $ associativity _ _ _ _), (L $ idempotency _ _).
  + intros ?? ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite <-(L $ associativity _ _ _ _), (L $ E2).
  Qed.
End join_sl_order_alt.

Definition default_meet_sl_le `{Equiv A} `{Meet A} : Le A :=  λ x y, x ⊓ y = x.

Section meet_sl_order_alt.
  Context {A} {L:@set A} `{Equiv A} `{Meet A} `{!MeetSemiLattice L}.
  Context `{Le A} (le_correct : ∀ `{x ∊ L} `{y ∊ L}, x ≤ y ↔ x ⊓ y = x).

  Lemma alt_Build_MeetSemiLatticeOrder : MeetSemiLatticeOrder L.
  Proof. split. 2: apply _. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. rewrite !(le_correct _ _ _ _), (L $ E1), (L $ E2). now intro.
  + intros ??. rewrite !(le_correct _ _ _ _). exact (idempotency _ _).
  + intros ?? ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite <- (L $ E1), <-(L $ associativity _ _ _ _), (L $ E2).
  + intros ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite <- (L $ E2), (L $ commutativity _ _ _), <-(L $ E1) at 1.
  + intros ?? ??. rewrite !(le_correct _ _ _ _), (L $ commutativity _ _ _).
    now rewrite (L $ associativity _ _ _ _), (L $ idempotency _ _).
  + intros ?? ??. now rewrite !(le_correct _ _ _ _),<-(L $ associativity _ _ _ _), (L $ idempotency _ _).
  + intros ?? ?? ??. rewrite !(le_correct _ _ _ _). intros E1 E2.
    now rewrite (L $ associativity _ _ _ _), (L $ E1).
  Qed.
End meet_sl_order_alt.

Section join_order_preserving.
  Context `{JoinSemiLatticeOrder (L:=L)} `{JoinSemiLatticeOrder (L:=K)}
    (f : L ⇀ K) `{!JoinSemiLattice_Morphism L K f}.

  Lemma join_sl_mor_preserving: OrderPreserving L K f.
  Proof.
    repeat (split; try apply _).
    intros ?? ??. rewrite 2!(join_sl_le_spec _ _), <-(K $ preserves_join f _ _).
    intros E. now rewrite (L $ E).
  Qed.

  Lemma join_sl_mor_reflecting `{!Injective L K f}: OrderReflecting L K f.
  Proof.
    repeat (split; try apply _).
    intros ?? ??. rewrite 2!(join_sl_le_spec _ _), <-(K $ preserves_join f _ _).
    intros. now apply (injective f _ _).
  Qed.
End join_order_preserving.

Section meet_order_preserving.
  Context `{MeetSemiLatticeOrder (L:=L)} `{MeetSemiLatticeOrder (L:=K)}
    (f : L ⇀ K) `{!MeetSemiLattice_Morphism L K f}.

  Lemma meet_sl_mor_preserving: OrderPreserving L K f.
  Proof.
    repeat (split; try apply _).
    intros ?? ??. rewrite 2!(meet_sl_le_spec _ _), <-(K $ preserves_meet f _ _).
    intros E. now rewrite (L $ E).
  Qed.

  Lemma meet_sl_mor_reflecting `{!Injective L K f}: OrderReflecting L K f.
  Proof.
    repeat (split; try apply _).
    intros ?? ??. rewrite 2!(meet_sl_le_spec _ _), <-(K $ preserves_meet f _ _).
    intros. now apply (injective f _ _).
  Qed.
End meet_order_preserving.

Section order_preserving_join_sl_mor.
  Context `{JoinSemiLatticeOrder (L:=L)} `{JoinSemiLatticeOrder (L:=K)}
    `{!TotalOrder L} `{!TotalOrder K} (f: L ⇀ K) `{!OrderPreserving L K f}.

  Existing Instance order_morphism_mor.

  Lemma order_preserving_join_sl_mor: JoinSemiLattice_Morphism L K f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. change (f (x ⊔ y) = f x ⊔ f y). subsymmetry.
    case (total (≤) x y); intro; lattice_order_simplify L;
    [ apply (join_r _ _) | apply (join_l _ _) ];
    now apply (order_preserving f).
  Qed.
End order_preserving_join_sl_mor.

Section order_preserving_meet_sl_mor.
  Context `{MeetSemiLatticeOrder (L:=L)} `{MeetSemiLatticeOrder (L:=K)}
    `{!TotalOrder L} `{!TotalOrder K} (f: L ⇀ K) `{!OrderPreserving L K f}.

  Existing Instance order_morphism_mor.

  Lemma order_preserving_meet_sl_mor: MeetSemiLattice_Morphism L K f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. change (f (x ⊓ y) = f x ⊓ f y). subsymmetry.
    case (total (≤) x y); intro; lattice_order_simplify L;
    [ apply (meet_l _ _) | apply (meet_r _ _) ];
    now apply (order_preserving f).
  Qed.
End order_preserving_meet_sl_mor.

Require Import orders.orders.

Section join_strict.
  Context `{JoinSemiLatticeOrder (L:=L)} `{Lt _} `{UnEq _} `{!FullPartialOrder L}.

  Lemma join_lt_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z < x → z < x ⊔ y.
  Proof. intros E. apply (lt_le_trans _ x _); trivial; lattice_order_tac. Qed.
  Lemma join_lt_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z < y → z < x ⊔ y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply join_lt_compat_r. Qed.
End join_strict.

Section meet_strict.
  Context `{MeetSemiLatticeOrder (L:=L)} `{Lt _} `{UnEq _} `{!FullPartialOrder L}.

  Lemma meet_lt_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x < z → x ⊓ y < z.
  Proof. intros E. apply (le_lt_trans _ x _); trivial; lattice_order_tac. Qed.
  Lemma meet_lt_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y < z → x ⊓ y < z.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply meet_lt_compat_r. Qed.
End meet_strict.

Section join_full.
  Context `{FullJoinSemiLatticeOrder (L:=L)}.

  Global Instance: JoinSemiLatticeOrder L.
  Proof. split. apply _.
  + exact full_join_closed.
  + exact full_join_ub_l.
  + exact full_join_ub_r.
  + intros x ? y ? z ?. assert (x ⊔ y ∊ L) by now apply full_join_closed.
    rewrite 3!(le_iff_not_lt_flip _ _). intros E1 E2 E3.
    destruct (join_sub _ _ _ E3). now destruct E1. now destruct E2.
  Qed.

  Lemma join_sub_l x `{x ∊ L} y `{y ∊ L} : x < x ⊔ y → x < y.
  Proof. intro E. destruct (join_sub _ _ _ E); trivial. now destruct (irreflexivity (<) x). Qed.

  Lemma join_sub_r x `{x ∊ L} y `{y ∊ L} : y < x ⊔ y → y < x.
  Proof. intro E. destruct (join_sub _ _ _ E); trivial. now destruct (irreflexivity (<) y). Qed.

  Lemma join_lt x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x < z → y < z → x ⊔ y < z.
  Proof. intros E1 E2.
    destruct (cotransitivity E1 (x ⊔ y)); trivial.
    assert (x ≤ y) as E3 by now apply (lt_le _ _); apply (join_sub_l _ _).
    now lattice_order_simplify L.
  Qed.

  Lemma join_lt_compat x₁ `{x₁ ∊ L} x₂ `{x₂ ∊ L} y₁ `{y₁ ∊ L} y₂ `{y₂ ∊ L}
  : x₁ < x₂ → y₁ < y₂ → x₁ ⊔ y₁ < x₂ ⊔ y₂.
  Proof. intros E1 E2. apply (join_lt _ _ _).
    apply (lt_le_trans _ x₂ _); trivial; lattice_order_tac.
    apply (lt_le_trans _ y₂ _); trivial; lattice_order_tac.
  Qed.
End join_full.

Section meet_full.
  Context `{FullMeetSemiLatticeOrder (L:=L)}.

  Global Instance: MeetSemiLatticeOrder L.
  Proof. split. apply _.
  + exact full_meet_closed.
  + exact full_meet_lb_l.
  + exact full_meet_lb_r.
  + intros x ? y ? z ?. assert (x ⊓ y ∊ L) by now apply full_meet_closed.
    rewrite 3!(le_iff_not_lt_flip _ _). intros E1 E2 E3.
    destruct (meet_slb _ _ _ E3). now destruct E1. now destruct E2.
  Qed.

  Lemma meet_slb_l x `{x ∊ L} y `{y ∊ L} : x ⊓ y < x → y < x.
  Proof. intro E. destruct (meet_slb _ _ _ E); trivial. now destruct (irreflexivity (<) x). Qed.

  Lemma meet_slb_r x `{x ∊ L} y `{y ∊ L} : x ⊓ y < y → x < y.
  Proof. intro E. destruct (meet_slb _ _ _ E); trivial. now destruct (irreflexivity (<) y). Qed.

  Lemma meet_lt x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z < x → z < y → z < x ⊓ y.
  Proof. intros E1 E2.
    destruct (cotransitivity E1 (x ⊓ y)); trivial.
    assert (y ≤ x) as E3 by now apply (lt_le _ _); apply (meet_slb_l _ _).
    now lattice_order_simplify L.
  Qed.

  Lemma meet_lt_compat x₁ `{x₁ ∊ L} x₂ `{x₂ ∊ L} y₁ `{y₁ ∊ L} y₂ `{y₂ ∊ L}
  : x₁ < x₂ → y₁ < y₂ → x₁ ⊓ y₁ < x₂ ⊓ y₂.
  Proof. intros E1 E2. apply (meet_lt _ _ _).
    apply (le_lt_trans _ x₁ _); trivial; lattice_order_tac.
    apply (le_lt_trans _ y₁ _); trivial; lattice_order_tac.
  Qed.
End meet_full.

Global Instance: ∀ `{FullLatticeOrder (L:=L)}, LatticeOrder L := {}.

Section dec_full_lattice_order.
  Context `{FullPseudoOrder (S:=L)} `{!SubDecision L L (<)}.

  Instance dec_full_join_semilattice_order `{Join _} `{!JoinSemiLatticeOrder L}
    : FullJoinSemiLatticeOrder L.
  Proof. split; try apply _.
  + exact join_ub_l.
  + exact join_ub_r.
  + intros x ? y ? z ? E.
    destruct (decide_sub (<) z x) as [?| E1]. now left.
    destruct (decide_sub (<) z y) as [?| E2]. now right.
    cut False. tauto. revert E. apply (le_iff_not_lt_flip _ _).
    revert E1 E2. rewrite <-2!(le_iff_not_lt_flip _ _).
    exact (join_lub _ _ _).
  Qed.

  Instance dec_full_meet_semilattice_order `{Meet _} `{!MeetSemiLatticeOrder L}
    : FullMeetSemiLatticeOrder L.
  Proof. split; try apply _.
  + exact meet_lb_l.
  + exact meet_lb_r.
  + intros x ? y ? z ? E.
    destruct (decide_sub (<) x z) as [?| E1]. now left.
    destruct (decide_sub (<) y z) as [?| E2]. now right.
    cut False. tauto. revert E. apply (le_iff_not_lt_flip _ _).
    revert E1 E2. rewrite <-2!(le_iff_not_lt_flip _ _).
    exact (meet_glb _ _ _).
  Qed.

  Instance dec_full_lattice_order `{Join _} `{Meet _} `{!LatticeOrder L}
    : FullLatticeOrder L := {}.
End dec_full_lattice_order.

Section strictly_order_reflecting_join_sl_mor.
  Context `{FullJoinSemiLatticeOrder (L:=L)} `{FullJoinSemiLatticeOrder (L:=K)}
    (f: L ⇀ K) `{!StrictlyOrderReflecting L K f}.

  Existing Instance full_pseudo_order_preserving.
  Existing Instance strict_order_morphism_mor.

  Global Instance strictly_order_reflecting_join_sl_mor: JoinSemiLattice_Morphism L K f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. change (f (x ⊔ y) = f x ⊔ f y).
    apply (antisymmetry le _ _).
    + apply (le_iff_not_lt_flip _ _). intro.
      destruct (irreflexivity (<) x). subtransitivity y;
      [ apply (join_sub_l _ _) | apply (join_sub_r _ _) ];
      apply (strictly_order_reflecting f _ _);
      apply (le_lt_trans _ (f x ⊔ f y) _); trivial; lattice_order_tac.
    + apply (join_lub _ _ _); apply (order_preserving f _ _); lattice_order_tac.
  Qed.
End strictly_order_reflecting_join_sl_mor.

Section strictly_order_reflecting_meet_sl_mor.
  Context `{FullMeetSemiLatticeOrder (L:=L)} `{FullMeetSemiLatticeOrder (L:=K)}
    (f: L ⇀ K) `{!StrictlyOrderReflecting L K f}.

  Existing Instance full_pseudo_order_preserving.
  Existing Instance strict_order_morphism_mor.

  Global Instance strictly_order_reflecting_meet_sl_mor: MeetSemiLattice_Morphism L K f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. change (f (x ⊓ y) = f x ⊓ f y).
    apply (antisymmetry le _ _).
    + apply (meet_glb _ _ _); apply (order_preserving f _ _); lattice_order_tac.
    + apply (le_iff_not_lt_flip _ _). intro.
      destruct (irreflexivity (<) x). subtransitivity y;
      [ apply (meet_slb_r _ _) | apply (meet_slb_l _ _) ];
      apply (strictly_order_reflecting f _ _);
      apply (lt_le_trans _ (f x ⊓ f y) _); trivial; lattice_order_tac.
  Qed.
End strictly_order_reflecting_meet_sl_mor.

Instance strictly_order_reflecting_lattice_mor
  `{FullLatticeOrder (L:=L)} `{FullLatticeOrder (L:=K)}
  (f: L ⇀ K) `{!StrictlyOrderReflecting L K f}
  : Lattice_Morphism L K f := {}.
