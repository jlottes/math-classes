Require Import
  abstract_algebra interfaces.orders orders.maps theory.setoids theory.lattices.

(*
We prove that the algebraic definition of a lattice corresponds to the
order theoretic one. Note that we do not make any of these instances global,
because that would cause loops.
*)
Section join_semilattice_order.
  Context `{JoinSemiLatticeOrder (L:=L)}.

  Instance: Setoid L := po_setoid.

  Existing Instance join_closed.
  Existing Instance closed_binary.

  Lemma join_ub_3_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x ⊔ y ⊔ z.
  Proof join_ub_r _ _.
  Lemma join_ub_3_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ x ⊔ y ⊔ z.
  Proof. subtransitivity (x ⊔ y). now apply join_ub_r. apply join_ub_l; apply _. Qed.
  Lemma join_ub_3_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ x ⊔ y ⊔ z.
  Proof. subtransitivity (x ⊔ y); apply join_ub_l; apply _. Qed.

  Lemma join_ub_3_assoc_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ x ⊔ (y ⊔ z).
  Proof join_ub_l _ _.
  Lemma join_ub_3_assoc_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ x ⊔ (y ⊔ z).
  Proof. subtransitivity (y ⊔ z). now apply join_ub_l. apply join_ub_r; apply _. Qed.
  Lemma join_ub_3_assoc_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x ⊔ (y ⊔ z).
  Proof. subtransitivity (y ⊔ z); apply join_ub_r; apply _. Qed.

  Instance: Morphism (L ⇒ L ⇒ L) (⊔).
  Proof. apply binary_morphism_proper_back.
    intros ? ? E1 ? ? E2. unfold_sigs. red_sig.
    apply (subantisymmetry (≤) _ _); apply (join_lub _ _ _).
    + rewrite (L $ E1). now apply join_ub_l.
    + rewrite (L $ E2). now apply join_ub_r.
    + rewrite <-(L $ E1). now apply join_ub_l.
    + rewrite <-(L $ E2). now apply join_ub_r.
  Qed.

  Global Instance join_sl_order_join_sl: JoinSemiLattice L.
  Proof. split. split. split; try apply _.
  + intros x ? y ? z ?. apply (subantisymmetry (≤) _ _).
    * apply (join_lub _ _ _). 2: apply (join_lub _ _ _).
      - now apply join_ub_3_l.
      - now apply join_ub_3_m.
      - now apply join_ub_3_r.
    * apply (join_lub _ _ _). apply (join_lub _ _ _).
      - now apply join_ub_3_assoc_l.
      - now apply join_ub_3_assoc_m.
      - now apply join_ub_3_assoc_r.
  + intros x ? y ?. apply (subantisymmetry (≤) _ _); apply (join_lub _ _ _);
      now first [apply join_ub_l | try apply join_ub_r].
  + intros x ?. apply (subantisymmetry (≤) _ _). now apply join_lub. now apply join_ub_l.
  Qed.

  Lemma join_le_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x → z ≤ x ⊔ y.
  Proof. intros E. subtransitivity x. now apply join_ub_l. Qed.
  Lemma join_le_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ y → z ≤ x ⊔ y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply join_le_compat_r. Qed.

  Lemma join_l x `{x ∊ L} y `{y ∊ L} : y ≤ x → x ⊔ y = x.
  Proof. intros E. apply (subantisymmetry (≤) _ _). now apply join_lub. now apply join_ub_l. Qed.
  Lemma join_r x `{x ∊ L} y `{y ∊ L} : x ≤ y → x ⊔ y = y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply join_l. Qed.

  Lemma join_sl_le_spec x `{x ∊ L} y `{y ∊ L} : x ≤ y ↔ x ⊔ y = y.
  Proof. split; intros E. now apply join_r. rewrite <-(L $ E). now apply join_ub_l. Qed.

  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (z ⊔).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply (join_lub _ _ _). now apply join_ub_l. now apply  join_le_compat_l.
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

  Lemma join_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ z → y ≤ z → x ⊔ y ≤ z.
  Proof. intros. rewrite <-(L $ idempotency (⊔) z). now apply join_le_compat. Qed.
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
  Proof. subtransitivity (x ⊓ y). apply meet_lb_l; apply _. now apply meet_lb_r. Qed.
  Lemma meet_lb_3_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ y ⊓ z ≤ x.
  Proof. subtransitivity (x ⊓ y); apply meet_lb_l; apply _. Qed.

  Lemma meet_lb_3_assoc_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ x.
  Proof meet_lb_l _ _.
  Lemma meet_lb_3_assoc_m x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ y.
  Proof. subtransitivity (y ⊓ z). apply meet_lb_r; apply _. now apply meet_lb_l. Qed.
  Lemma meet_lb_3_assoc_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊓ (y ⊓ z) ≤ z.
  Proof. subtransitivity (y ⊓ z); apply meet_lb_r; apply _. Qed.

  Instance: Morphism (L ⇒ L ⇒ L) (⊓).
  Proof. apply binary_morphism_proper_back.
    intros ? ? E1 ? ? E2. unfold_sigs. red_sig.
    apply (subantisymmetry (≤) _ _); apply (meet_glb _ _ _).
    + rewrite <-(L $ E1). now apply meet_lb_l.
    + rewrite <-(L $ E2). now apply meet_lb_r.
    + rewrite (L $ E1). now apply meet_lb_l.
    + rewrite (L $ E2). now apply meet_lb_r.
  Qed.

  Global Instance meet_sl_order_meet_sl: MeetSemiLattice L.
  Proof. split. split. split; try apply _.
  + intros x ? y ? z ?. apply (subantisymmetry (≤) _ _).
    * apply (meet_glb _ _ _). apply (meet_glb _ _ _).
      - now apply meet_lb_3_assoc_l.
      - now apply meet_lb_3_assoc_m.
      - now apply meet_lb_3_assoc_r.
    * apply (meet_glb _ _ _). 2:apply (meet_glb _ _ _).
      - now apply meet_lb_3_l.
      - now apply meet_lb_3_m.
      - now apply meet_lb_3_r.
  + intros x ? y ?. apply (subantisymmetry (≤) _ _); apply (meet_glb _ _ _);
      now first [apply meet_lb_l | try apply meet_lb_r].
  + intros x ?. apply (subantisymmetry (≤) _ _). now apply meet_lb_l. now apply meet_glb.
  Qed.


  Lemma meet_le_compat_r x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ z → x ⊓ y ≤ z.
  Proof. intros E. subtransitivity x. now apply meet_lb_l. Qed.
  Lemma meet_le_compat_l x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : y ≤ z → x ⊓ y ≤ z.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply meet_le_compat_r. Qed.

  Lemma meet_l x `{x ∊ L} y `{y ∊ L} : x ≤ y → x ⊓ y = x.
  Proof. intros E. apply (subantisymmetry (≤) _ _). now apply meet_lb_l. now apply meet_glb. Qed.
  Lemma meet_r x `{x ∊ L} y `{y ∊ L} : y ≤ x → x ⊓ y = y.
  Proof. intros E. rewrite (L $ commutativity _ _ _). now apply meet_l. Qed.

  Lemma meet_sl_le_spec x `{x ∊ L} y `{y ∊ L} : x ≤ y ↔ x ⊓ y = x.
  Proof. split; intros E. now apply meet_l. rewrite <-(L $ E). now apply meet_lb_r. Qed.

  Global Instance: ∀ `{z ∊ L}, OrderPreserving L L (z ⊓).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply (meet_glb _ _ _). now apply meet_lb_l. now apply  meet_le_compat_l.
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

  Lemma meet_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x → z ≤ y → z ≤ x ⊓ y.
  Proof. intros. rewrite <-(L $ idempotency (⊓) z). now apply meet_le_compat. Qed.
End meet_semilattice_order.

Section lattice_order.
  Context `{LatticeOrder (L:=L)}.

  Instance: Absorption (⊓) (⊔) L L.
  Proof.
    intros x ? y ?. apply (subantisymmetry (≤) _ _).
     apply (meet_lb_l _ _).
    apply (meet_le _ _ _). easy. now apply join_ub_l.
  Qed.

  Instance: Absorption (⊔) (⊓) L L.
  Proof.
    intros x ? y ?. apply (subantisymmetry (≤) _ _).
     apply (join_le _ _ _). easy. now apply meet_lb_l.
    apply (join_ub_l _ _).
  Qed.

  Global Instance lattice_order_lattice: Lattice L := {}.

  Lemma meet_join_distr_l_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z).
  Proof. apply (meet_le _ _ _).
  + apply (join_le _ _ _); now apply meet_lb_l.
  + apply (join_le _ _ _).
    * subtransitivity y. now apply meet_lb_r. now apply join_ub_l.
    * subtransitivity z. now apply meet_lb_r. now apply join_ub_r.
  Qed.

  Lemma join_meet_distr_l_le x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z).
  Proof. apply (meet_le _ _ _).
  + apply (join_le _ _ _). now apply join_ub_l.
     subtransitivity y. now apply meet_lb_l. now apply join_ub_r.
  + apply (join_le _ _ _). now apply join_ub_l.
     subtransitivity z. now apply meet_lb_r. now apply join_ub_r.
  Qed.
End lattice_order.

Definition default_join_sl_le `{Equiv A} `{Join A} : Le A :=  λ x y, x ⊔ y = y.

Section join_sl_order_alt.
  Context {A} {L:@Subset A} `{Equiv A} `{Join A} `{!JoinSemiLattice L}.
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
  Context {A} {L:@Subset A} `{Equiv A} `{Meet A} `{!MeetSemiLattice L}.
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
    intros x ? y ?. change (f (x ⊔ y) = f x ⊔ f y). case (total (≤) x y); intros E.
    + rewrite (L $ join_r _ _ E). subsymmetry. apply (join_r _ _). now apply (order_preserving _).
    + rewrite (L $ join_l _ _ E). subsymmetry. apply (join_l _ _). now apply (order_preserving _).
  Qed.
End order_preserving_join_sl_mor.

Section order_preserving_meet_sl_mor.
  Context `{MeetSemiLatticeOrder (L:=L)} `{MeetSemiLatticeOrder (L:=K)}
    `{!TotalOrder L} `{!TotalOrder K} (f: L ⇀ K) `{!OrderPreserving L K f}.

  Existing Instance order_morphism_mor.

  Lemma order_preserving_meet_sl_mor: MeetSemiLattice_Morphism L K f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. change (f (x ⊓ y) = f x ⊓ f y). case (total (≤) x y); intros E.
    + rewrite (L $ meet_l _ _ E). subsymmetry. apply (meet_l _ _). now apply (order_preserving _).
    + rewrite (L $ meet_r _ _ E). subsymmetry. apply (meet_r _ _). now apply (order_preserving _).
  Qed.
End order_preserving_meet_sl_mor.

Section full_total_order.
  Context `{MeetSemiLatticeOrder (L:=L)} `{Lt _} `{UnEq _}
    `{!FullPartialOrder L} `{!TotalOrder L}.

  Lemma total_meet_lt x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z < x → z < y → z < x ⊓ y.
  Proof.
    destruct (total (≤) x y) as [E|E];
    [ rewrite (_ $ meet_l _ _ E) | rewrite (_ $ meet_r _ _ E) ]; tauto.
  Qed.

  Context `{Zero _} `{0 ∊ L}.

  Lemma total_meet_pos x `{x ∊ L₊} y `{y ∊ L₊} : x ⊓ y ∊ L₊ .
  Proof. split. apply _. apply (total_meet_lt _ _ _); firstorder. Qed.
End full_total_order.

Hint Extern 5 (_ ⊓ _ ∊ _₊) => eapply @total_meet_pos : typeclass_instances.

