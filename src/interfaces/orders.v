Require Import abstract_algebra.

Section orders.

  Context `{Ae : Equiv A} {Ale : Le A} {Alt : Lt A} {Ameet: Meet A} {AJoin: Join A}.

  Class PartialOrder P : Prop :=
    { po_setoid : Setoid P
    ; po_proper  : Proper ((P,=) ==> (P,=) ==> impl) (≤)
    ; po_refl    :> SubReflexive  P (≤)
    ; po_trans   :> SubTransitive P (≤)
    ; po_antisym :> SubAntiSymmetric P (≤)
    }.

  Class TotalOrder S : Prop :=
    { total_order_po :> PartialOrder S
    ; total_order_total :> TotalRelation S (≤)
    }.

  (*
  We define a variant of the order theoretic definition of meet and join
  semilattices. Notice that we include a meet operation instead of the
  more common:
    ∀ x y, ∃ m, m ≤ x ∧ m ≤ y ∧ ∀ z, z ≤ x → z ≤ y → m ≤ z
  Our definition is both stronger and more convenient than the above.
  This is needed to prove equavalence with the algebraic definition. We
  do this in orders.lattices.
  *)
  Class MeetSemiLatticeOrder L : Prop :=
    { meet_sl_order :>> PartialOrder L
    ; meet_closed : Closed (L ⇀ L ⇀ L) (⊓)
    ; meet_lb_l x `{x ∊ L} y `{y ∊ L} : x ⊓ y ≤ x
    ; meet_lb_r x `{x ∊ L} y `{y ∊ L} : x ⊓ y ≤ y
    ; meet_glb x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : z ≤ x → z ≤ y → z ≤ x ⊓ y
    }.

  Class JoinSemiLatticeOrder L : Prop :=
    { join_sl_order :>> PartialOrder L
    ; join_closed : Closed (L ⇀ L ⇀ L) (⊔)
    ; join_ub_l x `{x ∊ L} y `{y ∊ L} : x ≤ x ⊔ y
    ; join_ub_r x `{x ∊ L} y `{y ∊ L} : y ≤ x ⊔ y
    ; join_lub x `{x ∊ L} y `{y ∊ L} z `{z ∊ L} : x ≤ z → y ≤ z → x ⊔ y ≤ z
    }.

  Class LatticeOrder L : Prop :=
    { lattice_order_meet :>> MeetSemiLatticeOrder L
    ; lattice_order_join :>> JoinSemiLatticeOrder L
    }.

  Class StrictSetoidOrder S : Prop :=
    { so_setoid : Setoid S
    ; so_proper  : Proper ((S,=) ==> (S,=) ==> impl) (<)
    ; so_irrefl  :> SubIrreflexive S (<)
    ; so_trans   :> SubTransitive  S (<)
    }.

  Context {Aue : UnEq A}.

(* The constructive notion of a total strict total order. Note that we get Proper (<)
  from cotransitivity. We will prove that (<) is in fact a StrictSetoidOrder. *)
  Class PseudoOrder S : Prop :=
    { pseudo_order_setoid : StrongSetoid S
    ; pseudo_order_antisym x `{x ∊ S} y `{y ∊ S} : ¬(x < y ∧ y < x)
    ; pseudo_order_cotrans :> SubCoTransitive S (<)
    ; apart_iff_total_lt x `{x ∊ S} y `{y ∊ S} : x ≠ y ↔ x < y ∨ y < x
    }.

(* A partial order (≤) with a corresponding (<). We will prove that (<) is in fact
  a StrictSetoidOrder *)
  Class FullPartialOrder P : Prop :=
    { strict_po_setoid : StrongSetoid P
    ; strict_po_po :> PartialOrder P
    ; strict_po_trans :> SubTransitive P (<)
    ; lt_iff_le_apart x `{x ∊ P} y `{y ∊ P} : x < y ↔ x ≤ y ∧ x ≠ y
    }.

(* A pseudo order (<) with a corresponding (≤). We will prove that (≤) is in fact
  a PartialOrder. *)
  Class FullPseudoOrder S : Prop :=
    { full_pseudo_order_pseudo :> PseudoOrder S
    ; le_iff_not_lt_flip x `{x ∊ S} y `{y ∊ S} : x ≤ y ↔ ¬y < x
    }.

End orders.

Section order_maps.
  Context {A B} {Ae: Equiv A} {Ale: Le A} {Alt: Lt A} {Be: Equiv B} {Ble: Le B} {Blt: Lt B}.
  Context (S:@Subset A) (T:@Subset B) (f : A → B).

  (* An Order_Morphism is just the factoring out of the common parts of
    OrderPreserving and OrderReflecting *)
  Class Order_Morphism :=
    { order_morphism_mor : Morphism (S ⇒ T) f
    ; order_morphism_po_a : PartialOrder S
    ; order_morphism_po_b : PartialOrder T }.

  Class StrictOrder_Morphism :=
    { strict_order_morphism_mor : Morphism (S ⇒ T) f
    ; strict_order_morphism_so_a : StrictSetoidOrder S
    ; strict_order_morphism_so_b : StrictSetoidOrder T }.

  Class OrderPreserving :=
    { order_preserving_morphism :> Order_Morphism
    ; order_preserving `{x ∊ S} `{y ∊ S} : x ≤ y → f x ≤ f y }.

  Class OrderReflecting :=
    { order_reflecting_morphism :> Order_Morphism
    ; order_reflecting `{x ∊ S} `{y ∊ S} : f x ≤ f y → x ≤ y }.

  Class OrderEmbedding :=
    { order_embedding_preserving :> OrderPreserving
    ; order_embedding_reflecting :> OrderReflecting }.

  Lemma order_embedding `{!OrderEmbedding} `{x ∊ S} `{y ∊ S} : x ≤ y ↔ f x ≤ f y.
  Proof. split. now apply order_preserving. now apply order_reflecting. Qed.

  Class OrderIsomorphism `{!Inverse (f:S ⇀ T)} :=
    { order_iso_embedding :> OrderEmbedding
    ; order_iso_surjective :> Surjective S T f }.

  Class StrictlyOrderPreserving :=
    { strictly_order_preserving_morphism :> StrictOrder_Morphism
    ; strictly_order_preserving `{x ∊ S} `{y ∊ S} : x < y → f x < f y }.

  Class StrictlyOrderReflecting :=
    { strictly_order_reflecting_morphism :> StrictOrder_Morphism
    ; strictly_order_reflecting `{x ∊ S} `{y ∊ S} : f x < f y → x < y }.

  Class StrictOrderEmbedding :=
    { strict_order_embedding_preserving :> StrictlyOrderPreserving
    ; strict_order_embedding_reflecting :> StrictlyOrderReflecting }.

  Lemma strictly_order_embedding `{!StrictOrderEmbedding} `{x ∊ S} `{y ∊ S} : x < y ↔ f x < f y.
  Proof. split. now apply strictly_order_preserving. now apply strictly_order_reflecting. Qed.
End order_maps.
Arguments order_morphism_mor {A B _ _ _ _ S T} f {_} _ _ _.
Arguments order_preserving {A B _ _ _ _ S T} f {_} x {_} y {_} _.
Arguments order_reflecting {A B _ _ _ _ S T} f {_} x {_} y {_} _.
Arguments order_embedding  {A B _ _ _ _ S T} f {_} x {_} y {_}.
Arguments strict_order_morphism_mor {A B _ _ _ _ S T} f {_} _ _ _.
Arguments strictly_order_preserving {A B _ _ _ _ S T} f {_} x {_} y {_} _.
Arguments strictly_order_reflecting {A B _ _ _ _ S T} f {_} x {_} y {_} _.
Arguments strictly_order_embedding  {A B _ _ _ _ S T} f {_} x {_} y {_}.

Hint Extern 4 (?f _ ≤ ?f _) => apply (order_preserving f).
Hint Extern 4 (?f _ < ?f _) => apply (strictly_order_preserving f).

(*
We define various classes to describe the order on the lower part of the
algebraic hierarchy. This results in the notion of a PseudoSemiRingOrder, which
specifies the order on the naturals, integers, rationals and reals. This notion
is quite similar to a strictly linearly ordered unital commutative protoring in
Davorin Lešnik's PhD thesis.
*)
Class SemiRingOrder `{Equiv A} `{Plus A} `{Mult A}
    `{Zero A} `{One A} {Ale : Le A} R :=
  { srorder_po :> PartialOrder R
  ; srorder_semiring : SemiRing R
  ; srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : x ≤ y → ∃ `{z ∊ R}, y = x + z
  ; srorder_plus z `{z ∊ R} :> OrderEmbedding R R (z +)
  ; nonneg_mult_compat : Closed (R⁺ ⇀ R⁺ ⇀ R⁺) (.*.) }.

Class StrictSemiRingOrder `{Equiv A} `{Plus A} `{Mult A}
    `{Zero A} `{One A} {Alt : Lt A} R :=
  { strict_srorder_so :> StrictSetoidOrder R
  ; strict_srorder_semiring : SemiRing R
  ; strict_srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : x < y → ∃ `{z ∊ R}, y = x + z
  ; strict_srorder_plus z `{z ∊ R} :> StrictOrderEmbedding R R (z +)
  ; pos_mult_compat : Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.) }.

Class PseudoSemiRingOrder `{Equiv A} `{UnEq A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} {Alt : Lt A} R :=
  { pseudo_srorder_strict :> PseudoOrder R
  ; pseudo_srorder_semiring : SemiRing R
  ; pseudo_srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : ¬y < x → ∃ `{z ∊ R}, y = x + z
  ; pseudo_srorder_plus z `{z ∊ R} :> StrictOrderEmbedding R R (z +)
  ; pseudo_srorder_mult_ext :> Strong_Binary_Morphism R R R (.*.)
  ; pseudo_srorder_pos_mult_compat : Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.) }.

Class FullPseudoSemiRingOrder `{Equiv A} `{UnEq A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} {Ale : Le A} {Alt : Lt A} R :=
  { full_pseudo_srorder_pso :> PseudoSemiRingOrder R
  ; full_pseudo_srorder_le_iff_not_lt_flip x `{x ∊ R} y `{y ∊ R} : x ≤ y ↔ ¬y < x }.

Hint Extern 4 (_ * _ ∊ _⁺) => eapply @nonneg_mult_compat : typeclass_instances. 
Hint Extern 4 (_ * _ ∊ _₊) => eapply @pos_mult_compat    : typeclass_instances. 
Hint Extern 20 (Closed (?R⁺ ⇀ ?R⁺ ⇀ ?R⁺) (.*.)) => eapply @nonneg_mult_compat : typeclass_instances. 
Hint Extern 20 (Closed (?R₊ ⇀ ?R₊ ⇀ ?R₊) (.*.)) => eapply @pos_mult_compat    : typeclass_instances. 

(* Absolute value for ring orders, useful only for total orders *)
Local Open Scope mc_abs_scope.
Class DecAbs `{Equiv A} `{Negate A} `{Zero A} {l:Le A} {a:Abs A} R :=
  { abs_closed : Closed (R ⇀ R) |·|
  ; abs_nonneg x `{x ∊ R⁺} : |x| = x
  ; abs_nonpos x `{x ∊ R⁻} : |x| = -x
  }.

(* Due to bug #2528 *)
(*
Hint Extern 7 (PropHolds (0 < _ * _)) => eapply @pos_mult_compat : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ _ * _)) => eapply @nonneg_mult_compat : typeclass_instances.
*)

(*
Alternatively, we could have defined the standard notion of a RingOrder:

Class RingOrder `{Equiv A} `{Plus A} `{Mult A} `{Zero A} (Ale : Le A) :=
  { ringorder_po :> PartialOrder Ale
  ; ringorder_plus :> ∀ z, OrderPreserving (z +)
  ; ringorder_mult : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ x * y }.

Unfortunately, this notion is too weak when we consider semirings (e.g. the
naturals). Moreover, in case of rings, we prove that this notion is equivalent
to our SemiRingOrder class (see orders.rings.from_ring_order). Hence we omit
defining such a class.

Similarly we prove that a FullSemiRingOrder and a FullPseudoRingOrder are equivalent.

Class FullPseudoRingOrder `{Equiv A} `{Apart A} `{Plus A}
    `{Mult A} `{Zero A} (Ale : Le A) (Alt : Lt A) :=
  { pseudo_ringorder_spo :> FullPseudoOrder Ale Alt
  ; pseudo_ringorder_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
  ; pseudo_ringorder_plus :> ∀ z, StrictlyOrderPreserving (z +)
  ; pseudo_ringorder_mult : ∀ x y, 0 < x → 0 < y → 0 < x * y }.
*)
