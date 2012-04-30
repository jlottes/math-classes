Require Import abstract_algebra.

Section orders.

  Context `{Ae : Equiv A} {Ale : Le A} {Alt : Lt A}.

  Class PartialOrder (P:Subset A) : Prop :=
    { po_subsetoid : SubSetoid P
    ; po_proper  : Proper ((P,=) ==> (P,=) ==> impl) (≤)
    ; po_refl    :> SubReflexive  (≤) P
    ; po_trans   :> SubTransitive (≤) P
    ; po_antisym :> SubAntiSymmetric (≤) P
    }.

  Class TotalOrder (S:Subset A) : Prop :=
    { total_order_po :> PartialOrder S
    ; total_order_total :> TotalRelation (≤) S
    }.

(* The strict order from the standard library does not include (=) and thus
  does not require (<) to be Proper. *)
  Class SubStrictOrder (S:Subset A) : Prop :=
    { so_subsetoid : SubSetoid S
    ; so_proper  : Proper ((S,=) ==> (S,=) ==> impl) (<)
    ; so_irrefl  :> SubIrreflexive (<) S
    ; so_trans   :> SubTransitive  (<) S
    }.

  Context {Aue : UnEq A}.

(* The constructive notion of a total strict total order. Note that we get Proper (<)
  from cotransitivity. We will prove that (<) is in fact a SubStrictOrder. *)
  Class PseudoOrder (S:Subset A) : Prop :=
    { pseudo_order_setoid : SubStrongSetoid S
    ; pseudo_order_antisym x `{x ∊ S} y `{y ∊ S} : ¬(x < y ∧ y < x)
    ; pseudo_order_cotrans :> SubCoTransitive (<) S
    ; apart_iff_total_lt x `{x ∊ S} y `{y ∊ S} : x ≠ y ↔ x < y ∨ y < x
    }.

(* A partial order (≤) with a corresponding (<). We will prove that (<) is in fact
  a SubStrictOrder *)
  Class FullPartialOrder (P:Subset A) : Prop :=
    { strict_po_setoid : StrongSetoid A
    ; strict_po_po :> PartialOrder P
    ; strict_po_trans :> SubTransitive (<) P
    ; lt_iff_le_apart x `{x ∊ P} y `{y ∊ P} : x < y ↔ x ≤ y ∧ x ≠ y
    }.

(* A pseudo order (<) with a corresponding (≤). We will prove that (≤) is in fact
  a PartialOrder. *)
  Class FullPseudoOrder (S:Subset A) : Prop :=
    { full_pseudo_order_pseudo :> PseudoOrder S
    ; le_iff_not_lt_flip x `{x ∊ S} y `{y ∊ S} : x ≤ y ↔ ¬y < x
    }.

End orders.

Section order_maps.
  Context {A B : Type} {Ae: Equiv A} {Ale: Le A} {Alt: Lt A} {Be: Equiv B} {Ble: Le B} {Blt: Lt B}.
  Context (f : A → B).

  (* An Order_Morphism is just the factoring out of the common parts of
    OrderPreserving and OrderReflecting *)
  Class Order_Morphism (S:Subset A) (T:Subset B) :=
    { order_morphism_mor : SubSetoid_Morphism f S T
    ; order_morphism_po_a : PartialOrder S
    ; order_morphism_po_b : PartialOrder T }.

  Class StrictOrder_Morphism (S:Subset A) (T:Subset B) :=
    { strict_order_morphism_mor : SubSetoid_Morphism f S T
    ; strict_order_morphism_so_a : SubStrictOrder S
    ; strict_order_morphism_so_b : SubStrictOrder T }.

  Class OrderPreserving (S:Subset A) (T:Subset B) :=
    { order_preserving_morphism :> Order_Morphism S T
    ; order_preserving x `{x ∊ S} y `{y ∊ S} : x ≤ y → f x ≤ f y }.

  Class OrderReflecting (S:Subset A) (T:Subset B) :=
    { order_reflecting_morphism :> Order_Morphism S T
    ; order_reflecting x `{x ∊ S} y `{y ∊ S} : f x ≤ f y → x ≤ y }.

  Class OrderEmbedding (S:Subset A) (T:Subset B) :=
    { order_embedding_preserving :> OrderPreserving S T
    ; order_embedding_reflecting :> OrderReflecting S T }.

(*
  Class OrderIsomorphism `{!Inverse f} :=
    { order_iso_embedding :> OrderEmbedding
    ; order_iso_surjective :> Surjective f }.
*)

  Class StrictlyOrderPreserving (S:Subset A) (T:Subset B) :=
    { strictly_order_preserving_morphism :> StrictOrder_Morphism S T
    ; strictly_order_preserving x `{x ∊ S} y `{y ∊ S} : x < y → f x < f y }.

  Class StrictlyOrderReflecting (S:Subset A) (T:Subset B) :=
    { strictly_order_reflecting_morphism :> StrictOrder_Morphism S T
    ; strictly_order_reflecting x `{x ∊ S} y `{y ∊ S} : f x < f y → x < y }.

  Class StrictOrderEmbedding (S:Subset A) (T:Subset B) :=
    { strict_order_embedding_preserving :> StrictlyOrderPreserving S T
    ; strict_order_embedding_reflecting :> StrictlyOrderReflecting S T }.
End order_maps.

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
    `{Zero A} `{One A} {Ale : Le A} (R:Subset A) :=
  { srorder_po :> PartialOrder R
  ; srorder_semiring : SemiRing R
  ; srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : x ≤ y → ∃ `{z ∊ R}, y = x + z
  ; srorder_plus z `{z ∊ R} :> OrderEmbedding (z +) R R
  ; nonneg_mult_compat : Closed (R⁺ ==> R⁺ ==> R⁺) (.*.) }.

Class StrictSemiRingOrder `{Equiv A} `{Plus A} `{Mult A}
    `{Zero A} `{One A} {Alt : Lt A} (R:Subset A) :=
  { strict_srorder_so :> SubStrictOrder R
  ; strict_srorder_semiring : SemiRing R
  ; strict_srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : x < y → ∃ `{z ∊ R}, y = x + z
  ; strict_srorder_plus z `{z ∊ R} :> StrictOrderEmbedding (z +) R R
  ; pos_mult_compat : Closed (R₊ ==> R₊ ==> R₊) (.*.) }.

Class PseudoSemiRingOrder `{Equiv A} `{UnEq A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} {Alt : Lt A} (R:Subset A) :=
  { pseudo_srorder_strict :> PseudoOrder R
  ; pseudo_srorder_semiring : SemiRing R
  ; pseudo_srorder_partial_minus x `{x ∊ R} y `{y ∊ R} : ¬y < x → ∃ `{z ∊ R}, y = x + z
  ; pseudo_srorder_plus z `{z ∊ R} :> StrictOrderEmbedding (z +) R R
  ; pseudo_srorder_mult_ext :> SubStrongSetoid_Binary_Morphism (.*.) R R R
  ; pseudo_srorder_pos_mult_compat : Closed (R₊ ==> R₊ ==> R₊) (.*.) }.

Class FullPseudoSemiRingOrder `{Equiv A} `{UnEq A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} {Ale : Le A} {Alt : Lt A} (R:Subset A) :=
  { full_pseudo_srorder_pso :> PseudoSemiRingOrder R
  ; full_pseudo_srorder_le_iff_not_lt_flip x `{x ∊ R} y `{y ∊ R} : x ≤ y ↔ ¬y < x }.

Hint Extern 0 (_ * _ ∊ _⁺) => eapply @nonneg_mult_compat : typeclass_instances. 
Hint Extern 0 (_ * _ ∊ _₊) => eapply @pos_mult_compat    : typeclass_instances. 


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
