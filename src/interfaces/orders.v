Require Import abstract_algebra.


Class PartialOrder `{Ae : Equiv A} (Ale : Le A) (P:Subset A) : Prop :=
  { po_subsetoid : SubSetoid P
  ; po_proper  : Proper ((P,=) ==> (P,=) ==> impl) (≤)
  ; po_refl    :> SubReflexive  (≤) P
  ; po_trans   :> SubTransitive (≤) P
  ; po_antisym :> SubAntiSymmetric (≤) P
  }.

Class TotalOrder `{Ae : Equiv A} (Ale : Le A) (S:Subset A) : Prop :=
  { total_order_po :> PartialOrder (≤) S
  ; total_order_total :> TotalRelation (≤) S
  }.

Class SubStrictOrder `{Ae : Equiv A} (Alt : Lt A) (S:Subset A) : Prop :=
  { so_subsetoid : SubSetoid S
  ; so_proper  : Proper ((S,=) ==> (S,=) ==> impl) (<)
  ; so_irrefl  :> SubIrreflexive (<) S
  ; so_trans   :> SubTransitive  (<) S
  }.


