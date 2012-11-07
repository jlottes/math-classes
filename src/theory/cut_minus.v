Require Import
  abstract_algebra interfaces.additional_operations theory.setoids.

Lemma cut_minus_closed `{Setoid (S:=X)} `{CutMinus X} `{Le X} `{Plus X} `{Zero X} `{!CutMinusSpec X _}
  : Closed (X ⇀ X ⇀ X) (∸).
Proof _.
Hint Extern 5 (_ ∸ _ ∊ _) => eapply @cut_minus_closed : typeclass_instances. 

