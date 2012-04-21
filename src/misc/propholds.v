Require Import
  canonical_names.

(*
  The following class is nice to parametrize instances by additional properties, for example:
  [∀ z, PropHolds (z ≠ 0) → LeftCancellation op z]
  This tool is very powerful as we can combine it with instances as:
  [∀ x y, PropHolds (x ≠ 0) → PropHolds (y ≠ 0) → PropHolds (x * y ≠ 0)]
  Of course, one should be very careful not to make too many instances as that could
  easily lead to a blow-up of the search space (or worse, cycles).
*)
Class PropHolds (P : Prop) := prop_holds: P.

Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.

Instance: Proper (iff ==> iff) PropHolds.
Proof. now repeat intro. Qed.

Ltac solve_propholds :=
  match goal with
  | [ |- PropHolds (?P) ] => apply _
  | [ |- ?P ] => change (PropHolds P); apply _
  end.

Ltac mc_contradict H :=
  match goal with
  |- PropHolds ?P => unfold PropHolds
  | _ => idtac
  end;
  match type of H with
  | PropHolds ?P => unfold PropHolds in H
  | _ => idtac
  end;
  contradict H.
