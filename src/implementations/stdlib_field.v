Require Import
  Ring Field abstract_algebra dn_point theory.fields.

Section semiring_ops.
  Context `(R:set) `{H:CommutativeSemiRing _ (R:=R)}.

  Instance stdlib_field_setoid : Setoid R := _.
  Instance stdlib_field_zero_closed : 0 ∊ R := _.
  Instance stdlib_field_one_closed  : 1 ∊ R := _.
  Instance stdlib_field_plus_proper : Morphism (R⇒R⇒R) (+) := _.
  Instance stdlib_field_mult_proper : Morphism (R⇒R⇒R) (.*.) := _.
End semiring_ops.

Hint Extern 2 (Zero (Point ?R)) => eapply (point_zero R (pfs:=stdlib_field_setoid R) (pf:=stdlib_field_zero_closed R)) : typeclass_instances.
Hint Extern 2 (One  (Point ?R)) => eapply (point_one  R (pfs:=stdlib_field_setoid R) (pf:=stdlib_field_one_closed  R)) : typeclass_instances.
Hint Extern 2 (Plus (Point ?R)) => eapply (point_plus R (pfs:=stdlib_field_setoid R) (pf:=stdlib_field_plus_proper R)) : typeclass_instances.
Hint Extern 2 (Mult (Point ?R)) => eapply (point_mult R (pfs:=stdlib_field_setoid R) (pf:=stdlib_field_mult_proper R)) : typeclass_instances.

Section semiring.
  Context `(R:set) `{CommutativeSemiRing _ (R:=R)}.

  Notation R' := (every (Point R)).

  Instance: CommutativeSemiRing R' := point_comsemiring R _ _ _ _ _.

  Lemma point_stdlib_semiring_theory : Ring_theory.semi_ring_theory (R:=Point R) 0 1 (+) (.*.) (=).
  Proof.
   constructor; intros.
   exact (plus_0_l _).
   exact (commutativity (+) _ _).
   exact (associativity (+) _ _ _).
   exact (mult_1_l _).
   exact (mult_0_l _).
   exact (commutativity (.*.) _ _).
   exact (associativity (.*.) _ _ _).
   exact (plus_mult_distr_r _ _ _).
  Qed.

End semiring.

Section ring_ops.
  Context `(R:set) `{H:CommutativeRing _ (R:=R)}.

  Instance stdlib_field_negate_proper : Morphism (R⇒R) (-) := _.
End ring_ops.

Hint Extern 2 (Negate (Point ?R)) => eapply (point_negate R (pfs:=stdlib_field_setoid R) (pf:=stdlib_field_negate_proper R)) : typeclass_instances.

Section ring.
  Context `(R:set) `{CommutativeRing _ (R:=R)}.

  Notation R' := (every (Point R)).

  Instance: CommutativeRing R' := point_comring R _ _ _ _ _ _.

  Lemma point_stdlib_ring_theory :
    Ring_theory.ring_theory (R:=Point R) 0 1 (+) (.*.) (λ x y, x - y) (-) (=).
  Proof.
   constructor; intros.
   exact (plus_0_l _).
   exact (commutativity (+) _ _).
   exact (associativity (+) _ _ _).
   exact (mult_1_l x).
   exact (commutativity (.*.) _ _).
   exact (associativity (.*.) _ _ _).
   exact (plus_mult_distr_r _ _ _).
   reflexivity.
   exact (plus_negate_r _).
  Qed.

End ring.

Ltac point_stdlib_semiring_quote R := 
  let H1 := constr:(_ : CommutativeSemiRing R) in
  let s  := constr:(stdlib_field_setoid R (H:=H1)) in
  let zc := constr:(stdlib_field_zero_closed R (H:=H1)) in
  let oc := constr:(stdlib_field_one_closed R (H:=H1)) in
  let pp := constr:(stdlib_field_plus_proper R (H:=H1)) in
  let mp := constr:(stdlib_field_mult_proper R (H:=H1)) in
  point_quote R s s zc oc pp mp zc zc.

Ltac point_stdlib_ring_quote R := 
  let H1 := constr:(_ : CommutativeSemiRing R) in
  let H2 := constr:(_ : CommutativeRing R) in
  let s  := constr:(stdlib_field_setoid R (H:=H1)) in
  let zc := constr:(stdlib_field_zero_closed R (H:=H1)) in
  let oc := constr:(stdlib_field_one_closed R (H:=H1)) in
  let pp := constr:(stdlib_field_plus_proper R (H:=H1)) in
  let mp := constr:(stdlib_field_mult_proper R (H:=H1)) in
  let np := constr:(stdlib_field_negate_proper R (H:=H2)) in
  point_quote R s s zc oc pp mp np zc.

Ltac setfring R := first [
    let q := point_stdlib_ring_quote R in point_quote_equiv R q
  | let q := point_stdlib_semiring_quote R in point_quote_equiv R q
  ]; ring.

(*
Section test.

  Context `{CommutativeSemiRing (R:=R)}.
  Context `{∀ `{x ∊ R} `{y ∊ R}, Stable (x=y)}.

  Add Ring R : (point_stdlib_semiring_theory R).

  Goal ∀ x `{x ∊ R} y `{y ∊ R}, x*y=y*x.
  Proof. intros. setfring R. Qed.

End test.
*)

(*
Section test.

  Context `{CommutativeRing (R:=R)}.
  Context `{∀ `{x ∊ R} `{y ∊ R}, Stable (x=y)}.

  Add Ring R : (point_stdlib_ring_theory R).

  Goal forall x `{x ∊ R} y `{y ∊ R}, (x-x)*y=0.
  Proof. intros. setfring R. Qed.

End test.
*)

Section field_ops.
  Context `(F:set) `{H:Field _ (F:=F)}.

  Instance stdlib_field_strong_setoid : StrongSetoid F := _.
  Instance stdlib_field_inv_proper : Morphism (F ₀ ⇒ F ₀) inv := _.
End field_ops.

Hint Extern 2 (Inv (Point ?F)) => eapply (point_mult_inv F
  (pfs:=stdlib_field_strong_setoid F)
  (pf0:=stdlib_field_zero_closed F)
  (pfi:=stdlib_field_inv_proper F)) : typeclass_instances.

Section field.
  Context `(F:set) `{Field _ (F:=F)}.

  Notation F' := (every (Point F)).

  Lemma stdlib_field_theory :
    Field_theory.field_theory (R:=Point F) 0 1 (+) (.*.) (λ x y, x - y) (-)
                              (λ x y, x / y) inv (=).
  Proof. split.
  + exact (point_stdlib_ring_theory F).
  + exact (point_field_nontrivial F _ _ _ _).
  + intros. reflexivity.
  + now apply point_field_inv_l.
  Qed.

End field.

Ltac stdlib_field_quote F := 
  let H1 := constr:(_ : CommutativeSemiRing F) in
  let H2 := constr:(_ : CommutativeRing F) in
  let H3 := constr:(_ : Field F) in
  let s  := constr:(stdlib_field_setoid F (H:=H1)) in
  let ss := constr:(stdlib_field_strong_setoid F (H:=H3)) in
  let zc := constr:(stdlib_field_zero_closed F (H:=H1)) in
  let oc := constr:(stdlib_field_one_closed F (H:=H1)) in
  let pp := constr:(stdlib_field_plus_proper F (H:=H1)) in
  let mp := constr:(stdlib_field_mult_proper F (H:=H1)) in
  let np := constr:(stdlib_field_negate_proper F (H:=H2)) in
  let ip := constr:(stdlib_field_inv_proper F (H:=H3)) in
  point_quote F s ss zc oc pp mp np ip.

Ltac stdlib_field_quote_clean F :=
    let e0 := eval unfold zero in (@zero F _) in
    let e1 := eval unfold one in (@one F _) in
    let ep := eval unfold plus in (@plus F _) in
    let em := eval unfold mult in (@mult F _) in
    let en := eval unfold negate in (@negate F _) in
    repeat match goal with
    | |- context f [ exist _ _ (point_obl e0) ] =>
        let e := constr:(@zero (Point F) _) in
        let q := context f[e] in change q
    | |- context f [ exist _ _ (point_obl e1) ] =>
        let e := constr:(@one (Point F) _) in
        let q := context f[e] in change q
    | |- context f [ exist _ _ (point_map_binary_obl ep ?a ?b) ] =>
         let e := constr:(@plus (Point F) _ a b) in
         let q := context f[e] in change q
    | |- context f [ exist _ _ (point_map_binary_obl em ?a ?b) ] =>
         let e := constr:(@mult (Point F) _ a b) in
         let q := context f[e] in change q
    | |- context f [ exist _ _ (point_map_obl en ?a) ] =>
         let e := constr:(@negate (Point F) _ a) in
         let q := context f[e] in change q
    end.

Ltac stdlib_field_quote_nonzero F :=
    match goal with |- not (?px = 0) =>
      let k q := 
        match type of q with Point_Quote _ ?x ?px =>
          cut (x ∊ F ₀); [ intro; 
            exact (point_nonzero F _ _ _ x px q)
          |]
        end
      in stdlib_field_quote F px k
    end.

Ltac setfield F := 
    let q := stdlib_field_quote F in point_quote_equiv F q;
    [ field;
      stdlib_field_quote_clean F;
      repeat match goal with |- and ?a ?b => split end;
      try stdlib_field_quote_nonzero F
    |..]; try apply _.
(*
Require Import interfaces.orders orders.fields.

Section test.

  Context `{Field (F:=F)}.
  Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder F}.

  Add Field F : (stdlib_field_theory F).

  Goal forall x `{x ∊ F} y `{y ∊ F}, (x-x)*y=0.
  Proof. intros. setfring F. Qed.

  Instance : 2 + 0 ∊ F ₀ .
  Proof. apply (_ : Subset F₊ (F ₀)). apply _. Qed.

  Goal forall x `{x ∊ F ₀}, 2*x/4 + 2*x/4 = (-3)/(-3) * (x/x) * x.
  Proof. intros. setfield F. Qed.

End test.
*)
