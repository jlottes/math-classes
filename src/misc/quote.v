Require Import abstract_algebra interfaces.orders.
Require Import theory.subsetoids theory.rings.

(* Todo: unify with subsetsig somehow *)

Section quote.
  Context `(f:A → B) (R1:Subset A) (R2:Subset B) `{Equiv B}.

  Definition Quote x y := (x ∊ R1 ∧ y ∊ R2) ∧ f x = y.

  Section subsetoid.
    Context `{Equiv A} `{!SubSetoid_Morphism f R1 R2}.
    Existing Instance subsetoidmor_s.
    Existing Instance subsetoidmor_t.

    Lemma quote_base x `{x ∊ R1} : Quote x (f x).
    Proof. now repeat (split; try apply _). Qed.

    Lemma quote_equiv `{!Injective f R1 R2} `(Ex : Quote x x2) `(Ey : Quote y y2) : x = y ↔ x2 = y2.
    Proof. destruct Ex as [[??] Ex], Ey as [[??] Ey]. rewrite <- Ex, <- Ey. split.
      intro E. now rewrite_on R1 -> E. intro. now apply (injective f). Qed.

    Lemma quote_pred P `{!Proper ((R2,=) ==> iff) P} `(Ex : Quote x x2) : P (f x) ↔ P x2.
    Proof. destruct Ex as [[??] Ex]. now rewrite_on R2 -> Ex. Qed.

  End subsetoid.


  Section semirng.
    Context `{SemiRng_Morphism A B (Be:=_) (f:=f) (R:=R1) (S:=R2)}.

    Existing Instance srngmor_a.
    Existing Instance srngmor_b.

    Lemma quote_0 : Quote 0 0.
    Proof. split. split; apply _. exact preserves_0. Qed.

    Lemma quote_plus `(Ex : Quote x x2) `(Ey : Quote y y2) : Quote (x+y) (x2+y2).
    Proof. destruct Ex as [[??] Ex], Ey as [[??] Ey]. split. split; apply _.
      rewrite_on R2 <- Ex. rewrite_on R2 <- Ey. exact (preserves_plus _ _). Qed.

    Lemma quote_mult `(Ex : Quote x x2) `(Ey : Quote y y2) : Quote (x*y) (x2*y2).
    Proof. destruct Ex as [[??] Ex], Ey as [[??] Ey]. split. split; apply _.
      rewrite_on R2 <- Ex. rewrite_on R2 <- Ey. exact (preserves_mult _ _). Qed.

  End semirng.

  Section semiring.
    Context `{SemiRing_Morphism A B (Be:=_) (f:=f) (R:=R1) (S:=R2)}.

    Existing Instance sringmor_a.
    Existing Instance sringmor_b.

    Lemma quote_1 : Quote 1 1.
    Proof. split. split; apply _. exact preserves_1. Qed.
  End semiring.

  Section rng.
    Context `{Rng_Morphism A B (Be:=_) (f:=f) (R:=R1) (S:=R2)}.

    Existing Instance rngmor_a.
    Existing Instance rngmor_b.

    Lemma quote_negate `(Ex : Quote x x2) : Quote (-x) (-x2).
    Proof. destruct Ex as [[??] Ex]. split. split; apply _.
      rewrite_on R2 <- Ex. exact (preserves_negate _). Qed.
  End rng.

End quote.

Lemma quote_equiv_id `{SubSetoid (S:=X)} `(Ex:Quote id X X x x2) `(Ey:Quote id X X y y2) : x=y ↔ x2 = y2.
Proof. destruct Ex as [[??] Ex], Ey as [[??] Ey]. unfold id in Ex, Ey. now rewrite Ex, Ey. Qed.

Lemma quote_id `(f:A->B) (R1:Subset A) (R2:Subset B) `{Equiv B} `{!SubSetoid R2}
  `(E:Quote f R1 R2 x y) : Quote id R2 R2 (f x) y.
Proof. destruct E as [[??] E]. split. split.  now rewrite E. trivial. trivial. Qed.

Ltac quote_expr f R1 R2 quote :=
  let rec q expr :=
    match expr with
    | @zero _ _ => constr:(quote_0 f R1 R2)
    | @one  _ _ => constr:(quote_1 f R1 R2)
    | @plus _ _  ?x ?y => let qx := q x in let qy := q y in constr:(quote_plus f R1 R2 qx qy)
    | @mult _ _  ?x ?y => let qx := q x in let qy := q y in constr:(quote_mult f R1 R2 qx qy)
    | @negate _ _  ?x => let qx := q x in constr:(quote_negate f R1 R2 qx)
    | ?P ?x => match P with @equiv _ _ _ => fail 1
               | _ => match type of P with _ -> Prop =>
                 let qx := q x in constr:(quote_pred f R1 R2 P qx) end
               end
    | _ => quote expr
    | _ => constr:(quote_base f R1 R2 expr)
    end
  in q.

Lemma prop_quote_base P : P ↔ P. Proof. tauto. Qed.
Lemma quote_iff  `(Ex : x ↔ x2) `(Ey : y ↔ y2) : (x ↔ y) ↔ (x2 ↔ y2). Proof (_:Proper (iff==>iff==>iff) iff ) _ _ Ex _ _ Ey.
Lemma quote_impl `(Ex : x ↔ x2) `(Ey : y ↔ y2) : (x → y) ↔ (x2 → y2). Proof (_:Proper (iff==>iff==>iff) impl) _ _ Ex _ _ Ey.
Lemma quote_and  `(Ex : x ↔ x2) `(Ey : y ↔ y2) : (x ∧ y) ↔ (x2 ∧ y2). Proof (_:Proper (iff==>iff==>iff) and ) _ _ Ex _ _ Ey.
Lemma quote_or   `(Ex : x ↔ x2) `(Ey : y ↔ y2) : (x ∨ y) ↔ (x2 ∨ y2). Proof (_:Proper (iff==>iff==>iff) or  ) _ _ Ex _ _ Ey.
Lemma quote_not  `(Ex : x ↔ x2)                :   (¬ x) ↔ (¬ x2).    Proof (_:Proper (iff==>iff)       not ) _ _ Ex.

Ltac prop_quote q expr :=
  match type of expr with Prop => 
    match expr with
    | ¬ ?x    => let qx := q x in constr:(quote_not qx)
    | ?x ↔ ?y => let qx := q x in let qy := q y in constr:(quote_iff  qx qy)
    | ?x → ?y => let qx := q x in let qy := q y in constr:(quote_impl qx qy)
    | ?x ∧ ?y => let qx := q x in let qy := q y in constr:(quote_and  qx qy)
    | ?x ∨ ?y => let qx := q x in let qy := q y in constr:(quote_or   qx qy)
    | _ => constr:(prop_quote_base expr)
    end
  end.

Ltac quote_inj_expr f R1 R2 :=
  let rec q' expr :=
    let q := quote_expr f R1 R2 q' in
    match expr with
    | @equiv _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_equiv f R1 R2 qx qy)
    | _ => prop_quote q expr
    end
  in quote_expr f R1 R2 q'.

Ltac quote_inj f R1 R2 :=
  match goal with |- ?expr =>
    let E := quote_inj_expr f R1 R2 expr in apply E
  end.

Ltac preserves_simplify_expr f R1 R2 :=
  match type of f with ?A -> ?B =>
    let qa expr := fail in
    let rec qb expr :=
      let q := quote_expr (@id B) R2 R2 qb in
      match expr with
      | f ?x => let qfx := quote_expr f R1 R2 qa x in
          constr:(quote_id f R1 R2 qfx)
      | @equiv _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_equiv_id qx qy)
      | _ => prop_quote q expr
      end
    in quote_expr (@id B) R2 R2 qb
  end.

Ltac preserves_simplify f R1 R2 :=
  match goal with |- ?expr =>
    let E := preserves_simplify_expr f R1 R2 expr in
    apply E; unfold id
  end.

(*
Section test.

  Context `{Ring (R:=R1)} `{Ring (R:=R2)} `{!Ring_Morphism f R1 R2}.

  Context `{a ∊ R1} `{b ∊ R1} `{c ∊ R1} `{x ∊ R2} `{y ∊ R2} `{z ∊ R2}.

  Goal x * f (a + b*c + 0*1) = y -> f (a *b) = f 0.
  preserves_simplify f R1 R2.
  Abort.

  Context `{!Injective f R1 R2}.

  Goal a * b + c = 0.
  quote_inj f R1 R2.

End test.
*)
