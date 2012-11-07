Require Import abstract_algebra interfaces.orders.
Require Import theory.strong_setoids theory.fields.

(* Todo: unify with subsetsig somehow *)

Section quote.
  Context {A B} {R1:@Subset A} {R2:@Subset B} (f:R1 ⇀ R2) `{Equiv B}.

  Definition Quote x y := (x ∊ R1 ∧ f x ∊ R2 ∧ y ∊ R2) ∧ f x = y.

  Section setoid.
    Context `{Equiv A} `{!Setoid R1} `{!Setoid R2} `{!Morphism (R1 ⇒ R2) f}.

    Lemma quote_base x `{x ∊ R1} : Quote x (f x).
    Proof. now repeat (split; try apply _). Qed.

    Lemma quote_equiv `{!Injective R1 R2 f} `(Ex : Quote x x2) `(Ey : Quote y y2) : x = y ↔ x2 = y2.
    Proof. destruct Ex as [[?[??]] Ex], Ey as [[?[??]] Ey]. rewrite_on R2 <- Ex, <- Ey. split.
      intro E. now rewrite_on R1 -> E. intro. now apply (injective f). Qed.

    Lemma quote_pred P `{!Proper ((R2,=) ==> iff) P} `(Ex : Quote x x2) : P (f x) ↔ P x2.
    Proof. destruct Ex as [[?[??]] Ex]. now rewrite_on R2 -> Ex. Qed.

  End setoid.

  Section strong_setoid.
    Context `{Equiv A} `{UnEq A} `{UnEq B} `{!StrongSetoid R1} `{!StrongSetoid R2}.
    Context `{!StrongInjective R1 R2 f}.
    Instance: Strong_Morphism R1 R2 f := strong_injective_mor _.

    Lemma quote_uneq `(Ex : Quote x x2) `(Ey : Quote y y2) : x ≠ y ↔ x2 ≠ y2.
    Proof. destruct Ex as [[?[??]] Ex], Ey as [[?[??]] Ey]. rewrite_on R2 <- Ex, <- Ey. split; intro E.
      now apply (strong_injective f _ _). now apply (strong_extensionality f).
    Qed.
  End strong_setoid.

  Ltac quote_tac :=
    repeat match goal with E : Quote _ _ |- _ => destruct E as [[?[??]] E] end;
    split; [ intuition (apply _) |].

  Section semirng.
    Context `{SemiRng_Morphism A B (Be:=_) (R:=R1) (S:=R2) (f:=f)}.

    Existing Instance srngmor_a.
    Existing Instance srngmor_b.

    Lemma quote_0 : Quote 0 0.
    Proof. quote_tac. exact preserves_0. Qed.

    Lemma quote_plus `(Ex : Quote x x2) `(Ey : Quote y y2) : Quote (x+y) (x2+y2).
    Proof. quote_tac. rewrite_on R2 <- Ex, <- Ey. exact (preserves_plus _ _). Qed.

    Lemma quote_mult `(Ex : Quote x x2) `(Ey : Quote y y2) : Quote (x*y) (x2*y2).
    Proof. quote_tac. rewrite_on R2 <- Ex, <- Ey. exact (preserves_mult _ _). Qed.

  End semirng.

  Section semiring.
    Context `{SemiRing_Morphism A B (Be:=_) (R:=R1) (S:=R2) (f:=f)}.

    Existing Instance sringmor_a.
    Existing Instance sringmor_b.

    Lemma quote_1 : Quote 1 1.
    Proof. quote_tac. exact preserves_1. Qed.
  End semiring.

  Section rng.
    Context `{Rng_Morphism A B (Be:=_) (R:=R1) (S:=R2) (f:=f)}.

    Existing Instance rngmor_a.
    Existing Instance rngmor_b.

    Lemma quote_negate `(Ex : Quote x x2) : Quote (-x) (-x2).
    Proof. quote_tac. rewrite_on R2 <- Ex. exact (preserves_negate _). Qed.
  End rng.

  Section field.
    Context `{Field A (F:=R1)} `{Field B (Ae:=_) (F:=R2)}
      `{!Strong_Morphism R1 R2 f} `{!Ring_Morphism R1 R2 f}.

    Lemma quote_mult_inv `{x ∊ R1 ₀} `(Ex : Quote x x2) : Quote (inv x) (inv x2).
    Proof. destruct Ex as [[? [??]] Ex].
      pose proof (_ : f x ∊ R2 ₀).
      assert (x2 ∊ R2 ₀) by now rewrite <- (R2 $ Ex).
      split. intuition (apply _). rewrite <- (R2 ₀ $ Ex).
      exact (preserves_mult_inv _).
    Qed.
  End field.
End quote.

Lemma quote_equiv_id `{Setoid (S:=X)} `(Ex:Quote id x x2) `(Ey:Quote id y y2) : x=y ↔ x2 = y2.
Proof quote_equiv id Ex Ey.

Lemma quote_uneq_id `{StrongSetoid (S:=X)} `(Ex:Quote id x x2) `(Ey:Quote id y y2) : x ≠ y ↔ x2 ≠ y2.
Proof quote_uneq id Ex Ey.

Lemma quote_id `{R1:Subset} `{Setoid (S:=R2)} (f:R1 ⇀ R2)
  `(E:Quote f x y) : Quote id (f x) y.
Proof. destruct E as [[?[??]] E]. split. intuition (apply _). trivial. Qed.

Ltac quote_expr f quote :=
  let rec q expr :=
    match expr with
    | @zero _ _ => constr:(quote_0 f)
    | @one  _ _ => constr:(quote_1 f)
    | @plus _ _  ?x ?y => let qx := q x in let qy := q y in constr:(quote_plus f qx qy)
    | @mult _ _  ?x ?y => let qx := q x in let qy := q y in constr:(quote_mult f qx qy)
    | @negate _ _ ?x => let qx := q x in constr:(quote_negate f qx)
    | @inv    _ _ ?x => let qx := q x in constr:(quote_mult_inv f qx)
    | ?P ?x => match P with
               | @equiv _ _ _ => fail 1
               | @uneq  _ _ _ => fail 1
               | _ => match type of P with _ -> Prop =>
                 let qx := q x in constr:(quote_pred f P qx) end
               end
    | _ => quote expr
    | _ => constr:(quote_base f expr)
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

Ltac quote_inj_expr f :=
  let rec q' expr :=
    let q := quote_expr f q' in
    match expr with
    | @equiv _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_equiv f qx qy)
    | @uneq  _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_uneq  f qx qy)
    | _ => prop_quote q expr
    end
  in quote_expr f q'.

Ltac quote_inj f :=
  match goal with |- ?expr =>
    let E := quote_inj_expr f expr in apply E
  end.

Ltac preserves_simplify_expr f :=
  match type of f with elt_type (?R1 ⇀ ?R2) =>
    let qa expr := fail in
    let rec qb expr :=
      let q := quote_expr (id:R2⇀R2) qb in
      match expr with
      | f ?x => let qfx := quote_expr f qa x in
          constr:(quote_id f qfx)
      | @equiv _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_equiv_id qx qy)
      | @uneq  _ _ ?x ?y => let qx := q x in let qy := q y in constr:(quote_uneq_id  qx qy)
      | _ => prop_quote q expr
      end
    in quote_expr (id:R2⇀R2) qb
  end.

Ltac preserves_simplify f :=
  match goal with |- ?expr =>
    let E := preserves_simplify_expr f expr in
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
