(* The standard library's implementation of the integers (BinInt) uses nasty binary positive
  crap with various horrible horrible bit fiddling operations on it (especially Pminus).
  The following is a much simpler implementation whose correctness can be shown much
  more easily. In particular, it lets us use initiality of the natural numbers to prove initiality
  of these integers. *)

Require theory.naturals.
Require Import
 abstract_algebra interfaces.naturals interfaces.integers theory.setoids theory.rings.
Require Import
 stdlib_ring misc.quote.
Require Export
 implementations.semiring_pairs.

Section contents.
Context `{Naturals (N:=N)}.
Add Ring N : (stdlib_semiring_theory N).

Notation Z := (SRpair N).

(* We show that Z is initial, and therefore a model of the integers. *)
Global Instance SRpair_to_ring: IntegersToRing Z :=
  λ _ _ _ _ _ _ _ z, let (a,b) := z in naturals_to_semiring N _ a + - naturals_to_semiring N _ b.

Section for_another_ring.
  Context `{CommutativeRing (R:=R)}.

  Add Ring R : (stdlib_ring_theory R).

  Notation n_to_sr := (naturals_to_semiring N R).
  Notation z_to_r := (integers_to_ring Z R).

  Instance: Morphism (Z ⇒ R) z_to_r.
  Proof. intros [xp xn][yp yn] [[[??][??]]E]. change (xp + yn = yp + xn) in E.
    unfold integers_to_ring, SRpair_to_ring. split. split; apply _.
    apply (equal_by_zero_sum _ _).
    subtransitivity (n_to_sr xp + n_to_sr yn - (n_to_sr xn + n_to_sr yp)). setring R.
    rewrite <- !(R $ preserves_plus (f:=n_to_sr) _ _), (N $ E), (N $ commutativity (+) xn yp).
    exact (plus_negate_r _).
  Qed.

  Ltac derive_preservation :=
    repeat match goal with H : ?x ∊ Z |- _ => destruct x as [??], H as [??] end;
    unfold integers_to_ring, SRpair_to_ring; simpl;
    preserves_simplify (naturals_to_semiring N R); setring R.

  Let preserves_plus x `{x ∊ Z} y `{y ∊ Z}: z_to_r (x + y) = z_to_r x + z_to_r y.
  Proof. derive_preservation. Qed.

  Let preserves_mult x `{x ∊ Z} y `{y ∊ Z}: z_to_r (x * y) = z_to_r x * z_to_r y.
  Proof. derive_preservation. Qed.

  Let preserves_1: z_to_r 1 = 1.
  Proof. derive_preservation. Qed.

  Global Instance: SemiRing_Morphism Z R z_to_r.
  Proof. apply (ring_morphism_alt z_to_r). apply _.
    exact preserves_plus.
    exact preserves_mult.
    exact preserves_1.
  Qed.

  Section for_another_morphism.
    Context (f : Z ⇀ R) `{!SemiRing_Morphism Z R f}.

    Definition g : N ⇀ R := f ∘ cast N Z.

    Instance: SemiRing_Morphism N R g.
    Proof. unfold g. repeat (split; try apply _). exact abstract_algebra.preserves_1. Qed.

    Lemma same_morphism: f = z_to_r.
    Proof.
      intros [p n] z' E. unfold_sigs. split. split; apply _.
      rewrite_on Z <- E. clear dependent z'. pose proof el. destruct el.
      rewrite_on Z -> (SRpair_splits p n).
      preserves_simplify f. preserves_simplify (integers_to_ring Z R).
      now rewrite 2!(R $ naturals.to_semiring_twice z_to_r (cast N Z) g _).
    Qed.
  End for_another_morphism.
End for_another_ring.

Global Instance: Integers Z.
Proof. split; try apply _. intros. now apply same_morphism. Qed.

Context `{!NatDistance N}.

Global Program Instance SRpair_abs: IntAbs Z N := λ x,
  match nat_distance_sig (pos x) (neg x) with
  | inl (exist n p) => inr n
  | inr (exist n p) => inl n
  end.
Next Obligation.
  destruct x as [a b]. match goal with H : _ ∊ Z |- _ => pose proof H; destruct H end.
  simpl in p. destruct (p _ _) as [? E]. clear dependent p. split. apply _.
  rewrite <- (Z $ naturals.to_semiring_unique (cast N Z) _).
  do 2 red. simpl. now rewrite (N $ plus_0_r _), (N $ commutativity (+) n _).
Qed.
Next Obligation.
  destruct x as [a b]. match goal with H : _ ∊ Z |- _ => pose proof H; destruct H end.
  simpl in p. destruct (p _ _) as [? E]. clear dependent p. split. apply _.
  rewrite <- (Z $ naturals.to_semiring_unique (cast N Z) _).
  do 2 red. simpl. now rewrite (N $ plus_0_r _), (N $ commutativity (+) n _).
Qed.

Notation n_to_z := (naturals_to_semiring N Z).

Let zero_product_aux a `{a ∊ N} b `{b ∊ N} :
  n_to_z a * n_to_z b = 0 → n_to_z a = 0 ∨ n_to_z b = 0.
Proof.
  rewrite_on Z <- (preserves_mult (f:=n_to_z) a b).
  rewrite <- !(Z $ naturals.to_semiring_unique (cast N Z) _).
  intro. assert (a*b=0) as E. now apply (injective (cast N Z) _ _).
  destruct (zero_product _ _ E) as [C|C]; [left|right]; rewrite_on N -> C; subreflexivity.
Qed.

Global Instance: ZeroProduct Z.
Proof.
  intros x ? y ? E.
  destruct (SRpair_abs x) as [[a p1]|[a p1]], (SRpair_abs y) as [[b p2]|[b p2]];
  destruct (p1 _) as [? Ea]; destruct (p2 _) as [? Eb]; clear p1; clear p2;
  (destruct (zero_product_aux a b) as [C|C];
    [ rewrite_on Z -> Ea, Eb;
      first [ easy
            | now apply (negate_zero_prod_r x y)
            | now apply (negate_zero_prod_l x y)
            | now rewrite_on Z -> (negate_mult_negate x y) ]
    | left | right ];
    try match goal with E : n_to_z _ = - ?x |- ?x = 0 => apply (flip_negate_0 x) end;
    match goal with E : n_to_z _ = ?x |- ?x = 0 => now rewrite_on Z <- E end
  ).
Qed.
End contents.
