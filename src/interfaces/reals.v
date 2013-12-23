Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_fields.

Class ToReals `(R:set)
  := to_reals: ∀ `{F:set} `{Equiv F} `{Le F} `{Mult F} `{Plus F} `{One F} `{Zero F} `{Negate F} `{Inv F}, F ⇀ R.
Arguments to_reals {_} R {ToReals _} F {_ _ _ _ _ _ _ _} _.
Instance: Params (@to_reals) 13.

Section definition.
  Context `(R:set) `{ArchimedeanField _ (F:=R)}.

  Local Notation f := (to_reals _ _).

  Class Reals {U:ToReals R} : Prop :=
  { reals_arch_field :>> ArchimedeanField R
  ; to_reals_mor       `{ArchimedeanField (F:=F)} : SemiRing_Morphism    F R f
  ; to_reals_embedding `{ArchimedeanField (F:=F)} : StrictOrderEmbedding F R f
  ; to_reals_terminal  `{ArchimedeanField (F:=F)}
      (g:F ⇀ R) `{!SemiRing_Morphism F R g} `{!StrictOrderEmbedding F R g} : g = f
  }.
End definition.

Hint Extern 2 (SemiRing_Morphism    _ _ (to_reals _ _)) => eapply @to_reals_mor : typeclass_instances.
Hint Extern 2 (StrictOrderEmbedding _ _ (to_reals _ _)) => eapply @to_reals_embedding : typeclass_instances.

(* The following class allows a specified reals instance to be referenced implicitly *)
Class TheReals {A} := thereals : @set A.
Identity Coercion Id_TheReals_Subset : TheReals >-> set.

Ltac reals_of_type A := let H := constr:(@thereals A _) in eval unfold thereals in H.
Ltac ensure_reals R :=
  match type of R with @set ?A =>
    let H := constr:(_ : @TheReals A) in unify H R
  end.
