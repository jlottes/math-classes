Require Import canonical_names restrict_rel.

(** A database of declared signatures of functions, associated with the head.
    [S] should be [∀ a b ..., Proper R (f x y ...)].
    More than one signature can be declared per head.
    The first instance tried has [i=0], the second has [i=1], etc.

    It is important that the signature is declared using something like

    [Hint Extern 0 (Find_Proper_Signature (@f) 0 _) => eexact f_proper : typeclass_instances]

    as otherwise any term convertible with @f will be found.
    (For example, @mult, @plus, and @sg_op are all convertible).
 *)

Class Find_Proper_Signature {T} (head:T) (i:nat) S := find_proper_sig : S.
Arguments find_proper_sig {T head i S} Find_Proper_Signature.

Ltac find_proper_count_aux i h :=
  match i with
  | _ => let s := constr:(_:Find_Proper_Signature h i _ _) in
         find_proper_count_aux (S i) h
  | _ => i
  end.
Ltac find_proper_count h := find_proper_count_aux O h.


(* The following idiom can be used to add instances to the db
   when we don't know how many have already been added.
   ( haven't needed this yet; how to use Hint Extern instead? )
*)

(*
Section inst1.
Let c : nat. let c:= find_proper_count (@Peano.plus) in exact c. Defined.
Print c.
Definition blah : Find_Proper_Signature (@Peano.plus) c O O (Proper (eq==>eq==>eq) (@Peano.plus)).
Proof. firstorder. Qed.
End inst1.
Existing Instance blah.

Section inst2.
Let c : nat. let c:= find_proper_count (@Peano.plus) in exact c. Defined.
Print c.
Definition blah2 : Find_Proper_Signature (@Peano.plus) c O O (Proper (eq-->eq-->eq) (@Peano.plus)).
Proof. firstorder. Qed.
End inst2.
Existing Instance blah2.

Check (_:Find_Proper_Signature (@Peano.plus) 0%nat _ _ _).
Check (_:Find_Proper_Signature (@Peano.plus) 1%nat _ _ _).
*)

(** To deal with partial applications, the tactic needs to synthesize
    reflexivity statements. We use the following copies of Proper and Reflexive
    for this. The redundancy is to keep tight control over the search size. *)

Class Find_Proper_Proper {A} (R:relation A) (x:A) := find_proper_proper : R x x.
Arguments Find_Proper_Proper {A}%type R%signature x.

Class Find_Proper_Reflexive {A} (R:relation A) := find_proper_refl x
  :> Find_Proper_Proper R x.


(** Next we exploit any of the following declared relationships between
    relations to convert a declared signature to the one being sought.
*)

Class Find_Proper_Symmetric {A} (R:relation A) := find_proper_sym : Symmetric R.
Class Find_Proper_Subrelation {A} (R1 R2:relation A) := find_proper_sub : subrelation R1 R2.

Class Find_Proper_PrePartialOrder {A} (eq le: relation A) :=
  { find_proper_pporder_sym     :> Find_Proper_Symmetric eq
  ; find_proper_pporder_sub     :> Find_Proper_Subrelation eq le
  ; find_proper_antisym         : AntiSymmetricT eq le
  }.

(** A starting set of instances of the above properties. *)


Instance: ∀ A, Find_Proper_Reflexive (@eq A). Proof. firstorder. Qed.
Instance: ∀ A (R:relation A) `{!Find_Proper_Reflexive R}, Find_Proper_Subrelation eq R.
Proof. intros ??? ?? E. rewrite E. apply find_proper_refl. Qed.
Instance: Find_Proper_Reflexive impl. Proof. firstorder. Qed.
Instance: Find_Proper_Reflexive iff. Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_Reflexive (@subrelation A). Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_Reflexive (@relation_equivalence A). Proof. firstorder. Qed.


Instance: ∀ A, Find_Proper_Symmetric (@eq A). Proof. firstorder. Qed.
Instance: Find_Proper_PrePartialOrder iff impl. Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_PrePartialOrder (relation_equivalence) (@subrelation A).
Proof. intro. split; try apply _; firstorder. Qed.


(** The restriction of a relation to some subset ([restrict_rel]) is used ubiquitously.
    Apart from reflexivity, all of the above properties lift to restricted relations. *)

Lemma restrict_rel_sub_fp `(S:A → Prop) (R:relation A): Find_Proper_Subrelation (restrict_rel S R)%signature R.  Proof restrict_rel_sub S R.
Lemma restrict_rel_sym_fp `(S:A → Prop) (R:relation A) {sym:Find_Proper_Symmetric R}: Find_Proper_Symmetric (restrict_rel S R). Proof @restrict_rel_sym _ S R sym.
Hint Extern 0 (@Find_Proper_Subrelation _ (@restrict_rel _ _ ?R) ?R) => eapply @restrict_rel_sub_fp : typeclass_instances.
Hint Extern 4 (@Find_Proper_Symmetric _ (@restrict_rel _ _ _)) => eapply @restrict_rel_sym_fp : typeclass_instances.

Lemma restrict_sub_sub_fp `(S:A → Prop) (R1 R2:relation A) {sub:Find_Proper_Subrelation R1 R2}
  : Find_Proper_Subrelation (restrict_rel S R1) (restrict_rel S R2).
Proof restrict_sub_sub S R1 R2 (sub:=sub).

(* Hint Extern 4 (@Find_Proper_Subrelation  _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_sub_sub_fp : typeclass_instances. *)

Lemma restrict_ppo_fp `(S:A → Prop) (eq le:relation A) `{!Find_Proper_PrePartialOrder eq le}
  : Find_Proper_PrePartialOrder (restrict_rel S eq) (restrict_rel S le).
Proof. pose proof (find_proper_antisym (eq:=eq)). split. apply _.
  apply restrict_sub_sub_fp. apply _. now apply restrict_antisym.
Qed.

(*Hint Extern 2 (@Find_Proper_PrePartialOrder _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_ppo_fp : typeclass_instances.*)

(** The tactic for partial applications, which uses reflexivity. *)

Lemma cut_proper_refl `{R:relation A} x `{!Find_Proper_Proper R x} `{R':relation B} {f}
  (p:Proper (R==>R') f) : Proper R' (f x).
Proof p _ _ find_proper_proper.

Lemma cut_proper_refl_flip `{R:relation A} x `{!Find_Proper_Proper R x} `{R':relation B} {f}
  (p:Proper (R-->R') f) : Proper R' (f x).
Proof p _ _ (find_proper_proper (R:=R)).

Ltac cut_proper p x :=
  match type of p with | Proper (?R --> _) _ => constr:(cut_proper_refl_flip x p)
                       | Proper (?R ==> _) _ => constr:(cut_proper_refl x p)
  end.

Ltac trim_proper n p expr :=
  match n with
  | O => p
  | S ?m => match expr with ?f ?x => 
              let p' := trim_proper m p f in
              cut_proper p' x
            end
  end.

(** The tactic for converting one signature to another. *)

Lemma chain_conv {A B} {R1 S1 : relation A} {R2 S2 : relation B}
  (c1 : ∀ x y, S1 x y → R1 x y)
  (c2 : ∀ f g, R2 f g → S2 f g)
  f g : (R1++>R2)%signature f g → (S1++>S2)%signature f g.
Proof. intros P ???. now apply c2, P, c1. Qed.

Lemma chain_invert_conv {A B} {R1 S1 : relation A} {R2 S2 : relation B}
  (c1 : ∀ x y, S1 y x → R1 x y)
  (c2 : ∀ f g, R2 g f → S2 f g)
  f g : (R1++>R2)%signature g f → (S1++>S2)%signature f g.
Proof. intros P ???. now apply c2, P, c1. Qed.

Lemma chain_join_conv {A B} {R1 S1 : relation A} {R2 S2 : relation B}
  (c1 : ∀ x y, S1 x y → R1 x y ∧ R1 y x)
  (c2 : ∀ f g, R2 f g ∧ R2 g f → S2 f g)
  f g :   (R1++>R2)%signature f g
        ∧ (R1++>R2)%signature g f
        → (S1++>S2)%signature f g.
Proof. intros [P1 P2] x y E. destruct (c1 x y E).
 apply c2; split; [ apply P1 | apply P2]; assumption.
Qed.

Definition id_conv `(R:relation A) x y : R x y → R x y := id.
Definition sub_conv {A} (R S:relation A) `{!Find_Proper_Subrelation R S} : ∀ x y, R x y → S x y := find_proper_sub.
Definition sub_conv_ff {A} (R S:relation A) `{!Find_Proper_Subrelation R S} : ∀ x y, (flip R) x y → (flip S) x y.
Proof. unfold flip. intros. now apply find_proper_sub. Defined.
Definition sub_conv_f2 {A} (R S:relation A) `{!Find_Proper_Symmetric R} `{!Find_Proper_Subrelation R S}
  : ∀ x y, R x y → (flip S) x y.
Proof. unfold flip. intros. now apply find_proper_sub, find_proper_sym. Defined.

Ltac find_conv R S :=
  match constr:(pair R S) with
  | _                          => constr:(id_conv S         : ∀ x y, R x y → S x y)
  | pair (flip ?R') (flip ?S') => constr:(sub_conv_ff R' S' : ∀ x y, R x y → S x y)
  | pair _          (flip ?S') => constr:(sub_conv_f2 R  S' : ∀ x y, R x y → S x y)
  | _                          => constr:(sub_conv    R  S  : ∀ x y, R x y → S x y)
  end.

(*
Goal True.
let c := find_conv (iff) (flip impl) in idtac c.
evar (R:relation Prop).
let R' := eval unfold R in R in
let c := find_conv R' (flip impl) in idtac c.
Abort.
*)

Definition id_flip_conv1 `(R:relation A) x y : R y x → (flip R) x y := id.
Definition id_flip_conv2 `(R:relation A) x y : (flip R) y x → R x y := id.
Definition sym_conv `(R:relation A) `{!Find_Proper_Symmetric R} : ∀ x y, R y x → R x y := λ x y, find_proper_sym y x.
Definition sub_inv_conv_f2 {A} (R S:relation A) `{!Find_Proper_Subrelation R S}  : ∀ x y, R y x → (flip S) x y.
Proof. unfold flip. intros. now apply find_proper_sub. Defined.
Definition sub_conv_f1 {A} (R S:relation A) `{!Find_Proper_Subrelation R S} : ∀ x y, (flip R) y x → S x y.
Proof. unfold flip. intros. now apply find_proper_sub. Defined.
Definition sym_sub_conv {A} (R S:relation A) `{!Find_Proper_Symmetric R} `{!Find_Proper_Subrelation R S}
  : ∀ x y, R y x → S x y.
Proof. intros. now apply find_proper_sub, find_proper_sym. Defined.

Ltac find_inv_conv R S :=
  match constr:(pair R S) with
  | _                 => constr:(sym_conv S           : ∀ x y, R y x → S x y)
  | pair _ (flip ?S') => constr:(id_flip_conv1 S'     : ∀ x y, R y x → S x y)
  | _                 => constr:(id_flip_conv2 S      : ∀ x y, R y x → S x y)
  | pair _ (flip ?S') => constr:(sub_inv_conv_f2 R S' : ∀ x y, R y x → S x y)
  | pair (flip ?R') _ => constr:(sub_conv_f1 R' S     : ∀ x y, R y x → S x y)
  | _                 => constr:(sym_sub_conv R S     : ∀ x y, R y x → S x y)
  end.

Ltac find_inv_conv_2 R S k :=
  match S with
  | _ => is_evar S; first [ let c :=
    match R with
    | flip ?R' => constr:(id_flip_conv2 R')
    | _ => constr:(id_flip_conv1 R)
    end in k c | fail 2 ]
  | _ => let c := find_inv_conv R S in k c
  end.

(*
Goal True.
let c := find_inv_conv (iff) (impl) in idtac c.
evar (R:relation Prop).
let R' := eval unfold R in R in
let c := find_inv_conv R' (impl) in idtac c.
Abort.
*)

Definition sym_split `(R:relation A) `{!Find_Proper_Symmetric R} : ∀ x y, R x y → R x y ∧ R y x.
Proof. intros. split. assumption. now apply find_proper_sym. Defined.
Definition sym_sub_split_f {A} (R S:relation A) `{!Find_Proper_Symmetric R} `{!Find_Proper_Subrelation R S}
  : ∀ x y, R x y → (flip S) x y ∧ (flip S) y x.
Proof. intros. unfold flip. split; apply find_proper_sub. now apply find_proper_sym. assumption. Defined.
Definition sym_sub_split {A} (R S:relation A) `{!Find_Proper_Symmetric R} `{!Find_Proper_Subrelation R S}
  : ∀ x y, R x y → S x y ∧ S y x.
Proof. intros. split; apply find_proper_sub. assumption. now apply find_proper_sym. Defined.

Ltac find_split_conv R S :=
  match constr:(pair R S) with
  | _                 => constr:(sym_split S          : ∀ x y, R x y → S x y ∧ S y x)
  | pair _ (flip ?S') => constr:(sym_sub_split_f R S' : ∀ x y, R x y → S x y ∧ S y x)
  | _                 => constr:(sym_sub_split R S    : ∀ x y, R x y → S x y ∧ S y x)
  end.

(*
Goal True.
let c := find_split_conv (iff) (flip impl) in idtac c.
evar (R:relation Prop).
let R' := eval unfold R in R in
let c := find_split_conv R' (flip impl) in idtac c.
Abort.
*)

Definition id_join1 `(R:relation A) : ∀ x y, R x y ∧ R y x → R x y. Proof. tauto. Defined.
Definition id_join2 `(R:relation A) : ∀ x y, R y x ∧ R x y → R x y. Proof. tauto. Defined.
Definition ppo_join_f  {A} (R S:relation A) `{!Find_Proper_PrePartialOrder R S}
  : ∀ x y, (flip S) x y ∧ (flip S) y x → R x y.
Proof. unfold flip. intros ?? [??]. now apply find_proper_antisym. Defined.
Definition ppo_join {A} (R S:relation A) `{!Find_Proper_PrePartialOrder R S}
  : ∀ x y, S x y ∧ S y x → R x y.
Proof. intros ?? [??]. now apply find_proper_antisym. Defined.
Definition ppo_sub_join_f  {A} {eq:relation A} (R S:relation A) `{!Find_Proper_PrePartialOrder eq R}
  `{!Find_Proper_Subrelation eq S}
  : ∀ x y, (flip R) x y ∧ (flip R) y x → S x y.
Proof. unfold flip. intros ?? [??]. now apply find_proper_sub, find_proper_antisym. Defined.
Definition ppo_sub_join  {A} {eq:relation A} (R S:relation A) `{!Find_Proper_PrePartialOrder eq R}
  `{!Find_Proper_Subrelation eq S}
  : ∀ x y, R x y ∧ R y x → S x y.
Proof. intros ?? [??]. now apply find_proper_sub, find_proper_antisym. Defined.

Ltac find_join_conv R S :=
  match constr:(pair R S) with
  | _                 => constr:(id_join1 S           : ∀ x y, R x y ∧ R y x → S x y)
  | _                 => constr:(id_join2 S           : ∀ x y, R x y ∧ R y x → S x y)
  | pair (flip ?R') _ => constr:(ppo_join_f S R'      : ∀ x y, R x y ∧ R y x → S x y)
  | pair (flip ?R') _ => constr:(ppo_sub_join_f R' S  : ∀ x y, R x y ∧ R y x → S x y)
  | _                 => constr:(ppo_join S R         : ∀ x y, R x y ∧ R y x → S x y)
  | _                 => constr:(ppo_sub_join R S     : ∀ x y, R x y ∧ R y x → S x y)
  end.

(*
Goal True.
let c := find_join_conv (flip impl) (iff) in idtac c.
Abort.
*)

Ltac build_chain_conv R S k :=
  match constr:(pair R S) with
  | pair (?R1++>?R2)%signature (?S1++>?S2)%signature => first [
      let c1 := find_conv S1 R1 in
      let with_c2 c2 :=
        let c := constr:(chain_conv c1 c2) in k c
      in build_chain_conv R2 S2 with_c2
    | fail 2 ]
  | _ => let c := find_conv R S in k c
  end.

Ltac build_chain_inv_conv R S k :=
  match constr:(pair R S) with
  | pair (?R1++>?R2)%signature (?S1++>?S2)%signature => first [
      let c1 := find_inv_conv S1 R1 in
      let with_c2 c2 :=
        let c := constr:(chain_invert_conv c1 c2) in k c
      in build_chain_inv_conv R2 S2 with_c2
    | fail 2 ]
  | _ => find_inv_conv_2 R S k
  end.

Ltac build_chain_join_conv R S k :=
  match constr:(pair R S) with
  | pair (?R1++>?R2)%signature (?S1++>?S2)%signature => first [
      let c1 := find_split_conv S1 R1 in
      let with_c2 c2 :=
        let c := constr:(chain_join_conv c1 c2) in k c
      in build_chain_join_conv R2 S2 with_c2
    | fail 2 ]
  | _ => let c := find_join_conv R S in k c
  end.

(** The main tactic follows. *)

(*
Goal True.
let print x := let t := type of x in idtac t in
build_chain_conv (impl-->impl)%signature (iff++>impl)%signature print.
let print x := let t := type of x in idtac t in
build_chain_inv_conv (impl-->flip impl)%signature (iff++>impl)%signature print.
let print x := let t := type of x in idtac t in
build_chain_join_conv (impl-->impl++>flip impl)%signature (iff++>iff++>iff)%signature print.
Abort.
*)

Ltac conv_and_apply bc p :=
  match goal with |- Proper ?S ?f =>
    match type of p with Proper ?R ?g =>
      unify f g;
      let with_c c :=
        (* let t := type of c in idtac "got conversion" t; *)
        let p' := constr:(c f f p : Proper S f) in
        (* let t := type of p' in idtac "found" t; *)
        eexact p'
      in bc R S with_c
    | _ => (* idtac "conv_and_apply failure"; *) fail
    end
  end.

Ltac conv_apply     p := conv_and_apply ltac:(build_chain_conv) p.
Ltac conv_inv_apply p := conv_and_apply ltac:(build_chain_inv_conv) p.

Ltac conv_join_apply p :=
  match goal with |- Proper ?S ?f =>
    match type of p with Proper ?R ?g =>
      unify f g;
      let with_c c :=
        (*let t := type of c in idtac "got conversion" t;*)
        let p' := constr:(c f f (conj p p) : Proper S f) in
        (*let t := type of p' in idtac "found joined" t; *)
        eexact p'
      in build_chain_join_conv R S with_c
    | _ => (* idtac "conv_and_apply failure"; *) fail
    end
  end.


Ltac sig_tail_of s :=
  match s with | (_ ++> ?t)%signature => sig_tail_of t
               | _ => s end.

Ltac compare_tails p :=
  let t  := match type of p with Proper ?s _ => sig_tail_of s end in
  let tg := match goal with |- Proper ?s _ => sig_tail_of s end in
  match constr:(pair tg t) with
  | pair (flip ?R) ?R => first [ conv_inv_apply p | fail 2 ]
  | pair ?R (flip ?R) => first [ conv_inv_apply p | fail 2 ]
  | pair iff impl => first [ conv_join_apply p | fail 2 ]
  | _ => conv_apply p
  | _ => conv_inv_apply p
  | _ => conv_join_apply p
  end.

Ltac compare_rel sym R S k :=
  (* idtac "compare_rel" R S; *)
  first [
    is_evar S; first [ k sym | fail 2 ]
  | has_evar R;
    (* idtac "compare" R S; *)
    match constr:(pair R S) with
    | pair (restrict_rel ?RS ?RR) (restrict_rel ?SS ?SR) => first [
        unify RS SS; compare_rel sym RR SR k
      | fail 2 ]
    | pair _ (restrict_rel ?SS ?SR) => first [ compare_rel sym R SR k | fail 2 ]
    | pair (@equiv _ ?eq1) (@equiv _ ?eq2) => unify eq1 eq2; first [ k sym | fail 2 ]
    | _ => let S1 := match R with SubRelation ?S => S | flip (SubRelation ?S) => S end in
           let S2 := match S with SubRelation ?S => S | flip (SubRelation ?S) => S end in
           unify S1 S2; first [k false | fail 2]
    end
  | match sym with false => idtac end; first [ k false | fail 2 ]
  | has_evar S; first [ k sym | fail 2 ]
  | match S with @equiv _ _ => idtac end; first [k true | fail 2]
  | let fpsym := constr:(_:Find_Proper_Symmetric S) in first [ k true | fail 2 ]
  | k false
  ].

Ltac compare_tail_rel sym R S k :=
  first [
    match sym with true => idtac end;
    is_evar S; (* idtac "S is evar"; *)
    first [ has_evar R; fail 1 
    | let fpsym := constr:(_:Find_Proper_Symmetric R) in
      unify S R; first [ k true | fail 3 ]
    | let R' := match R with flip ?R' => R' | _ => R end in
      let ppo := constr:(_:Find_Proper_PrePartialOrder _ R') in
      let Rsym := match type of ppo with Find_Proper_PrePartialOrder ?Rsym _ => Rsym end in
      (* idtac "ppo" Rsym; *)
      unify S Rsym; first [ k true | fail 3 ]
    ]
  | compare_rel false S R k
  ].

Ltac compare_sigs n R R' k :=
  (* idtac "compare_sigs" n R R'; *)
  let rec cmp sym R R' :=
    match constr:(pair R R') with
    | pair (?R1++>?R2)%signature (?R1'++>?R2')%signature => first [
      let k' sym := cmp sym R2 R2' in compare_rel sym R1 R1' k'
      | fail 2 ]
    | _ => let k' sym := k n in compare_tail_rel sym R R' k'
    end
  in let rec chop n R R' :=
    match n with
    | O => cmp true R R'
    | S ?m => match R with (?R1++>?R2)%signature => chop m R2 R' end
    end
  in chop n R R' .

Ltac trim_apps n expr :=
  match n with
  | O => expr
  | S ?m => match expr with ?f _ => trim_apps m f end
  end.

Ltac count_len R k :=
  match R with
  | (?R1 ++> ?R2)%signature =>
      first [ let k' n := k (S n) in count_len R2 k' | fail 2 ]
  | _ => k 0%nat
  end.

Ltac compare_len R Sig k kfail :=
  match constr:(pair R Sig) with
  | pair (?R1 ++> ?R2)%signature (?S1 ++> ?S2)%signature =>
      first [ compare_len R2 S2 k kfail | fail 2 ]
  | pair _ (?S1 ++> ?S2)%signature => kfail 1
  | pair (?R1 ++> ?R2)%signature _ => 
      first [ let k' n := k (S n) in count_len R2 k' | fail 2 ]
  | _ => k 0%nat
  end.

Ltac compare_expr p k :=
  match type of p with Proper ?s ?e =>
    match goal with |- Proper ?sg ?eg =>
      (* idtac "compare_expr" e eg; *)
      let too_short _ := (* idtac "too short";*) fail in
      let with_len n :=
        (* idtac "extra params: " n; *)
        let eg' := trim_apps n eg in
        unify eg' e;
        let s'  := constr:(s) in
        let sg' := constr:(sg) in
        (* idtac s'; *)
        compare_sigs n s' sg' k
      in
      compare_len s sg with_len too_short
    end
  end.

(*
Ltac rebuild p pa k :=
  match pa with
  | _ => constr_eq p pa; first [ k p | fail 2 ]
  | ?f ?x => (* match type of x with ?t => idtac t end; *)
    let k' f' :=
      (* idtac "apply" x; *)
      let cont x' :=
        let pa' := constr:(f' x') in k pa'
      in
      match x with
      | _ => is_evar x; first [
          let t' := match type of f' with ?t -> _ => t end in
          (* idtac "finding instance of type" t'; *)
          match goal with
          | x' : t' |- _ => first [ cont x' | fail 2 ]
          | _ => let x' := constr:(_:t') in cont x'
          end
        | fail 2 ]
      | _ => cont x
      end
    in rebuild p f k'
  end.
*)

Ltac rebuild p pa k :=
  (* idtac "rebuild" p pa; *)
  let t' := type of pa in
  let t := constr:(t') in
  (* idtac "rebuild" t; *)
  let P := fresh "P" in
  assert t as P by (first [class_apply p; apply _ | apply p; apply _ ]); instantiate;
  (*assert t as P by (class_apply p; apply _); instantiate;*)
  let P' := constr:(P) in
  (* let t := type of P' in
  idtac "got" t; *)
  k P'.

Ltac head_of x :=
  match x with
  | ?f _ => head_of f
  | ?h => h
  end.

Ltac apply_evars p k :=
  match type of p with
  | Proper _ _ => k p
  | (∀ (x:?A), _) =>
    let x := fresh "x" in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let p' := constr:(p x') in
    apply_evars p' k
  end.

Ltac find_proper :=
  match goal with |- @Proper _ ?sig ?expr =>
    let h := head_of expr in
    let rec loop i := 
      let s := constr:(_:Find_Proper_Signature h i _) in
      (* try match i with O => idtac "find_proper" expr sig end; *)
      match type of s with Find_Proper_Signature _ _ ?T => (* idtac "trying" T; *)
      first [
        let p := constr:(find_proper_sig s : T) in
        let do_conv p :=
          (*let t := type of p in idtac "do_conv" t; *)
          compare_tails p
        in let do_cmp pevars :=
          let do_inst n :=
            let pe := constr:(pevars) in
            let do_partial pa :=
              let p := trim_proper n pa expr in do_conv p
            in rebuild p pe do_partial
          in compare_expr pevars do_inst
        in apply_evars p do_cmp
      | (* idtac "next";*) loop (S i) ]
      end
    in loop O
  end.

Hint Extern 0 (@Proper _ _ _) => find_proper : typeclass_instances.
