Require Import HoTT.
Require Import ShapeSystems.
Require Import DeductiveClosure.
Require Import Family.
Require Import Coproduct.
Require Import RawSyntax.
Require Import RawTypeTheories.

(** This module defines the “standard rules” — the rules which are not explicitly specified in a type theory, but are always assumed to be present.  These fall into several groups:

- context formation rules (in fact closure conditions in our terminology, not rules, since the latter involve only hypothetical judgements)
- structural rules
- congruence rules: any logical rule-specification determines a corresponding cogruence rule specification
*)

Section Context_Formation.

Context {Proto_Cxt : Shape_System}.
Context (Σ : @Signature Proto_Cxt).

(* These need to be defined directly as closure conditions, since our raw rules only allow derivations of hypothetical judgements.  *)

Definition empty_context_cc : closure_condition (Judgt_Instance Σ).
Proof.
  split.
  (* No premises: *)
  - exact [< >].
  (* Conclusion: *)
  - exact [Cxt! |- [::] !].
Defined.

Definition context_extension_cc : Family (closure_condition (Judgt_Instance Σ)).
Proof.
  exists { Γ : Raw_Context Σ & Raw_Syntax Σ Ty Γ }.
  intros [ Γ A ]; split.
  (* Premises: |- Γ cxt; Γ |- A type *)
  - refine [< _ ; _ >].
    + exact [Cxt! |- Γ !].
    + exact [Ty! Γ |- A !].
  (* Conclusion: *)
  - exact [Cxt! |- (snoc_Raw_Context Γ A) !].
Defined.

(* An issue arising from the present approach to shapes/proto-contexts: if the context extension rule is formulated just with [shape_extend] as above, then it will give no way to ever prove well-typedness of contexts with other shapes; in particular, of contexts using [shape_coproduct], which will arise in the premises of logical rules.

  Possible solutions (without entirely changing the proto-context approach):

  - a closure condition for the context judgements under “renaming variables” along isomorphisms of proto-contexts?
  - formulate the context-extension rule in more general way: for *any* coproduct… (though still, is that enough?)
  - for now, just aim to work over the de Bruijn shape-system, in which case the standard rules actually are enough.
 *)

(* TODO: renaming-of-variables rule (?)*)

End Context_Formation.

Section Structural_Rules.

(* Structural rules:

  - var rule
  - subst, wkg rules, for each type of judgement.
  - equality rules

*)

Context {Proto_Cxt : Shape_System}.
Context (Σ : @Signature Proto_Cxt).


Section Var_Subst_Wkg.

(* The var rule:

  |– A type
-----------
x:A |– x:A

*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt )    (* [ A ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* single premise:  |— A type *)
  - simple refine [< [Ty! _ |- _ !] >].
    + exact [: :].
    + exact [M/ A /].
  (* conclusion:  x:A |- x:A *)
  - simple refine [Tm! _ |- _ ; _ !].
    + exact [: [M/ A /] :].
    + refine (var_raw _).
      apply (plusone_one _ _ (shape_is_plusone _ _)).
    + exact [M/ A /].
Defined.

(* General substitution/weakening: another special case that has to be given directly as a closure condition, since it doesn’t fit the pattern of our raw rules. *)

(* TODO: consider names of access functions. *)
Record Substitution_Data
:=
  { src : Raw_Context Σ
  ; tgt : Raw_Context Σ
  ; map : Raw_Context_Map Σ src tgt
  }.

Definition subst_cc : Family (closure_condition (Judgt_Instance Σ)).
Proof.
  exists {f : Substitution_Data
       & { hjf : Hyp_Judgt_Form
       & forall i : Hyp_Judgt_Form_Slots hjf,
                         Raw_Syntax Σ (fam_element _ i) (tgt f) }}.
  intros [[Γ' Γ f] [hjf hjfi]].
  split.
  (* premises: *)
  - apply Snoc.
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (Raw_Subst f (Γ i)).
    (* the judgement holds over Γ *)
    + exists (HJF hjf).
      exists Γ.
      exact hjfi.
  - exists (HJF hjf).
    exists Γ'.
    intros i. exact (Raw_Subst f (hjfi i)).
Defined.

End Var_Subst_Wkg.

Section Equality_Rules.

(* rule REFL_TyEq
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Definition refl_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt )    (* [ A ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
  (* Conclusion : ⊢ A ≡ A *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ A /].
Defined.

(* rule SYMM_TyEq
   ⊢ A ≡ B
--------------
   ⊢ B ≡ A
*)

Definition symm_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt )    (* [ A ] *)
    ; (Ty , shape_empty Proto_Cxt )    (* [ B ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (A := Some None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
  (* Conclusion : ⊢ B ≡ A *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ B /].
    + exact [M/ A /].
Defined.

(* rule TRANS_TyEq
  ⊢ A ≡ B     ⊢ B ≡ C
-----------------------
       ⊢ A ≡ C
*)

Definition trans_ty_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt )    (* [ A ] *)
    ; (Ty , shape_empty Proto_Cxt )    (* [ B ] *)
    ; (Ty , shape_empty Proto_Cxt )    (* [ C ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (C := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ B ≡ C *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ B /].
      * exact [M/ C /].
  (* Conclusion : ⊢ A ≡ C *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ C /].
Defined.

(* rule REFL_TmEq
  ⊢ u : A
-----------
⊢ u ≡ u : A
*)

Definition refl_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt)    (* [ A ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (A := Some None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u : A type *)
      simple refine [Tm! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion : ⊢ u ≡ u : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ u /].
    + exact [M/ u /].
Defined.

(* rule SYMM_TmEq
   ⊢ u ≡ v : A
----------------
   ⊢ v ≡ u : A
*)

Definition symm_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt)    (* [ A ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ v ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (v := None : Metas).
  pose (u := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u ≡ v : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
  (* Conclusion : ⊢ v ≡ u : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ v /].
    + exact [M/ u /].
Defined.

(* rule TRANS_TmEq
  ⊢ u ≡ v : A     ⊢ v ≡ w : A
-------------------------------
         ⊢ u ≡ w : A
*)

Definition trans_tm_eq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt)    (* [ A ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ v ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ w ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (w := None : Metas).
  pose (v := Some None : Metas).
  pose (u := Some (Some None) : Metas).
  pose (A := Some (Some (Some None)) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ u ≡ v : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
    + (* Premise ⊢ v ≡ w : A type *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ v /].
      * exact [M/ w /].
  (* Conclusion : ⊢ u ≡ w : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ u /].
    + exact [M/ w /].
Defined.

(* rule COERCE_Tm

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)

Definition coerce_tm_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt)    (* [ A ] *)
    ; (Ty , shape_empty Proto_Cxt)    (* [ B ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ ; _ ; _ >].
    + (* Premise ⊢ A type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
    + (* Premise ⊢ B type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ B /].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ u : A *)
      simple refine [Tm! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion: ⊢ u : B *)
  - simple refine [Tm! _ |- _ ; _ !].
    + exact [::].
    + exact [M/ u /].
    + exact [M/ B /].
Defined.

(* rule COERCE_TmEq

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u, u' : A 
 ⊢ u = u' : A
-------------
 ⊢ u = u' : B
*)

Definition coerce_tmeq_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty Proto_Cxt)    (* [ A ] *)
    ; (Ty , shape_empty Proto_Cxt)    (* [ B ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u ] *)
    ; (Tm , shape_empty Proto_Cxt)    (* [ u' ] *)
    >] : Arity _).
  (* Name the symbols. *)
  pose (A := Some (Some (Some None)) : Metas).
  pose (B := Some (Some None) : Metas).
  pose (u := Some None : Metas).
  pose (u' := None : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ ; _ ; _ ; _ ; _ >].
    + (* Premise ⊢ A type *)
      exact [Ty! [::] |- [M/ A /] !].
    + (* Premise ⊢ B type *)
      exact [Ty! [::] |- [M/ B /] !].
    + (* Premise ⊢ A ≡ B *)
      exact [TyEq! [::] |- [M/ A /] ≡ [M/ B /] !].
    + (* Premise ⊢ u : A *)
      exact [Tm! [::] |- [M/ u /] ; [M/ A /] !].
    + (* Premise ⊢ u' : A *)
      exact [Tm! [::] |- [M/ u' /] ; [M/ A /] !].
    + (* Premise ⊢ u ≡ u' : A *)
      exact [TmEq! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ A /] !].
  (* Conclusion: ⊢ u ≡ u' : B *)
  - exact [TmEq! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ B /] !].
Defined.

End Equality_Rules.

End Structural_Rules.

Section Congruence_Rules.

Context {Proto_Cxt : Shape_System}.
Context (Σ : @Signature Proto_Cxt).

Definition associated_congruence_rule_spec
  {a} {cl} (R : Rule_Spec Σ a (obj_HJF cl))
  : (Rule_Spec Σ (Family.Sum a a) (eq_HJF cl)).
Admitted.
(* A good test proposition will be the following: whenever a rule-spec is well-typed, then so is its associated congruence rule-spec. *)

End Congruence_Rules.

