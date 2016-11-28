Require Import HoTT.
Require Import Auxiliary RawSyntax.

Section Structural_Rules.

Context (Σ : Signature).

(* Structural rules:

  - context formation rules
  - var rule
  - subst, wkg rules, for each type of judgement.
  - equality rules

*)


Section Context_Formation.

(* These need to be defined directly as closure conditions, since our raw rules only allow derivations of hypothetical judgements.  *)

Definition empty_context_cc : Closure_Condition (Judgt_Instance Σ).
Proof.
  split. 
  (* No premises: *)
  - exact [< >].
  (* Conclusion: *)
  - exact [Cxt! |- [::] !].
Defined.

Definition context_extension_cc : Family (Closure_Condition (Judgt_Instance Σ)).
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

(* An issue arising from the present approach to shapes/proto-contexts: if the context extension rule is formulated just with [shape_extend], then it will give no way to ever prove well-typedness of contexts with other shapes; in particular, of contexts using [shape_coprod], which will arise in the premises of logical rules.

  Possible solutions (without entirely changing the proto-context approach):

  - a closure condition for the context judgements under “renaming variables” along isomorphisms of proto-contexts?
  - formulate the context-extension rule in more general way: for *any* coproduct… (though still, is that enough?)
  - for now, just aim to work over the de Bruijn shape-system, in which case the standard rules actually are enough.
 *)

(* TODO: renaming-of-variables rule (?)*)

End Context_Formation.

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
      (Ty , shape_empty _ )    (* [ A ] *)
    >] : Arity).
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
      apply (plusone_top _ _ (shape_is_plusone _ _)).
    + exact [M/ A /].
Defined.

(* rule WKG_Ty

 |– A type
 |– B type
-------------
x:B |– A type
*)

Definition wkg_ty_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty, shape_empty _) (* [ A ] *)
    ; (Ty, shape_empty _) (* [ B ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (A := Some None : Metas).
  exists Metas.
  (* Premises *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ A type *)
      simple refine [Ty!  _  |-  _  !].
      *  exact [: :].
      * exact [M/ A/].
    + (* Premise ⊢ B type *)
      simple refine [Ty!  _  |-  _  !].
      * exact [::].
      * exact [M/ B/].
  (* Conclusion: x:B ⊢ A type *)
  - simple refine [Ty!  _  |-  _  !].
    + exact [: [M/ B /] :].
    + exact [M/ A /].
Defined.


(* rule WKG_Tm

 |– A type
 |– a:A
 |– B type
-------------
x:B |– a:A

*)

Definition wkg_tm_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty _ )    (* [ A ] *)
    ; (Tm , shape_empty _ )    (* [ a ] *)
    ; (Ty , shape_empty _ )    (* [ B ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (a := Some (None) : Metas).
  pose (A := Some (Some (None)) : Metas).
  exists Metas.
  (* premises *)
  - refine [< _ ; _ ; _ >].
    + (* Premise:  |— A type *)
      simple refine [Ty!  _  |-  _  !].
      * exact [: :].
      * exact [M/ A /].
    + (* Premise:  |— a : A *)
      simple refine ( [Tm! _  |-  _ ; _  !] ).
      * exact [: :].
      * exact [M/ a /].
      * exact [M/ A /].
    + (* Premise:  |— B type  *)
      simple refine ( [Ty! _  |-  _ !] ).
      * exact [: :].
      * exact [M/ B /].
  (* conclusion: x:B |- a : A *)
  - simple refine [Tm!  _  |-  _ ; _ !].
    + exact [: [M/ B /] :].
    + exact [M/ a /].
    + exact [M/ A /].
Defined.


(* rule WKG_TyEq
   ⊢ A ≡ B
   ⊢ C type
-------------
 x:C ⊢ A ≡ B
 *)

Definition wkg_ty_eq_raw_rule : Raw_Rule Σ.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty _ )    (* [ A ] *)
    ; (Ty , shape_empty _ )    (* [ B ] *)
    ; (Ty , shape_empty _ )    (* [ C ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (C := None : Metas).
  pose (B := Some (None) : Metas).
  pose (A := Some (Some None) : Metas).
  exists Metas.
  (* premises *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [TyEq! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ C type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ C /].
  (* Conclusion : x:C ⊢ A ≡ B *)
  - simple refine [TyEq! _ |- _ ≡ _ !].
    + exact [: [M/ C /] :].
    + exact [M/ A /].
    + exact [M/ B /].
Defined.

(* rule WKG_TmEq
   ⊢ u ≡ v : A
   ⊢ B type
-----------------
 x:B ⊢ u ≡ v : A
 *)

Definition wkg_tm_eq_raw_rule : Raw_Rule Σ.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty _ )    (* [ A ] *)
    ; (Ty , shape_empty _ )    (* [ B ] *)
    ; (Tm , shape_empty _ )    (* [ u ] *)
    ; (Tm , shape_empty _ )    (* [ v ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (v := None : Metas).
  pose (u := Some (None) : Metas).
  pose (B := Some (Some None) : Metas).
  pose (A := Some (Some (Some None)) : Metas).
  exists Metas.
  (* Premises *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ u ≡ v : A *)
      simple refine [TmEq! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
    + (* Premise ⊢ B type *)
      simple refine [Ty! _ |- _ !].
      * exact [::].
      * exact [M/ B /].
  (* Conclusion : x:B ⊢ u ≡ v : A *)
  - simple refine [TmEq! _ |- _ ≡ _ ; _ !].
    + exact [: [M/ B /] :].
    + exact [M/ A /].
    + exact [M/ u /].
    + exact [M/ v /].
Defined.

(* TODO: QUESTION — is it enough to give single-variable substitution rules, or must we give more general family of rules for substituting along context morphisms? *)

(* TODO: rule SUBST_Ty *)

(* TODO: rule SUBST_TmEq *)

(* TODO: rule SUBST_TyEq *)

(* TODO: rule SUBST_TmEq *)

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
      (Ty , shape_empty _ )    (* [ A ] *)
    >] : Arity).
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
      (Ty , shape_empty _ )    (* [ A ] *)
    ; (Ty , shape_empty _ )    (* [ B ] *)
    >] : Arity).
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
      (Ty , shape_empty _ )    (* [ A ] *)
    ; (Ty , shape_empty _ )    (* [ B ] *)
    ; (Ty , shape_empty _ )    (* [ C ] *)
    >] : Arity).
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
      (Ty , shape_empty _)    (* [ A ] *)
    ; (Tm , shape_empty _)    (* [ u ] *)
    >] : Arity).
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
      (Ty , shape_empty _)    (* [ A ] *)
    ; (Tm , shape_empty _)    (* [ u ] *)
    ; (Tm , shape_empty _)    (* [ v ] *)
    >] : Arity).
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
      (Ty , shape_empty _)    (* [ A ] *)
    ; (Tm , shape_empty _)    (* [ u ] *)
    ; (Tm , shape_empty _)    (* [ v ] *)
    ; (Tm , shape_empty _)    (* [ w ] *)
    >] : Arity).
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

(* rule COERCE_Ty

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)

Definition coerce_ty_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty _)    (* [ A ] *)
    ; (Ty , shape_empty _)    (* [ B ] *)
    ; (Tm , shape_empty _)    (* [ u ] *)
    >] : Arity).
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
  (* Conclusion : ⊢ u ≡ w : A *)
  - simple refine [Tm! _ |- _ ; _ !].
    + exact [::].
    + exact [M/ u /].
    + exact [M/ B /].
Defined.

End Equality_Rules.

End Structural_Rules.
