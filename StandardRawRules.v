Require Import HoTT.
Require Import ShapeSystems.
Require Import DeductiveClosure.
Require Import Family.
Require Import Coproduct.
Require Import RawSyntax.
Require Import SignatureMaps.
Require Import RawTypeTheories.

(** This module defines the “standard rules” — the rules which are not explicitly specified in a type theory, but are always assumed to be present.  These fall into several groups.   

- context formation
- substitution rules
- variable rule
- equality rules
- associated congruence rules: any logical rule-specification determines a corresponding cogruence rule specification

Since “rule” in our terminology consist just of hypothetical judgements over a common context, the structural rules that don’t fit this form (context formation and substitution) have to be given directly as families of closure conditions.

All of the above *except* for associated congruence rules (TODO: these should really be moved out of this file!) are collected for quick export as a single family [Structural_CCs].
*)

Section Structural_Rules.

Context {σ : Shape_System}.
Context (Σ : @Signature σ).

Section Context_Formation.

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

Definition context_ccs
  : Family (closure_condition (Judgt_Instance Σ))
:= Family.Snoc context_extension_cc empty_context_cc.

(* An issue arising from the present approach to shapes/proto-contexts: if the context extension rule is formulated just with [shape_extend] as above, then it will give no way to ever prove well-typedness of contexts with other shapes; in particular, of contexts using [shape_coproduct], which will arise in the premises of logical rules.

  Possible solutions (without entirely changing the proto-context approach):

  - a closure condition for the context judgements under “renaming variables” along isomorphisms of proto-contexts?
  - formulate the context-extension rule in more general way: for *any* coproduct… (though still, is that enough?)
  - for now, just aim to work over the de Bruijn shape-system, in which case the standard rules actually are enough.
 *)

(* TODO: renaming-of-variables rule (?)*)

End Context_Formation.

Section Substitution.

(* General substitution along context maps. *)

Definition subst_cc : Family (closure_condition (Judgt_Instance Σ)).
Proof.
  exists {   Γ : Raw_Context Σ
    & { Γ' : Raw_Context Σ
    & { f : Raw_Context_Map Σ Γ' Γ
    & { hjf : Hyp_Judgt_Form
    & Hyp_Judgt_Form_Instance Σ hjf Γ}}}}.
  intros [Γ [Γ' [f [hjf hjfi]]]].
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
  (* conclusion: *)
  - exists (HJF hjf).
    exists Γ'.
    intros i. exact (Raw_Subst f (hjfi i)).
Defined.

(* Substitution respects *equality* of context morphisms *)
Definition subst_eq_cc : Family (closure_condition (Judgt_Instance Σ)).
Proof.
  exists {   Γ : Raw_Context Σ
    & { Γ' : Raw_Context Σ
    & { f : Raw_Context_Map Σ Γ' Γ
    & { f' : Raw_Context_Map Σ Γ' Γ
    & { cl : Syn_Class
    & Hyp_Judgt_Form_Instance Σ (obj_HJF cl) Γ}}}}}.
  intros [Γ [Γ' [f [f' [cl hjfi]]]]].
  split.
  (* premises: *)
  - refine (Snoc (_ + _ + _) _).
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (Raw_Subst f (Γ i)).
    (* f' is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f' i).
      * exact (Raw_Subst f' (Γ i)).
    (* f ≡ f' *)
    + exists Γ.
      intros i. refine [TmEq! Γ' |- _ ≡ _ ; _ !].
    (* TODO: note inconsistent ordering of arguments in [give_Tm_ji] compared to other [give_Foo_ji].  Consider, consistentise? *)
      * exact (Raw_Subst f (Γ i)).
      * exact (f i).
      * exact (f' i).
    (* the judgement holds over Γ *)
    + exists (HJF (obj_HJF cl)).
      exists Γ.
      exact hjfi.
 (* conclusion: *) 
  - exists (HJF (eq_HJF cl)).
    exists Γ'.
    cbn. intros [i | ]. 
    + (* boundry and LHS *)
      exact (Raw_Subst f (hjfi i)).
    + (* RHS *)
      exact (Raw_Subst f' (hjfi None)).
Defined.

Definition subst_ccs : Family (closure_condition (Judgt_Instance Σ))
  := subst_cc + subst_eq_cc.

End Substitution.

Section Hyp_Structural_Rules.

(* Hypothetical structural rules:

  - var rule
  - equality rules

*)

(* The var rule:

  |– A type
-----------
x:A |– x:A

*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (Ty , shape_empty σ )    (* [ A ] *)
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
      (Ty , shape_empty σ )    (* [ A ] *)
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
      (Ty , shape_empty σ )    (* [ A ] *)
    ; (Ty , shape_empty σ )    (* [ B ] *)
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
      (Ty , shape_empty σ )    (* [ A ] *)
    ; (Ty , shape_empty σ )    (* [ B ] *)
    ; (Ty , shape_empty σ )    (* [ C ] *)
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
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
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
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ v ] *)
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
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ v ] *)
    ; (Tm , shape_empty σ)    (* [ w ] *)
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
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Ty , shape_empty σ)    (* [ B ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
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
      (Ty , shape_empty σ)    (* [ A ] *)
    ; (Ty , shape_empty σ)    (* [ B ] *)
    ; (Tm , shape_empty σ)    (* [ u ] *)
    ; (Tm , shape_empty σ)    (* [ u' ] *)
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

Definition Equality_Raw_Rules : Family (Raw_Rule Σ)
:= [< refl_ty_eq_raw_rule 
    ; symm_ty_eq_raw_rule
    ; trans_ty_eq_raw_rule
    ; refl_tm_eq_raw_rule 
    ; symm_tm_eq_raw_rule
    ; trans_tm_eq_raw_rule
    ; coerce_tm_raw_rule
    ; coerce_tmeq_raw_rule
  >]. 

End Equality_Rules.

End Hyp_Structural_Rules.

Definition Structural_CCs : Family (closure_condition (Judgt_Instance Σ))
:= context_ccs
  + subst_ccs
  + CCs_of_RR var_raw_rule
  + Family.Bind Equality_Raw_Rules CCs_of_RR.
(* TODO: add Haskell-style >= notation for bind? *)
(* TODO: capitalise naming in [Context_CCs], etc. *)

End Structural_Rules.

(* TODO: move the following to a separate file, probably — e.g. would make much more sense with [Raw_Rule_of_Rule_Spec]. *)
Section Congruence_Rules.

  Context {σ : Shape_System}.
  Context (Σ : @Signature σ).

  Definition associated_original_premise {obs eqs : Arity σ}
    : (obs + obs) + (eqs + eqs + obs) -> (obs + eqs).
  Proof.
    intros p ; repeat destruct p as [p | p];
      try exact (inl p); exact (inr p).
  Defined.
  
  Arguments associated_original_premise : simpl nomatch.

  (* The ordering of premises of the congruence rule_spec associated to an object rule_spec. 

  TODO: perhaps try to refactor to avoid so many special cases?  E.g. as: take the lex product of the input relation [R] with the 3-element order ({{0},{1},{0,1}}, ⊂ ) and then pull this back along the suitable map (o+o)+(e+e+o) —> (o+e)*3 ?  *)
  Definition associated_congruence_rule_lt
      {obs eqs : Type} (lt : relation (obs + eqs))
    : relation ((obs + obs) + (eqs + eqs + obs)).
  Proof.
  (*  In a more readable organisation, the cases we want are as follows:

           ob_l i   ob_r i   eq_l i   eq_r i   eq_new i

ob_l j     i < j    0        i < j    0        0

ob_r j     0        i < j    0        i < j    0
 
eq_l j     i < j    0        i < j    0        0

eq_r j     0        i < j    0        i < j    0

eq_new j   i ≤ j    i ≤ j    i < j    i < j    i < j

*)
    intros [ [ ob_l | ob_r ] | [ [ eq_l | eq_r ] | eq_new ] ];
    intros [ [ ob'_l | ob'_r ] | [ [ eq'_l | eq'_r ] | eq'_new ] ].
      (* column eq_l *)
    - exact (lt (inl ob_l) (inl ob'_l)).
    - exact False.
    - exact (lt (inl ob_l) (inr eq'_l)).
    - exact False.
    - exact ((lt (inl ob_l) (inl eq'_new)) \/ (ob_l = eq'_new)).
      (* column ob_r *)
    - exact False.
    - exact (lt (inl ob_r) (inl ob'_r)).
    - exact False.
    - exact (lt (inl ob_r) (inr eq'_r)).
    - exact ((lt (inl ob_r) (inl eq'_new)) \/ (ob_r = eq'_new)).
      (* column eq_l *)
    - exact (lt (inr eq_l) (inl ob'_l)).
    - exact False.
    - exact (lt (inr eq_l) (inr eq'_l)).
    - exact False.
    - exact (lt (inr eq_l) (inl eq'_new)).
      (* column eq_r *)
    - exact False.
    - exact (lt (inr eq_r) (inl ob'_r)).
    - exact False.
    - exact (lt (inr eq_r) (inr eq'_r)).
    - exact (lt (inr eq_r) (inl eq'_new)).
      (* column eq_new *)
    - exact False.
    - exact False.
    - exact False.
    - exact False.
    - exact (lt (inl eq_new) (inl eq'_new)).
  Defined.

  Arguments associated_congruence_rule_lt : simpl nomatch.

  Definition associated_congruence_rule_original_constructor_translation
    {a} {γ_concl} {hjf_concl} (R : Rule_Spec Σ a γ_concl hjf_concl)
    (p : (a + a) + (RS_equality_premise R + RS_equality_premise R + a))
    : Signature_Map
        (Metavariable_Extension Σ
          (RS_arity_of_premise R (associated_original_premise p)))
        (Metavariable_Extension Σ (Subfamily (a + a)
           (fun j => associated_congruence_rule_lt (RS_lt R) (inl j) p))).
  Proof.
    (* In case [p] is one of the 2 copies of the original premises, there is a single canonical choice for this definition.

    In case [p] is one of the new equality premises (between the 2 copies of the old equality premises), there are in principle 2 possibilities; it should make no difference which one chooses. *)
      destruct p as [ [ pob_l | pob_r ] | [ [ peq_l | peq_r ] | peq_new ] ].
      - (* pob_l *)
        simple refine (_;_).
        + intros [s | q].
          * exact (inl s). 
          * refine (inr _). exists (inl (pr1 q)). exact (pr2 q).
        + intros [? | ?]; exact idpath. 
      - (* pob_r *) 
        simple refine (_;_).
        + intros [s | q].
          * exact (inl s). 
          * refine (inr _). exists (inr (pr1 q)). exact (pr2 q).
        + intros [? | ?]; exact idpath. 
      - (* peq_l *) 
        simple refine (_;_).
        + intros [s | q].
          * exact (inl s). 
          * refine (inr _). exists (inl (pr1 q)). exact (pr2 q).
        + intros [? | ?]; exact idpath. 
      - (* peq_r *) 
        simple refine (_;_).
        + intros [s | q].
          * exact (inl s). 
          * refine (inr _). exists (inr (pr1 q)). exact (pr2 q).
        + intros [? | ?]; exact idpath. 
      - (* peq_new *)
        simple refine (_;_).
        + intros [s | q].
          * exact (inl s). 
          * refine (inr _).
            exists (inr (pr1 q)). (* note both [inl], [inr] make this work *)
            cbn; cbn in q. exact (inl (pr2 q)).
        + intros [? | ?]; exact idpath.         
  Defined.

  (* TODO: move *)
  (* Useful, with [idpath] as the equality argument, when want wants to construct the smybol argument interactively — this is difficult with original [symb_raw] due to [class S] appearing in the conclusion. *)
  Definition symb_raw' {Σ' : Signature σ}
      {γ} {cl} (S : Σ') (e : class S = cl)
      (args : forall i : arity S,
        Raw_Syntax Σ' (arg_class i) (shape_coproduct γ (arg_pcxt i)))
    : Raw_Syntax Σ' cl γ.
  Proof.
    destruct e.
    apply symb_raw; auto.
  Defined.

  Definition associated_congruence_rule_spec
    {a} {γ_concl} {hjf_concl} (R : Rule_Spec Σ a γ_concl hjf_concl)
    (H : is_obj_HJF hjf_concl)
    (S : Σ)
    (e_a : arity S = a + (simple_arity γ_concl))
    (e_cl : class S = class_of_HJF hjf_concl)
    : (Rule_Spec Σ (Family.Sum a a) γ_concl
                 (eq_HJF (class_of_HJF hjf_concl))).
  Proof.
    simple refine (Build_Rule_Spec _ _ _ _ _ _ _ _ _ _).
    - (* RS_equality_premise: arity of equality premises *)
      exact (((RS_equality_premise R) + (RS_equality_premise R)) + a). 
    - (* RS_lt *)
      exact (associated_congruence_rule_lt (RS_lt R)).
    - (* RS_context_expr_of_premise *)
      intros p i.
      refine (Fmap_Raw_Syntax
        (associated_congruence_rule_original_constructor_translation _ _) _).
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | ? ] ];
      refine (RS_context_expr_of_premise R p_orig i).
      (* alternatively, instead of destructing [p], could use equality reasoning on the type of [i]. *)
    - (* RS_hyp_bdry_instance_of_premise *)
      intros p.
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | p ] ];
      try (refine (Fmap_Hyp_Judgt_Bdry_Instance
        (associated_congruence_rule_original_constructor_translation _ _) _);
           refine (RS_hyp_bdry_instance_of_premise R p_orig)).
      (* The cases where [p] is a copy of an original premise are all just translation,
      leaving just the new equality premises to give. *)
      intros i; simpl Hyp_Judgt_Bdry_Slots in i.
      destruct i as [ [ i | ] | ]; [ idtac | simpl | simpl]. 
      + (* boundary of the corresponding original premise *)
        refine (Fmap_Raw_Syntax
          (associated_congruence_rule_original_constructor_translation _ _) _).
        apply (RS_hyp_bdry_instance_of_premise R p_orig).
      + (* LHS of new equality premise *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inr_Metavariable.
          refine (inl p; _).
          apply inr, idpath.
        * apply idpath.
        * intros i.
          apply var_raw, (coproduct_inj1 shape_is_coproduct), i.
      + (* RHS of new equality premise *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inr_Metavariable.
          refine (inr p; _).
          apply inr, idpath.
        * apply idpath.
        * intros i.
          apply var_raw, (coproduct_inj1 shape_is_coproduct), i.
    - (* RS_context_expr_of_conclusion *)
      intros i.
      refine (Fmap_Raw_Syntax _ (RS_context_expr_of_conclusion R i)).
      apply Fmap2_Metavariable_Extension, inl_Family.
    - (* RS_hyp_judgt_bdry_instance_of_conclusion *)
      intros [ [ i | ] | ]; simpl. 
      + (* boundary of original conclusion *)
        refine (Fmap_Raw_Syntax _ _).
        * apply Fmap2_Metavariable_Extension, inl_Family.
        * destruct hjf_concl as [cl | ?].
          -- exact (RS_hyp_judgt_bdry_instance_of_conclusion R i).
          -- destruct H. (* [hjf_concl] can’t be an equality judgement *)
      + (* LHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros [ p | i ].
          -- simple refine (symb_raw' _ _ _).
             ++ apply inr_Metavariable.
                exact (inl p).
             ++ apply idpath.
             ++ cbn. intros i.
                apply var_raw. 
                apply (coproduct_inj1 shape_is_coproduct).
                apply (coproduct_inj2 shape_is_coproduct).
                exact i.
          -- apply var_raw, (coproduct_inj1 shape_is_coproduct), i.
      + (* RHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros [ p | i ].
          -- simple refine (symb_raw' _ _ _).
             ++ apply inr_Metavariable.
                exact (inr p).
             ++ apply idpath.
             ++ cbn. intros i.
                apply var_raw. 
                apply (coproduct_inj1 shape_is_coproduct).
                apply (coproduct_inj2 shape_is_coproduct).
                exact i.
          -- apply var_raw, (coproduct_inj1 shape_is_coproduct), i.
  Defined.
  (* TODO: the above is a bit unreadable.  An alternative approach that might be clearer and more robust:
   - factor out the constructions of the head terms of conclusions and premises from [Raw_Rule_of_Rule_Spec], if doable.
   - here, invoke those, but (for the LHS/RHS of the new equalities), translate them under appropriate context morphisms “inl”, “inr”. *)

(* A good test proposition will be the following: whenever a rule-spec is well-typed, then so is its associated congruence rule-spec. *)

(* TODO: add “substitution respects judgemental equality” structural rules.  Just like the main “substitution” rules, this should be admissible anyway in case all logical rules are given in “absolute” form, with no context in conclusion, but is required if we allow rules where contexts have non-empty conclusion, and seems natural to include in any case — certainly once we’ve decided to add substitution rules at all. *)

End Congruence_Rules.

