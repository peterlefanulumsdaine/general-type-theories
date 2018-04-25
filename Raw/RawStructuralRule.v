Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.RawSubstitution.
Require Import Raw.FlatRule.

(**
  This module defines the “standard rules” — the rules which are not explicitly specified
  in a type theory, but are always assumed to be present. These fall into several groups.

  - context formation
  - substitution rules
  - variable rule
  - equality rules

  Since “rule” in our terminology always mean _hypothetical_ rules, the structural rules
  that don’t fit this form (context formation and substitution) have to be given directly
  as families of closure conditions.

  All of the above are then collected as a single family [Structural_CCs].
*)

(** Naming convention for rule names: we prefix a rule name with a keyword, depending on
    what kind of rule it is:

    -- [ctx_XYZ] for context rule
    -- [term_XYZ] for term formation
    -- [type_XYZ] for type formation
    -- [tmeq_XYZ] for term equality
    -- [tyeq_XYZ] for type equality
    -- [subst_XYZ] for substitution rules
*)

Section StructuralRules.

Context {σ : shape_system}.
Context (Σ : signature σ).

Section ContextRules.

(* The empty context rule:

  ---------------
  |-  .   cxt

*)
Local Definition ctx_empty_rule : Closure.rule (judgement_total Σ).
Proof.
  split.
  (* No premises: *)
  - exact [< >].
  (* Conclusion: *)
  - exact [Cxt! |- [::] !].
Defined.

(* The context extension rule:

   |- Γ cxt
   Γ |- A type
   ----------------
   |- Γ, x:A cxt

*)
Local Definition ctx_extend_instance : Closure.system (judgement_total Σ).
Proof.
  exists { Γ : raw_context Σ & raw_type Σ Γ }.
  intros [ Γ A ]; split.
  (* Premises: |- Γ cxt; Γ |- A type *)
  - refine [< _ ; _ >].
    + exact [Cxt! |- Γ !].
    + exact [Ty! Γ |- A !].
  (* Conclusion: *)
  - exact [Cxt! |- (Context.extend Γ A) !].
Defined.

Local Definition context_instance : Closure.system (judgement_total Σ)
  := Family.adjoin ctx_extend_instance ctx_empty_rule.

End ContextRules.

Section RenamingRules.
(** Renaming of variables:

for any isomorphism of shapes [f : γ ≅ δ], we can rename variables along
[f] in any judgement with shape [γ], both hypothetical and context judgements:

  Γ |- J   [J any hypothetical judgement]
  --------------------
  f^* Γ |- f^*J

  |- Γ cxt
  --------------------
  |- f^* Γ cxt

This is not traditionally explicitly given; we need it because our context
extension rule only extends by “the standard fresh variable” over a given
shape, and so to show that e.g. contexts whose shapes are given as coproducts
are contexts, we need a rule like this (or some other strengthening of the
context rules, or restrictions on the shape system).
*)
  Local Definition rename_hypothetical_instance : Closure.system (judgement_total Σ).
  Admitted.

  Local Definition rename_context_instance : Closure.system (judgement_total Σ).
  Admitted.

  Local Definition rename_instance : Closure.system (judgement_total Σ)
    := rename_context_instance + rename_hypothetical_instance.

End RenamingRules.

Section SubstitutionRules.

(** General substitution along context maps:

  Γ' |- f(x) : A   [for each x in Γ, A := type of x in Γ]
  Γ |- J   [for J any hypothetical judgement]
  --------------------
  Γ' |- f^*J
*)
Local Definition subst_apply_instance : Closure.system (judgement_total Σ).
Proof.
  exists { Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { f : Context.map Σ Γ' Γ
    & { hjf : Judgement.hypothetical_form
    & hypothetical_judgement Σ hjf Γ}}}}.
  intros [Γ [Γ' [f [hjf hjfi]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin (Family.adjoin _ _) _).
    (* all components of [f] are suitably typed: *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* [Γ'] is a valid context: *)
    + exact [Cxt! |- Γ' !]. 
    (* the target judgement holds over Γ *)
    + exists (Judgement.form_hypothetical hjf).
      exists Γ.
      exact hjfi.
  (* conclusion: *)
  - exists (Judgement.form_hypothetical hjf).
    exists Γ'.
    intros i. exact (substitute f (hjfi i)).
Defined.

(** Substitution respects *equality* of context morphisms:

  Γ' |- f(x) = g(x) : A   [for each x in Γ, A := type of x in Γ]
  Γ |- J   [for J any hypothetical judgement]
  --------------------
  Γ' |- f^*J = g^*J  [ for J any object judgement ]
 *)
Local Definition subst_equal_instance : Closure.system (judgement_total Σ).
Proof.
  exists {   Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { f : Context.map Σ Γ' Γ
    & { f' : Context.map Σ Γ' Γ
    & { cl : syntactic_class
    & hypothetical_judgement Σ (form_object cl) Γ}}}}}.
  intros [Γ [Γ' [f [f' [cl hjfi]]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin (Family.adjoin (_ + _ + _) _) _).
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* f' is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f' i).
      * exact (substitute f' (Γ i)).
    (* f ≡ f' *)
    + exists Γ.
      intros i. refine [TmEq! Γ' |- _ ≡ _ ; _ !].
    (* TODO: note inconsistent ordering of arguments in [give_Tm_ji] compared to other
       [give_Foo_ji]. Consider, consistentise? *)
      * exact (substitute f (Γ i)).
      * exact (f i).
      * exact (f' i).
    (* [Γ'] is a valid context: *)
    + exact [Cxt! |- Γ' !]. 
    (* the target judgement holds over Γ *)
    + exists (Judgement.form_hypothetical (form_object cl)).
      exists Γ.
      exact hjfi.
  (* conclusion: *)
  - exists (Judgement.form_hypothetical (form_equality cl)).
    exists Γ'.
    intros [i | | ].
    + (* boundary *)
      exact (substitute f (hjfi (the_boundary _ i))).
    + (* LHS *)
      exact (substitute f (hjfi (the_head _))).
    + (* RHS *)
      exact (substitute f' (hjfi (the_head _))).
Defined.

Local Definition substitution_instance : Closure.system (judgement_total Σ)
  := subst_apply_instance + subst_equal_instance.

End SubstitutionRules.

Section HypotheticalStructuralRules.

(* Hypothetical structural rules:

  - var rule
  - equality rules

*)

(* The general variable rule:

  |- Γ cxt
  Γ |- A type
  ------------- (x in Γ, A := type of x in Γ)
  Γ |- x : A 

*)

Local Definition variable_instance : Closure.system (judgement_total Σ).
Proof.
  exists { Γ : raw_context Σ & Γ }.
  intros [Γ x]. set (A := Γ x). split.
  (* premises *)
  - exact [< [Cxt! |- Γ !]
           ; [Ty! Γ |- A !]
          >].
  (*conclusion *)
  - exact [Tm! Γ |- (raw_variable x) ; A !].
Defined.

Section Equality.

(* rule tyeq_refl
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Local Definition tyeq_refl_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ )    (* [ A ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (A := tt : Metas).
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

(* rule tyeq_sym
   ⊢ A ≡ B
--------------
   ⊢ B ≡ A
*)

Local Definition tyeq_sym_rule : flat_rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ )    (* [ A ] *)
    ; (class_type, shape_empty σ )    (* [ B ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (A := Some tt : Metas).
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

(* rule tyeq_tran
  ⊢ A ≡ B     ⊢ B ≡ C
-----------------------
       ⊢ A ≡ C
*)

Local Definition tyeq_tran_rule : flat_rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ )    (* [ A ] *)
    ; (class_type, shape_empty σ )    (* [ B ] *)
    ; (class_type, shape_empty σ )    (* [ C ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (C := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
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

(* rule tmeq_refl
  ⊢ u : A
-----------
⊢ u ≡ u : A
*)

Local Definition tmeq_refl_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (A := Some tt : Metas).
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

(* rule tmeq_sym
   ⊢ u ≡ v : A
----------------
   ⊢ v ≡ u : A
*)

Local Definition tmeq_sym_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    ; (class_term, shape_empty σ)    (* [ v ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (v := None : Metas).
  pose (u := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
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

(* rule tmeq_tran
  ⊢ u ≡ v : A     ⊢ v ≡ w : A
-------------------------------
         ⊢ u ≡ w : A
*)

Local Definition tmeq_tran_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    ; (class_term, shape_empty σ)    (* [ v ] *)
    ; (class_term, shape_empty σ)    (* [ w ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (w := None : Metas).
  pose (v := Some None : Metas).
  pose (u := Some (Some None) : Metas).
  pose (A := Some (Some (Some tt)) : Metas).
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

(* rule term_convert

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)

Local Definition term_convert_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_type, shape_empty σ)    (* [ B ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
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

(* rule tmeq_convert

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u, u' : A
 ⊢ u = u' : A
-------------
 ⊢ u = u' : B
*)

Local Definition tmeq_convert_rule : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_type, shape_empty σ)    (* [ B ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    ; (class_term, shape_empty σ)    (* [ u' ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (A := Some (Some (Some tt)) : Metas).
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

Local Definition equality_instance : family (rule (judgement_total Σ)) :=
  Family.bind
    [< tyeq_refl_rule
    ; tyeq_sym_rule
    ; tyeq_tran_rule
    ; tmeq_refl_rule
    ; tmeq_sym_rule
    ; tmeq_tran_rule
    ; term_convert_rule
    ; tmeq_convert_rule
    >]
    FlatRule.closure_system.

End Equality.

End HypotheticalStructuralRules.

Definition structural_rule : Closure.system (judgement_total Σ)
  := context_instance + substitution_instance + variable_instance + equality_instance.

End StructuralRules.


Section StructuralRuleAccessors.
  (** Access functions, for selcting structural rules in derivations *)

  (* Note: in a separate section just so that [Σ] can be declared as implicit
   argument for them all, rather than needing to be all redeclared with
   [Arguments] afterwards. *)

Context {σ : shape_system} {Σ : signature σ}.

Definition ctx_empty : structural_rule Σ := inl (inl (inl None)).
Definition ctx_extend : ctx_extend_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inl (Some i))).
Definition subst_apply : subst_apply_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inr (inl i))).
Definition subst_equal : subst_equal_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inr (inr i))).
Definition variable : variable_instance Σ -> structural_rule Σ
  := fun i => inl (inr i).
Definition equality : equality_instance Σ -> structural_rule Σ
  := fun i => inr i.
Definition tyeq_refl : FlatRule.closure_system (tyeq_refl_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some (Some (Some tt)))))) ; i).
Definition tyeq_sym : FlatRule.closure_system (tyeq_sym_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some (Some None))))) ; i).
Definition tyeq_tran : FlatRule.closure_system (tyeq_tran_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some None)))) ; i).
Definition tmeq_refl : FlatRule.closure_system (tmeq_refl_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some None))) ; i).
Definition tmeq_sym : FlatRule.closure_system (tmeq_sym_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some (Some None)) ; i).
Definition tmeq_tran : FlatRule.closure_system (tmeq_tran_rule Σ) -> structural_rule Σ
  := fun i => inr (Some (Some None) ; i).
Definition term_convert : FlatRule.closure_system (term_convert_rule Σ) -> structural_rule Σ
  := fun i => inr (Some None ; i).
Definition tmeq_convert : FlatRule.closure_system (tmeq_convert_rule Σ) -> structural_rule Σ
  := fun i => inr (None ; i).

End StructuralRuleAccessors.

Section StructuralRuleMap.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* TODO: perhaps abstract [Family_Map_over] or something, i.e. a displayed-category version of family maps, for use in definitions like this? *)

  (** For a given signature map [f] from [Σ] to [Σ'], give a family map from
     the structural rules of [Σ] to structural rules of [Σ']. *)
  Local Definition fmap
      {Σ Σ' : signature σ}
      (f : Signature.map Σ Σ')
    : Family.map
        (Family.fmap (Closure.fmap (fmap_judgement_total f)) (structural_rule Σ))
        (structural_rule Σ').
  Proof.
    (* TODO: possible better approach:
       - [Fmap_Family] of families commutes with sums;
       - then use [repeat apply Fmap_Family_Sum.] or similar.  *)
    (* TODO: intermediate approach: at least allow family map to be constructed as a single function, to avoid duplicated destructing. *)
    apply Family.Build_map'.
    intros [ [ [ [ c1 | ] | [c2 | c3] ] | c4 ]  | c5 ].
    (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap_Family] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: try a few by hand, then consider this. *)
    - (* context extension *)
      simple refine (_;_).
      + rename c1 into ΓA.
        refine (ctx_extend _).
        exists (Context.fmap f ΓA.1).
        exact (Expression.fmap f ΓA.2).
      + cbn. apply Closure.rule_eq.
        * simple refine (Family.eq _ _). { apply idpath. }
          cbn. intros [ [] | ].
          -- apply idpath.
          -- apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros [ [] | ];
             apply idpath.
        * cbn. apply (ap (fun x => (_; x))).
          apply (ap (Build_raw_context _)).
          apply path_forall.
          refine (plusone_rect _ _ (shape_is_extend _ _) _ _ _).
          -- eapply concat. { refine (plusone_comp_one _ _ _ _ _ _). }
             eapply concat.
               2: { apply ap. refine (plusone_comp_one _ _ _ _ _ _)^. }
             apply inverse. apply RawSubstitution.fmap_rename.
          -- intros x. cbn in x.
             eapply concat. { refine (plusone_comp_inj _ _ _ _ _ _ _). }
             eapply concat.
               2: { apply ap. refine (plusone_comp_inj _ _ _ _ _ _ _)^. }
             apply inverse. apply RawSubstitution.fmap_rename.
    - (* empty context *)
      exists (ctx_empty).
      cbn. apply Closure.rule_eq.
      * simple refine (Family.eq _ _). { apply idpath. }
        intros [].
      * cbn. apply (ap (fun x => (_; x))).
        apply (ap (Build_raw_context _)).
        apply path_forall. refine (empty_rect _ shape_is_empty _).
    - (* substitution *)
      destruct c2 as [ Γ [Γ' [g [hjf hjfi]]]].
      simple refine (_;_).
      + refine (subst_apply _).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          unfold Family.fmap.
          apply ap, path_forall; intros i.
          apply (ap (fun x => (_; x))).
          apply (ap (fun x => (_; x))).
          apply path_forall. intros [ [] | ]; try apply idpath.
          refine (fmap_substitute _ _ _).
        * apply (ap (fun x => (_; x))).
          apply (ap (fun x => (_; x))).
          apply path_forall. intros i.
          unfold Judgement.fmap_hypothetical_judgement.
          refine (fmap_substitute _ _ _)^.
    - (* substitution equality *)
      destruct c3 as [ Γ [Γ' [g [g' [hjf hjfi]]]]].
      simple refine (_;_).
      + refine (subst_equal _).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists (fmap_raw_context_map f g').
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          eapply concat. { apply Family.fmap_sum. }
          eapply concat. { eapply (ap (fun K => K + _)), Family.fmap_sum. }
          apply ap2; try apply ap2; unfold Family.fmap.
          -- apply ap, path_forall; intros i.
             apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros [ [] | ]; try apply idpath.
             refine (fmap_substitute _ _ _).
          -- apply ap, path_forall; intros i.
             apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros [ [] | ]; try apply idpath.
             refine (fmap_substitute _ _ _).
          -- apply ap, path_forall; intros i.
             apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros j.
             destruct j as [ [] | | ]; try apply idpath.
             refine (fmap_substitute _ _ _).
        * apply (ap (fun x => (_; x))).
          apply (ap (fun x => (_; x))).
          apply path_forall. intros i.
          unfold Judgement.fmap_hypothetical_judgement.
          destruct i; refine (fmap_substitute _ _ _)^.
    - (* var rule *)
      destruct c4 as [Γ x].
      simple refine (variable _ ; _).
      + exists (Context.fmap f Γ); exact x.
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          apply Judgement.eq_by_eta, idpath.
        * apply Judgement.eq_by_eta, idpath.
    - (* equality rules *)
      simple refine (equality _; _); admit.
      (* This should be do-able cleanly going via a lemma about
      naturality of translation of flat rules into closure rules,
      used for logical rules in [fmap] below, once that’s done. *)
  Admitted.

End StructuralRuleMap.