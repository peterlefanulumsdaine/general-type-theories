Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.Substitution.
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
Context (Σ : @signature σ).

Section Context.

Local Definition ctx_empty : Closure.rule (judgement_total Σ).
Proof.
  split.
  (* No premises: *)
  - exact [< >].
  (* Conclusion: *)
  - exact [Cxt! |- [::] !].
Defined.

Local Definition ctx_extend : Closure.system (judgement_total Σ).
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

Local Definition context : Closure.system (judgement_total Σ)
  := Family.adjoin ctx_extend ctx_empty.

(**

  NOTE: an issue arising from the present approach to shapes/proto-contexts: if the
  context extension rule is formulated just with [shape_extend] as above, then it will
  give no way to ever prove well-typedness of contexts with other shapes; in particular,
  of contexts using [shape_coproduct], which will arise in the premises of logical rules.

  Possible solutions (without entirely changing the proto-context approach):

  - for now, we just aim to work over the de Bruijn shape-system, in which case the
    standard rules as currently given are enough;

  - to give the standard rules in named-variable case, formulate the context-extension
    rule in more general way: for *any* (γ+1) coproduct, … (again, should be enough in
    finitary shape systems)

  - add a closure condition for the context judgements under “renaming variables” along
    isomorphisms of proto-contexts? (should again suffice in enough in “finitary” shape
    systems, i.e. where all shapes finite, and is a nice derived rule to have anyway)

  - for eventual generalisation to infinitary settings, is there some more uniform way of
    setting this up that would give the standard rules as derived rules? e.g. (a) put
    well-orderings on (proto-)contexts, and say: a context is well-typed if each type is
    well-typed under earlier parts? (b) similar, but without well-orderings (and then
    allow derivations to take place over not-yet-well-typed contexts)?
*)

End Context.

Section Substitution.

(** General substitution along context maps. *)

Local Definition subst_apply : Closure.system (judgement_total Σ).
Proof.
  exists { Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { f : Context.map Σ Γ' Γ
    & { hjf : Judgement.hypothetical_form
    & hypothetical_judgement Σ hjf Γ}}}}.
  intros [Γ [Γ' [f [hjf hjfi]]]].
  split.
  (* premises: *)
  - apply Family.adjoin.
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [Tm! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* the judgement holds over Γ *)
    + exists (Judgement.form_hypothetical hjf).
      exists Γ.
      exact hjfi.
  (* conclusion: *)
  - exists (Judgement.form_hypothetical hjf).
    exists Γ'.
    intros i. exact (substitute f (hjfi i)).
Defined.

(** Substitution respects *equality* of context morphisms *)
Local Definition subst_equal : Closure.system (judgement_total Σ).
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
  - refine (Family.adjoin (_ + _ + _) _).
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
    (* the judgement holds over Γ *)
    + exists (Judgement.form_hypothetical (form_object cl)).
      exists Γ.
      exact hjfi.
 (* conclusion: *)
  - exists (Judgement.form_hypothetical (form_equality cl)).
    exists Γ'.
    cbn. intros [i | ].
    + (* boundry and LHS *)
      exact (substitute f (hjfi i)).
    + (* RHS *)
      exact (substitute f' (hjfi None)).
Defined.

Local Definition substitution : Closure.system (judgement_total Σ)
  := subst_apply + subst_equal.

End Substitution.

Section HypotheticalStructuralRules.

(* Hypothetical structural rules:

  - var rule
  - equality rules

*)

(* The variable rule:

  |– A type
  -----------
  x:A |– x:A

*)

Local Definition variable : Closure.system (judgement_total Σ).
Proof.
  apply FlatRule.closure_system.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type , shape_empty σ )    (* [ A ] *)
    >] : arity _).
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
    + refine (raw_variable _).
      apply (plusone_one _ _ (shape_is_extend _ _)).
    + exact [M/ A /].
Defined.


Section Equality.

(* rule tyeq_refl
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Local Definition tyeq_refl : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ )    (* [ A ] *)
    >] : arity _).
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

(* rule tyeq_sym
   ⊢ A ≡ B
--------------
   ⊢ B ≡ A
*)

Local Definition tyeq_sym : flat_rule Σ.
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ )    (* [ A ] *)
    ; (class_type, shape_empty σ )    (* [ B ] *)
    >] : arity _).
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

(* rule tyeq_tran
  ⊢ A ≡ B     ⊢ B ≡ C
-----------------------
       ⊢ A ≡ C
*)

Local Definition tyeq_tran : flat_rule Σ.
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

(* rule tmeq_refl
  ⊢ u : A
-----------
⊢ u ≡ u : A
*)

Local Definition tmeq_refl : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    >] : arity _).
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

(* rule tmeq_sym
   ⊢ u ≡ v : A
----------------
   ⊢ v ≡ u : A
*)

Local Definition tmeq_sym : flat_rule Σ.
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

(* rule tmeq_tran
  ⊢ u ≡ v : A     ⊢ v ≡ w : A
-------------------------------
         ⊢ u ≡ w : A
*)

Local Definition tmeq_tran : flat_rule Σ.
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

(* rule term_convert

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)

Local Definition term_convert : flat_rule Σ.
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

(* rule tmeq_convert

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u, u' : A
 ⊢ u = u' : A
-------------
 ⊢ u = u' : B
*)

Local Definition tmeq_convert : flat_rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, shape_empty σ)    (* [ A ] *)
    ; (class_type, shape_empty σ)    (* [ B ] *)
    ; (class_term, shape_empty σ)    (* [ u ] *)
    ; (class_term, shape_empty σ)    (* [ u' ] *)
    >] : arity _).
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

Local Definition equality : family (rule (judgement_total Σ)) :=
  Family.bind
    [< tyeq_refl
    ; tyeq_sym
    ; tyeq_tran
    ; tmeq_refl
    ; tmeq_sym
    ; tmeq_tran
    ; term_convert
    ; tmeq_convert
    >]
    FlatRule.closure_system.

End Equality.

End HypotheticalStructuralRules.

Definition structural_rule : Closure.system (judgement_total Σ)
  := context + substitution + variable + equality.

(* TODO: add Haskell-style >= notation for bind? *)

End StructuralRules.

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
        (Family.fmap (Closure.fmap (Judgement.fmap_judgement_total f)) (structural_rule Σ))
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
        refine (inl (inl (inl (Some _)))).
        exists (Context.fmap f ΓA.1).
        exact (Expression.fmap f ΓA.2).
      + cbn. apply Closure.rule_eq.
        * simple refine (Family.eq _ _). { apply idpath. }
          cbn. intros [ [ [] | ] | ].
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
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_one _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Substitution.fmap_rename.
          -- intros x. cbn in x.
             eapply concat. { refine (plusone_comp_inj _ _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_inj _ _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Substitution.fmap_rename.
    - (* empty context *)
      exists (inl (inl (inl None))).
      cbn. apply Closure.rule_eq.
      * simple refine (Family.eq _ _). { apply idpath. }
        intros [].
      * cbn. apply (ap (fun x => (_; x))).
        apply (ap (Build_raw_context _)).
        apply path_forall. refine (empty_rect _ shape_is_empty _).
    - (* substitution *)
      destruct c2 as [ Γ [Γ' [g [hjf hjfi]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inl _)))).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.map_adjoin. }
          apply ap011.
          -- unfold Family.fmap.
            apply ap, path_forall; intros i.
            apply (ap (fun x => (_; x))).
            apply (ap (fun x => (_; x))).
            apply path_forall. intros [ [ [] | ] | ].
            ++ refine (fmap_substitute _ _ _).
            ++ apply idpath.
          -- apply idpath.
          (* Family_fmap_adjoin *)
        * apply (ap (fun x => (_; x))). cbn.
          apply (ap (fun x => (_; x))).
          apply path_forall. intros i.
          unfold Judgement.fmap_hypothetical_judgement.
          refine (fmap_substitute _ _ _)^.
    - (* substitution equality *)
      destruct c3 as [ Γ [Γ' [g [g' [hjf hjfi]]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inr _)))).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists (fmap_raw_context_map f g').
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + admit.
    - (* var rule *)
      simple refine (inl (inr _) ; _); admit.
    - (* equality rules *)
      simple refine (inr _; _); admit.
      (* Thest last two should be doable cleanly by the same lemmas
      used for logical rules in [fmap] below, once that’s done. *)
  Admitted.

End StructuralRuleMap.