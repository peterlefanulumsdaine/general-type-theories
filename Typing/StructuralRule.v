From HoTT Require Import HoTT.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.RawRule.

(**
  This module defines the _standard structural rules_ — the rules which are not
  specified separately for every type theory, but are always provided
  automatically. These fall into several groups:

  - variable-renaming rules: [rename]
  - substitution rules: [subst_apply], [subst_equal]
  - variable rule: [variable_rule]
  - equality rules:
      [tyeq_refl, tyeq_sym, tyeq_trans,
      tmeq_refl, tmeq_sym, tmeq_trans,
      term_convert, tmeq_convert].

  All of the above are then collected as a single family [structural_rule].

  Each rule, e.g. [variable_rule] — which formally is not just a single rule,
  but a family of rules, one for each raw context [Γ] and position [i] of it
  — has two things one might want to call [variable_rule]:

  - the definition of it as a family of rules;
  - the access function picking it out in the family [structural_rule].

  We use [variable_rule] for the access function, and call the family
  [variable_rule_instance], since an element of the family is a specific
  instance of the rule.  So when using this rule in a derivation, one will first
  say [apply variable_rule] to select the context extension rule, and then
  specify the particular instance desired, i.e. the earlier context and the type
  to extend by.

  (An alternative convention could be to use [variable_rule] for the family,
  and [select_variable_rule] or similar for the access function.)
*)


Section StructuralRules.

Context {σ : scope_system}.
Context (Σ : signature σ).

Section RenamingRules.
(** Renaming of variables:

given a variable-renaming f : Γ -> Δ respecting types up to literal sytnactic
equality (e.g. a weakening), if J is derivable over Γ, then f_* J is derivable
over Δ.

  Γ |- J   [J any hypothetical judgement over Γ]
  -------------------- [f : Γ -> Γ' a renaming respcting types]
  Γ' |- f_* J

This is not a traditional rule.  We need it since, in our setup, instantiations
of raw rules will always have conclusion context scope of the form γ+δ, where
δ is the conclusion context scope of the raw rule; this lets us go from such
conclusions to arbitrary contexts.

The specific instances we really use are isomorphisms of the form γ <~> γ+0 and
(γ+δ)+χ <~> γ+(δ+χ), used for instance in the instantiation of derivations,
Over some specific scope systems, e.g. de Bruijn scopes, these isomorphisms are
identities, so this rule should never be required over such scope systems.
*)

(* TODO: naming of this rule not ideal.  Keep seeking better options? *)
(* TODO: would it work more cleanly if the direction of this rule was reversed? *)
(* TODO: add restriction to equivalences! *)
Definition rename_instance : Closure.system (judgement Σ).
Proof.
  exists { Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { f : typed_renaming Γ Γ'
    & hypothetical_judgement Σ Γ}}}.
  intros [Γ [Γ' [f J]]]. split.
  - (* premises: *)
    refine [< _ >]. exists Γ; exact J.
  - (* conclusion: *)
    exists Γ'. exact (rename_hypothetical_judgement f J).
Defined.

End RenamingRules.

Section SubstitutionRules.

(** General substitution along (weakly typed) substitutions:

 [for each i in Γ,
    either “f acts trivially at i”, i.e.[f i = x_j] and [Γ' j = f^* Γ i],
    _or_ have a premise: ]
  Γ' |- f i : f^* (Γ i)
  Γ |- J   [for J any hypothetical judgement]
  --------------------
  Γ' |- f^*J

  The idea is that typically, substitution only acts non-trivially on some detachable part of the context; and typechecking is only required for this non-trivial part.
*)

Definition subst_apply_instance : Closure.system (judgement Σ).
Proof.
  exists { Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & hypothetical_judgement Σ Γ
    * { f : raw_substitution Σ Γ' Γ
    & forall i : Γ, option
             { j : Γ' & (f i = raw_variable j) * (Γ' j = substitute f (Γ i)) }
    }}}.
  intros [Γ [Γ' [J [f f_triv]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin _ _).
    (* all components of [f] are suitably typed: *)
    + exists {i : Γ & is_none (f_triv i)}.
      intros [i _]. refine [! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* the target judgement holds over Γ *)
    + exists Γ; exact J.
  (* conclusion: *)
  - exists Γ'.
    exact (substitute_hypothetical_judgement f J).
Defined.

(** Substitution respects *equality* of context morphisms:

  Γ' |- f(x) = g(x) : A   [for each x in Γ, A := type of x in Γ]
  Γ |- J   [for J any hypothetical object judgement]
  --------------------
  Γ' |- f^*J = g^*J  [ over f* of boundary of J ]
 *)
Definition subst_equal_instance : Closure.system (judgement Σ).
Proof.
  exists {   Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { fg : raw_substitution Σ Γ' Γ * raw_substitution Σ Γ' Γ
    & (forall i:Γ, option
           { j : Γ' & ((fst fg i = raw_variable j)
                      * (snd fg i = raw_variable j))
                      * ((Γ' j = substitute (fst fg) (Γ i))
                      * (Γ' j = substitute (snd fg) (Γ i)))})
    * { cl : syntactic_class
        & hypothetical_judgement_expressions Σ (form_object cl) Γ}}}}.
  intros [Γ [Γ' [[f g] [fg_triv [cl J]]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin _ _).
    (* the target judgement holds over Γ *)
    2: { exists Γ, (form_object cl); exact J. }
    (* remaning premises say fg forms a “weakly equal pair”,
     i.e. for each index i on which fg does not act trivially,
     [f i] and [g i] are each well-typed and are equal. *)
    eapply (@Family.bind Γ).
    { exists {i : Γ & is_none (fg_triv i) }.
      intros [i _]; exact i. }
    intros i. refine [< _ ; _ ; _ >]; exists Γ'.
    * exact [! Γ' |- f i ; substitute f (Γ i) !].
    * exact [! Γ' |- g i ; substitute g (Γ i) !].
    * exact [! Γ' |- f i ≡ g i ; substitute f (Γ i) !].
  (* conclusion: *)
  - exists Γ'.
    simple refine (substitute_equal_hypothetical_judgement f g _ _).
    { refine (Build_hypothetical_judgement _ J). }
    apply tt.
Defined.

Definition substitution_instance : Closure.system (judgement Σ)
  := subst_apply_instance + subst_equal_instance.

End SubstitutionRules.

Section HypotheticalStructuralRules.

(* Hypothetical structural rules:

  - var rule
  - equality rules

*)

(* The general variable rule:

  Γ |- A type
  ------------- (x in Γ, A := type of x in Γ)
  Γ |- x : A

*)

Definition variable_instance : Closure.system (judgement Σ).
Proof.
  exists { Γ : raw_context Σ & Γ }.
  intros [Γ x]. set (A := Γ x). split.
  (* premises *)
  - exact [< [! Γ |- A !] >].
  (*conclusion *)
  - exact [! Γ |- (raw_variable x) ; A !].
Defined.

Section Equality.
(** The equality structural rules can all be specified as raw rules over the empty signature.

(One could specify them directly over arbitrary signatures, but then one would have to prove naturality for them afterwards.)*)

(* rule tyeq_refl
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Definition tyeq_refl_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ )    (* [ A ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (A := tt : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A type *)
      simple refine [! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
  (* Conclusion : ⊢ A ≡ A *)
  - simple refine [! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ A /].
Defined.

(* rule tyeq_sym
   ⊢ A ≡ B
--------------
   ⊢ B ≡ A
*)

Definition tyeq_sym_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ )    (* [ A ] *)
    ; (class_type, scope_empty σ )    (* [ B ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (B := None : Metas).
  pose (A := Some tt : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
  (* Conclusion : ⊢ B ≡ A *)
  - simple refine [! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ B /].
    + exact [M/ A /].
Defined.

(* rule tyeq_trans
  ⊢ A ≡ B     ⊢ B ≡ C
-----------------------
       ⊢ A ≡ C
*)

Definition tyeq_trans_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity / metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ )    (* [ A ] *)
    ; (class_type, scope_empty σ )    (* [ B ] *)
    ; (class_type, scope_empty σ )    (* [ C ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (C := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ >].
    + (* Premise ⊢ A ≡ B *)
      simple refine [! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ B ≡ C *)
      simple refine [! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ B /].
      * exact [M/ C /].
  (* Conclusion : ⊢ A ≡ C *)
  - simple refine [! _ |- _ ≡ _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ C /].
Defined.

(* rule tmeq_refl
  ⊢ u : A
-----------
⊢ u ≡ u : A
*)

Definition tmeq_refl_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ)    (* [ A ] *)
    ; (class_term, scope_empty σ)    (* [ u ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (A := Some tt : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u : A type *)
      simple refine [! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion : ⊢ u ≡ u : A *)
  - simple refine [! _ |- _ ≡ _ ; _ !].
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

Definition tmeq_sym_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ)    (* [ A ] *)
    ; (class_term, scope_empty σ)    (* [ u ] *)
    ; (class_term, scope_empty σ)    (* [ v ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (v := None : Metas).
  pose (u := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ >].
    + (* Premise ⊢ u ≡ v : A type *)
      simple refine [! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
  (* Conclusion : ⊢ v ≡ u : A *)
  - simple refine [! _ |- _ ≡ _ ; _ !].
    + exact [::].
    + exact [M/ A /].
    + exact [M/ v /].
    + exact [M/ u /].
Defined.

(* rule tmeq_trans
  ⊢ u ≡ v : A     ⊢ v ≡ w : A
-------------------------------
         ⊢ u ≡ w : A
*)

Definition tmeq_trans_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ)    (* [ A ] *)
    ; (class_term, scope_empty σ)    (* [ u ] *)
    ; (class_term, scope_empty σ)    (* [ v ] *)
    ; (class_term, scope_empty σ)    (* [ w ] *)
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
      simple refine [! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ u /].
      * exact [M/ v /].
    + (* Premise ⊢ v ≡ w : A type *)
      simple refine [! _ |- _ ≡ _ ; _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ v /].
      * exact [M/ w /].
  (* Conclusion : ⊢ u ≡ w : A *)
  - simple refine [! _ |- _ ≡ _ ; _ !].
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

Definition term_convert_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ)    (* [ A ] *)
    ; (class_type, scope_empty σ)    (* [ B ] *)
    ; (class_term, scope_empty σ)    (* [ u ] *)
    >] : arity _).
  (* Name the symbols. *)
  pose (u := None : Metas).
  pose (B := Some None : Metas).
  pose (A := Some (Some tt) : Metas).
  exists Metas.
  (* Premise *)
  - refine [< _ ; _ ; _ ; _ >].
    + (* Premise ⊢ A type *)
      simple refine [! _ |- _ !].
      * exact [::].
      * exact [M/ A /].
    + (* Premise ⊢ B type *)
      simple refine [! _ |- _ !].
      * exact [::].
      * exact [M/ B /].
    + (* Premise ⊢ A ≡ B *)
      simple refine [! _ |- _ ≡ _ !].
      * exact [::].
      * exact [M/ A /].
      * exact [M/ B /].
    + (* Premise ⊢ u : A *)
      simple refine [! _ |- _ ; _ !].
      * exact [::].
      * exact [M/ u /].
      * exact [M/ A /].
  (* Conclusion: ⊢ u : B *)
  - simple refine [! _ |- _ ; _ !].
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

Definition tmeq_convert_rule : raw_rule (Signature.empty σ).
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [<
      (class_type, scope_empty σ)    (* [ A ] *)
    ; (class_type, scope_empty σ)    (* [ B ] *)
    ; (class_term, scope_empty σ)    (* [ u ] *)
    ; (class_term, scope_empty σ)    (* [ u' ] *)
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
      exact [! [::] |- [M/ A /] !].
    + (* Premise ⊢ B type *)
      exact [! [::] |- [M/ B /] !].
    + (* Premise ⊢ A ≡ B *)
      exact [! [::] |- [M/ A /] ≡ [M/ B /] !].
    + (* Premise ⊢ u : A *)
      exact [! [::] |- [M/ u /] ; [M/ A /] !].
    + (* Premise ⊢ u' : A *)
      exact [! [::] |- [M/ u' /] ; [M/ A /] !].
    + (* Premise ⊢ u ≡ u' : A *)
      exact [! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ A /] !].
  (* Conclusion: ⊢ u ≡ u' : B *)
  - exact [! [::] |- [M/ u /] ≡ [M/ u' /] ; [M/ B /] !].
Defined.

Definition equality_raw_rule : family (raw_rule (Signature.empty σ))
  := [< tyeq_refl_rule
    ; tyeq_sym_rule
    ; tyeq_trans_rule
    ; tmeq_refl_rule
    ; tmeq_sym_rule
    ; tmeq_trans_rule
    ; term_convert_rule
    ; tmeq_convert_rule
    >].

Definition equality_instance : family (rule (judgement Σ))
  := Family.bind
       (Family.fmap (RawRule.fmap (Signature.empty_rect _)) equality_raw_rule)
       RawRule.closure_system.

End Equality.

End HypotheticalStructuralRules.

Definition structural_rule_without_subst : Closure.system (judgement Σ)
  := rename_instance + variable_instance + equality_instance.

Definition structural_rule : Closure.system (judgement Σ)
  := structural_rule_without_subst + substitution_instance.

End StructuralRules.

Section StructuralRuleAccessors.
  (** Access functions, for selcting structural rules in derivations *)

  (* Note: in a separate section just so that [Σ] can be declared as implicit
   argument for them all, rather than needing to be all redeclared with
   [Arguments] afterwards. *)

Context {σ : scope_system} {Σ : signature σ}.

Local Definition rename : rename_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inl i)).
Definition subst_apply : subst_apply_instance Σ -> structural_rule Σ
  := fun i => inr (inl i).
Definition subst_equal : subst_equal_instance Σ -> structural_rule Σ
  := fun i => inr (inr i).
Definition variable_rule : variable_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inr i)).
Definition equality_rule : equality_instance Σ -> structural_rule Σ
  := fun i => inl (inr i).
Definition tyeq_refl : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tyeq_refl_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some (Some (Some (Some (Some (Some tt)))))) ; i).
Definition tyeq_sym : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tyeq_sym_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some (Some (Some (Some (Some None))))) ; i).
Definition tyeq_trans : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tyeq_trans_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some (Some (Some (Some None)))) ; i).
Definition tmeq_refl : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tmeq_refl_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some (Some (Some None))) ; i).
Definition tmeq_sym : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tmeq_sym_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some (Some None)) ; i).
Definition tmeq_trans : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tmeq_trans_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some (Some None) ; i).
Definition term_convert : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) term_convert_rule)
    -> structural_rule Σ
  := fun i => equality_rule (Some None ; i).
Definition tmeq_convert : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) tmeq_convert_rule)
    -> structural_rule Σ
  := fun i => equality_rule (None ; i).

(* TODO: for testing! remove this, or replace the above with this *)
Definition term_convert' : RawRule.closure_system
      (RawRule.fmap (Signature.empty_rect _) term_convert_rule)
    -> equality_instance Σ
  := fun i => (Some None ; i).

End StructuralRuleAccessors.

Section StructuralRuleInd.

Context {σ : scope_system}.
Context {Σ : signature σ}.

Definition structural_rule_rect
  : forall (P : structural_rule Σ -> Type),
     (forall i_rename : rename_instance Σ, P (rename i_rename))
  -> (forall i_sub_ap : subst_apply_instance Σ, P (subst_apply i_sub_ap))
  -> (forall i_sub_eq : subst_equal_instance Σ, P (subst_equal i_sub_eq))
  -> (forall i_var : variable_instance Σ, P (variable_rule i_var))
  -> (forall i_eq : equality_instance Σ, P (equality_rule i_eq))
  -> forall s : structural_rule Σ, P s.
Proof.
  intros P ? ? ? ? ? s.
  destruct s as
      [ [ [ i_rename
          | i_var ]
        | i_eq ]
      | [i_sub_ap | i_sub_eq] ]
  ; eauto.
Defined.

Definition equality_instance_rect :
  forall (P : structural_rule Σ -> Type),
       (forall i_tyeq_refl : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tyeq_refl_rule),
         P (tyeq_refl i_tyeq_refl))
    -> (forall tyeq_sym_rule : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tyeq_sym_rule),
         P (tyeq_sym tyeq_sym_rule))
    -> (forall tyeq_trans_rule : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tyeq_trans_rule),
         P (tyeq_trans tyeq_trans_rule))
    -> (forall i_tmeq_refl : RawRule.closure_system
          (RawRule.fmap (Signature.empty_rect _) tmeq_refl_rule),
         P (tmeq_refl i_tmeq_refl))
    -> (forall i_tmeq_sym : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tmeq_sym_rule),
         P (tmeq_sym i_tmeq_sym))
    -> (forall i_tmeq_trans : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tmeq_trans_rule),
         P (tmeq_trans i_tmeq_trans))
    -> (forall i_term_convert : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) term_convert_rule),
         P (term_convert i_term_convert))
    -> (forall i_tmeq_convert : RawRule.closure_system
           (RawRule.fmap (Signature.empty_rect _) tmeq_convert_rule),
         P (tmeq_convert i_tmeq_convert))
  -> forall e : equality_instance Σ, P (equality_rule e).
Proof.
  intros P X X0 X1 X2 X3 X4 X5 X6.
  intros [ index element ].
  repeat destruct index as [ index | ];
  try destruct index; eauto.
Defined.

End StructuralRuleInd.

(** For using the structural rules conveniently in derivations, we provide functions [derive_rename], [derive_variable] etc below.

To make those functions usable not just over the standard structural rules but also over the subst-free structural rules and other variants, we base them on a type-class [has_derivable].  [has_derivable R C] should be thought of as: the structural rules [R] have a canonical inclusion into the closure system [C], and so are available for derivaitons there. *)

Section Structural_Rule_Classes.

  Context `{H_Funext : Funext}
        {σ : scope_system} {Σ : signature σ}.

  Class has_derivable (Rs C : Closure.system (judgement Σ))
    := { use_derivable : Closure.map Rs C }.

  Global Arguments use_derivable _ {_ _}.

  Global Instance trivial_has_derivable {Rs}
    : has_derivable Rs Rs.
  Proof.
    constructor. apply Closure.idmap.
  Defined.

  Global Instance sum_left_has_derivable {Rs}
      {C D : Closure.system (judgement Σ)}
      `{ H_C : has_derivable Rs C }
    : has_derivable Rs (C + D).
  Proof.
    constructor.
    eapply Closure.compose.
    2: { apply Closure.inl. }
    apply (use_derivable Rs).
  Defined.

  Global Instance sum_right_has_derivable {Rs}
      {C D : Closure.system (judgement Σ)}
      `{ H_D : has_derivable Rs D }
    : has_derivable Rs (C + D).
  Proof.
    constructor.
    eapply Closure.compose.
    2: { apply Closure.inr. }
    apply (use_derivable Rs).
  Defined.

End Structural_Rule_Classes.

Section Renaming_Interface.
  (** Interface to the renaming structural rule,
   and some frequently-used special cases. *)

  Context
    `{H_Funext : Funext}
    {σ : scope_system} {Σ : signature σ}
    {T : Closure.system (judgement Σ)}
    `{H_T : has_derivable _ _ (rename_instance Σ) T}
    {H : family (judgement Σ) }.

  Lemma derive_rename
      (Γ Γ' : raw_context Σ)
      (f : typed_renaming Γ Γ')
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation T H (Build_judgement Γ J)
    -> Closure.derivation T H
      (Build_judgement Γ' (rename_hypothetical_judgement f J)).
  Proof.
    intros D.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { exists Γ, Γ', f; exact J. }
    { apply idpath. }
    { intros; apply D. }
  Defined.

  Lemma derive_rename'
      (J J' : judgement Σ)
      (f : typed_renaming
             (context_of_judgement J') (context_of_judgement J))
      (e : hypothetical_part J
           = rename_hypothetical_judgement f (hypothetical_part J'))
    : Closure.derivation T H J'
    -> Closure.derivation T H J.
  Proof.
    intros D.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { refine (_;(_;(f;_))). exact J'. }
    { apply (ap (Build_judgement _)), inverse, e. }
    { intros; apply D. }
  Defined.

  Lemma derive_renaming_along_equiv
      (J : judgement Σ)
      {γ' : σ} (e : γ' <~> scope_of_judgement J)
    : Closure.derivation T H J
    -> Closure.derivation T H (Judgement.rename J e).
  Proof.
    simple refine (derive_rename' _ _ _ _).
    - apply Context.typed_renaming_to_rename_context.
    - apply idpath.
  Defined.

  Lemma derive_from_renaming_along_equiv
      (J : judgement Σ)
      {γ' : σ} (e : γ' <~> scope_of_judgement J)
    : Closure.derivation T H (Judgement.rename J e)
      -> Closure.derivation T H J.
  Proof.
    simple refine (derive_rename' _ _ _ _).
    - apply Context.typed_renaming_from_rename_context.
    - apply inverse, eq_by_expressions_hypothetical_judgement; intros s.
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply rename_idmap. }
      apply (ap_2back Expression.rename), path_forall, (eisretr e).
  Defined.

(** A particularly common case: renaming along the equivalence [ Γ <~> Γ+0 ].

This arises with instantiations of raw rules: their conclusion is typically
over a context [ Γ + 0 ], not just [ Γ ] as one would want. *)

  Definition derive_reindexing_to_empty_sum
      (J : judgement Σ)
    : Closure.derivation T H J
    -> Closure.derivation T H
         (Judgement.rename J (equiv_inverse (scope_sum_empty_inl _))).
  Proof.
    apply derive_renaming_along_equiv.
  Defined.

  Definition derive_from_reindexing_to_empty_sum
      {Γ : raw_context Σ}
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation T H
          (Judgement.rename
             (Build_judgement Γ J) (equiv_inverse (scope_sum_empty_inl _)))
    -> Closure.derivation T H (Build_judgement Γ J).
  Proof.
    apply derive_from_renaming_along_equiv.
  Defined.

End Renaming_Interface.

Section Variable_Interface.
  (** Interface to the variable structural rule *)

  Context
    `{H_Funext : Funext}
    {σ : scope_system} {Σ : signature σ}
    {T : Closure.system (judgement Σ)}
    `{H_T : has_derivable _ _ (variable_instance Σ) T}
    {H : family (judgement Σ) }.

  Lemma derive_variable
      (Γ : raw_context Σ) (i : Γ)
      (d_Γi : derivation T H [! Γ |- Γ i !])
    : derivation T H [! Γ |- raw_variable i ; Γ i !].
  Proof.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { exists Γ; exact i. }
    { apply idpath. }
    { intros; assumption. }
  Defined.

  Lemma derive_variable'
      (Γ : raw_context Σ)
      (Je : hypothetical_judgement_expressions Σ (form_object class_term) Γ)
      (J := Build_judgement Γ (Build_hypothetical_judgement _ Je) : judgement Σ)
      (i : Γ)
      (e_tm : Je (@the_boundary_slot
                     (form_object class_term) the_type_slot) = Γ i)
      (e_ty : Je (the_head_slot _) = raw_variable i)
      (d_Γi : derivation T H [! Γ |- Γ i !])
    : derivation T H J.
  Proof.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { exists Γ; exact i. }
    { apply Judgement.eq_by_eta; simpl.
      apply ap, ap2; apply inverse; assumption.
    }
    { intros; assumption. }
  Defined.

End Variable_Interface.
  
Section Substitution_Interface.
  (** Interface to the substitution structural rules *)

  Context
    `{H_Funext : Funext}
    {σ : scope_system} {Σ : signature σ}
    {T : Closure.system (judgement Σ)}
    `{H_T : has_derivable _ _ (substitution_instance Σ) T}
    {H : family (judgement Σ) }.

  Definition derive_subst_apply'
      ( J J' : judgement Σ )
      ( Γ := context_of_judgement J )
      ( Γ' := context_of_judgement J' )
      ( f : raw_substitution Σ Γ' Γ )
      ( e : hypothetical_part J' = substitute_hypothetical_judgement f J)
      ( d_f : forall i,
        ({ j : Γ' & (f i = raw_variable j) * (Γ' j = substitute f (Γ i)) }
        + derivation T H [! Γ' |- f i ; substitute f (Γ i) !])%type)
      ( d_J : derivation T H J)
    : derivation T H J'.
  Proof.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { apply inl.
      exists Γ, Γ'. split. { exact J. } exists f.
      intros i.
      destruct (d_f i) as [ fi_triv | _ ].
      + exact (Some fi_triv).
      + exact None.
    }
    { apply (ap (Build_judgement _)), inverse, e. }
    simpl. intros [ [ i fi_nontriv ] | ].
    - destruct (d_f i) as [ ? | d_fi ].
      + destruct fi_nontriv.
      + apply d_fi.
    - apply d_J.
  Defined.

  Definition derive_subst_apply
      ( Γ Δ : raw_context Σ )
      ( f : raw_substitution Σ Δ Γ )
      ( J : hypothetical_judgement Σ Γ )
      ( d_f : (forall i,
        { j : Δ & (f i = raw_variable j) * (Δ j = substitute f (Γ i)) }
        + derivation T H [! Δ |- f i ; substitute f (Γ i) !])%type)
      ( d_J : derivation T H (Build_judgement Γ J))
    : derivation T H
             (Build_judgement Δ (substitute_hypothetical_judgement f J)).
  Proof.
    srapply derive_subst_apply'.
    1: exists Γ.
    3: apply idpath.
    1, 2: assumption.
  Defined.

  Definition derive_subst_equal'
      ( J J' : judgement Σ )
      ( Γ := context_of_judgement J )
      ( Γ' := context_of_judgement J' )
      ( f g : raw_substitution Σ Γ' Γ )
      ( J_obj : Judgement.is_object J )
      ( e : hypothetical_part J'
            = substitute_equal_hypothetical_judgement f g J J_obj)
      ( d_fg : forall i,
        ({ j : Γ' & ((f i = raw_variable j)
                 * (g i = raw_variable j))
                 * ((Γ' j = substitute f (Γ i))
                 * (Γ' j = substitute g (Γ i))) }
        + (derivation T H [! Γ' |- f i ; substitute f (Γ i) !]
          * derivation T H [! Γ' |- g i ; substitute g (Γ i) !]
          * derivation T H [! Γ' |- f i ≡ g i ; substitute f (Γ i) !]))%type)
      ( d_J : derivation T H (Build_judgement Γ J))
    : derivation T H J'.
  Proof.
    subst Γ; destruct J as [Γ [[cl | cl] J]]; [ | destruct J_obj].
    simpl in *.
    simple refine (Closure.deduce'_via_map (use_derivable _) _ _ _).
    { apply inr.
      exists Γ, Γ', (f, g). refine (_,(cl; J)).
      intros i. destruct (d_fg i) as [ fgi_triv | _ ].
      + exact (Some fgi_triv).
      + exact None.
    }
    { apply (ap (Build_judgement _)), inverse, e. }
    intros [ i | ]; try assumption.
    simpl in i |- *. destruct i as [[i i_nontriv] j].
    destruct (d_fg i) as [ ? | d_fgi ]; destruct i_nontriv.
    recursive_destruct j; apply d_fgi.
  Defined.

  Definition derive_subst_equal
      ( Γ Γ' : raw_context Σ )
      ( f g : raw_substitution Σ Γ' Γ )
      ( J : hypothetical_judgement Σ Γ )
      ( J_obj : Judgement.is_object J )
      ( d_fg : forall i,
        ({ j : Γ' & ((f i = raw_variable j)
                 * (g i = raw_variable j))
                 * ((Γ' j = substitute f (Γ i))
                 * (Γ' j = substitute g (Γ i))) }
        + (derivation T H [! Γ' |- f i ; substitute f (Γ i) !]
          * derivation T H [! Γ' |- g i ; substitute g (Γ i) !]
          * derivation T H [! Γ' |- f i ≡ g i ; substitute f (Γ i) !]))%type)
      ( d_J : derivation T H (Build_judgement Γ J))
    : derivation T H (Build_judgement Γ'
                         (substitute_equal_hypothetical_judgement f g J J_obj)).
  Proof.
    eapply (derive_subst_equal' (Build_judgement Γ J));
      try apply idpath;
      assumption.
  Defined.

End Substitution_Interface.

Section Equality_Interface.
  (** Interface to the equality structural rules *)

  Context
    `{H_Funext : Funext}
    {σ : scope_system} {Σ : signature σ}
    {T : Closure.system (judgement Σ)}
    `{H_ren : has_derivable _ _ (rename_instance Σ) T}
    `{H_eq : has_derivable _ _ (equality_instance Σ) T}
    {H : family (judgement Σ) }.

  Definition derive_tyeq_refl
      (Γ : raw_context Σ) (A : raw_expression Σ class_type Γ)
      (d_A : derivation T H [! Γ |- A !])
    : derivation T H [! Γ |- A ≡ A !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce'_via_map
                            (use_derivable (equality_instance _)) _ _ _).
    { exists (Some (Some (Some (Some (Some (Some (Some tt))))))), Γ.
      intros i; recursive_destruct i. cbn.
      refine (Expression.rename _ A).
      apply scope_sum_empty_inl. }
    { refine (Judgement.eq_by_expressions _ _).
      - intros i. apply @instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          refine (instantiate_binderless_metavariable _).
    }
    intros [].
    refine (transport _ _
                      (derive_reindexing_to_empty_sum _ d_A)).
    apply Judgement.eq_by_expressions.
    - intros i. apply inverse, @instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
        apply inverse, instantiate_binderless_metavariable.
  Defined.

  Definition derive_tyeq_sym
      (Γ : raw_context Σ) (A B : raw_expression Σ class_type Γ)
      (d_AB : derivation T H [! Γ |- A ≡ B !])
    : derivation T H [! Γ |- B ≡ A !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce'_via_map
                             (use_derivable (equality_instance _)) _ _ _).
    { exists (Some (Some (Some (Some (Some (Some None)))))), Γ.
      intros i; recursive_destruct i;
        refine (Expression.rename (scope_sum_empty_inl _) _);
        [ exact A | exact B ].
    }
    { refine (Judgement.eq_by_expressions _ _).
      - apply @instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          apply instantiate_binderless_metavariable.
    }
    intros [].
    refine (transport _ _
                      (derive_reindexing_to_empty_sum _ d_AB)).
    apply Judgement.eq_by_expressions.
    - intros i. apply inverse, @instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
        apply inverse, instantiate_binderless_metavariable.
  Defined.

(* TODO: derive_tyeq_trans *)

  Definition derive_tmeq_refl
      (Γ : raw_context Σ)
      (A : raw_type Σ Γ) (a : raw_term Σ Γ)
      (d_a : derivation T H [! Γ |- a ; A !])
    : derivation T H [! Γ |- a ≡ a ; A !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce'_via_map
                             (use_derivable (equality_instance _)) _ _ _).
    { exists (Some (Some (Some (Some None)))), Γ.
      intros i; recursive_destruct i;
        refine (Expression.rename (scope_sum_empty_inl _) _);
        assumption.
    }
    { refine (Judgement.eq_by_expressions _ _).
      - intros i. apply @instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          refine (instantiate_binderless_metavariable _).
    }
    intros [].
    refine (transport _ _
                      (derive_reindexing_to_empty_sum _ d_a)).
    rapply @Judgement.eq_by_expressions.
    - intros i. apply inverse, @instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
        apply inverse, instantiate_binderless_metavariable.
  Defined.

  Definition derive_tmeq_refl'
      (Γ : raw_context Σ)
      (Je : hypothetical_judgement_expressions Σ (form_equality class_term) Γ)
      (A : raw_type Σ Γ) (a : raw_term Σ Γ)
      (e_A : Je (the_equality_boundary_slot class_term the_type_slot)
             = A)
      (e_lhs : Je (the_lhs_slot _) = a)
      (e_rhs : Je (the_rhs_slot _) = a)
      (d_a : derivation T H [! Γ |- a ; A !])
    : derivation T H (Build_judgement Γ (Build_hypothetical_judgement _ Je)).
  Proof.
    refine (transport _ _ (derive_tmeq_refl _ _ _ d_a)).
    apply Judgement.eq_by_eta; simpl.
    apply ap, ap3; apply inverse; assumption.
  Defined.

(* TODO: derive_tmeq_sym *)

(* TODO: derive_tmeq_trans *)


  (* rule term_convert

     ⊢ A, B type
     ⊢ A ≡ B type
     ⊢ u : A
   -------------
     ⊢ u : B
   *)
  Definition derive_term_convert
      ( Γ : raw_context Σ )
      ( A B : raw_expression Σ class_type Γ )
      ( u : raw_expression Σ class_term Γ )
      ( d_A : derivation T H [! Γ |- A !] )
      ( d_B : derivation T H [! Γ |- B !] )
      ( d_AB : derivation T H [! Γ |- A ≡ B !] )
      ( d_u : derivation T H [! Γ |- u ; A !] )
    : derivation T H [! Γ |- u ; B !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce'_via_map
                             (use_derivable (equality_instance _)) _ _ _).
    { exists (Some None), Γ.
      intros i; recursive_destruct i;
        refine (Expression.rename (scope_sum_empty_inl _) _).
      + exact A.
      + exact B.
      + exact u.
    }
    { refine (Judgement.eq_by_expressions _ _).
      - apply @instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          apply instantiate_binderless_metavariable.
    }
    intros p.
    recursive_destruct p;
      [ set (d := d_A) | set (d := d_B) | set (d := d_AB) | set (d := d_u) ];
      refine (transport _ _ (derive_reindexing_to_empty_sum _ d));
      (apply Judgement.eq_by_expressions;
       [ intros; apply inverse, @instantiate_empty_ptwise
       | intros i; recursive_destruct i;
         apply inverse, instantiate_binderless_metavariable]).
  Defined.

  Definition derive_tmeq_convert
      ( Γ : raw_context Σ )
      ( A B : raw_expression Σ class_type Γ )
      ( u v : raw_expression Σ class_term Γ )
      ( d_A : derivation T H [! Γ |- A !] )
      ( d_B : derivation T H [! Γ |- B !] )
      ( d_AB : derivation T H [! Γ |- A ≡ B !] )
      ( d_u : derivation T H [! Γ |- u ; A !] )
      ( d_v : derivation T H [! Γ |- v ; A !] )
      ( d_uv : derivation T H [! Γ |- u ≡ v ; A !] )
    : derivation T H [! Γ |- u ≡ v ; B !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce'_via_map
                             (use_derivable (equality_instance _)) _ _ _).
    { exists None, Γ.
      intros i; recursive_destruct i;
        refine (Expression.rename (scope_sum_empty_inl _) _).
      + exact A.
      + exact B.
      + exact u.
      + exact v.
    }
    { refine (Judgement.eq_by_expressions _ _).
      - apply @instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          apply instantiate_binderless_metavariable.
    }
    intros p; recursive_destruct p;
      [ set (d := d_A) | set (d := d_B) | set (d := d_AB)
        | set (d := d_u) | set (d := d_v) | set (d := d_uv) ];
      refine (transport _ _ (derive_reindexing_to_empty_sum _ d));
      (apply Judgement.eq_by_expressions;
       [ intros; apply inverse, @instantiate_empty_ptwise
       | intros i; recursive_destruct i;
         apply inverse, instantiate_binderless_metavariable]).
  Defined.

End Equality_Interface.

Section SignatureMaps.

  Context `{H : Funext}.
  Context {σ : scope_system}.

  (** For a given signature map [f] from [Σ] to [Σ'],
     the translations of structural rules of [Σ] are structural rules of [Σ']. *)
  Local Definition fmap
      {Σ Σ' : signature σ}
      (f : Signature.map Σ Σ')
    : Family.map_over (Closure.rule_fmap (Judgement.fmap f))
        (structural_rule Σ)
        (structural_rule Σ').
  Proof.
    repeat apply Family.sum_fmap.
    - (* rename *)
      apply Family.Build_map'.
      intros [Γ [Γ' [α J]]].
      simple refine (_;_).
      + exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_typed_renaming f α).
        exact (fmap_hypothetical_judgement f J).
      + apply Closure.rule_eq.
        * apply idpath.
        * refine (Judgement.eq_by_expressions _ _); intros i.
          -- apply idpath.
          -- apply inverse, fmap_rename.
    - (* var rule *)
      apply Family.Build_map'.
      intros [Γ x].
      simple refine (_;_).
      + exists (Context.fmap f Γ). exact x.
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_singleton. }
          apply ap.
          apply Judgement.eq_by_eta, idpath.
        * apply Judgement.eq_by_eta, idpath.
    - (* equality rules *)
      apply Family.Build_map'.
      intros [r ΓI].
      simple refine (_;_).
      + exists r.
        simple refine (RawRule.closure_system_fmap' f _ ΓI).
        refine (_ @ _). { apply inverse, RawRule.fmap_compose. }
        rapply @ap_1back.
        apply Signature.empty_rect_unique.
      + refine (Family.map_over_commutes
                  (RawRule.closure_system_fmap' f _) _).
    - (* subst_apply *)
      apply Family.Build_map'.
      intros [ Γ [Δ [J [g g_triv]]]].
      simple refine (_;_).
      + exists (Context.fmap f Γ).
        exists (Context.fmap f Δ).
        split. { exact (Judgement.fmap_hypothetical_judgement f J). }
        exists (raw_substitution_fmap f g).
        intros i. refine (fmap_option _ (g_triv i)).
        intros [j [e_gi e_Δi]].
        exists j; split.
        * refine (ap (Expression.fmap f) e_gi).
        * eapply concat. { simpl. apply ap, e_Δi. }
          apply fmap_substitute.
      + apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap2; try apply idpath.
          simple refine (Family.eq _ _).
          { apply sigma_type_eq; intros i.
            apply inverse, is_none_fmap. }
          intros i; simpl in i; rewrite equiv_path_sigma_type_eq.
          refine (Judgement.eq_by_expressions _ _);
            intros j; try apply idpath; recursive_destruct j;
            try apply idpath; apply fmap_substitute.
        * refine (Judgement.eq_by_expressions _ _);
            intros; try apply idpath.
          refine (fmap_substitute _ _ _)^.
    - (* subst_equal *)
      apply Family.Build_map'.
      intros [ Γ [Γ' [[g h] [gh_triv [jf hj]]]]].
      simple refine (_;_).
      + exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (raw_substitution_fmap f g, raw_substitution_fmap f h).
        split.
        2: { exists jf. intro; apply (Expression.fmap f), hj. }
        intros i. refine (fmap_option _ (gh_triv i)).
        simpl; intros [ j [[e_g e_h] [e_gΓ e_hΓ]]].
        exists j; split.
        * split; [ set (e := e_g) | set (e := e_h) ];
            exact (ap (Expression.fmap _) e).
        * split; [ set (e := e_gΓ) | set (e := e_hΓ) ];
          refine (ap _ e @ _);
          apply fmap_substitute.
      + apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap2; try apply idpath.
          eapply concat. { apply Family.fmap_bind. }
          apply ap2.
          -- simple refine (Family.eq _ _).
            { apply sigma_type_eq; intros i. apply inverse, is_none_fmap. }
            intros i; rewrite equiv_path_sigma_type_eq; apply idpath.
          -- apply path_forall; intros i.
            repeat rewrite Family.fmap_adjoin.
            repeat apply ap2;
            try (rewrite Family.fmap_singleton; apply ap);
            refine (Judgement.eq_by_expressions _ _);
            intros j; recursive_destruct j;
              try apply idpath; apply fmap_substitute.
        * refine (Judgement.eq_by_expressions _ _);
            intros; try apply idpath.
          recursive_destruct i; refine (fmap_substitute _ _ _)^.
  Defined.

End SignatureMaps.

Section Instantiation.

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  (** Given a raw rule [R] over a signature [Σ], an arity [a] specifying a
  metavariable extension, and an instantiation [I] of [a] in [Σ] over some
  context [Γ],

  any instance of [R] over the extended signature [extend Σ a] gets translated
  under [I] into an instance of [R] over [Σ], modulo renaming.

  Note: this can’t be in [Typing.RawRule], since it uses the structural rules,
  specifically the rule for renaming along scope isomorphisms.  Morally perhaps
  that should be seen as more primitive than the other structural rules, and be
  baked into the notion of derivations earlier, as e.g. “closure systems on a
  groupoid”.  (Indeed, if the scope system is univalent then this rule _will_
  come for free.)
  *)
  Definition instantiate_raw_rule_closure_system
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : raw_rule Σ)
    : Closure.map_over
        (Judgement.instantiate Γ I)
        (RawRule.closure_system (RawRule.fmap include_symbol r))
        (structural_rule Σ + RawRule.closure_system r)%family.
  Proof.
    intros [Δ J].
    (* The derivation essentially consists of the instance
     [(Context.instantiate _ I Δ
     ; instantiate_instantiation I J)]
     of the same raw rule, wrapped in renamings along [scope_assoc].
     *)
    simple refine (derive_rename' _ _ _ _ _).
    4: simple refine (Closure.deduce' _ _ _);
       [ apply inr;
         exists (Context.instantiate _ I Δ);
         exact (instantiate_instantiation I J)
       | apply idpath | ].
    { apply Context.instantiate_instantiate_ltor. }
    { apply instantiate_instantiate_hypothetical_judgement. }
    intros p.
    simple refine (derive_rename' _ _ _ _ _).
    4: refine (Closure.hypothesis _ _ _); apply p.
    { apply Context.instantiate_instantiate_rtol. }
    apply eq_by_expressions_hypothetical_judgement; intros i.
    apply instantiate_instantiate_expression.
  Defined.

(** Structural rules in a metavariable extension,
  translated under an instantiation,
  can always be derived from structural rules over the base signature.

  Essentially, any structural rule gets translated into an instance of the same structural rule, possibly wrapped in a variable-renaming to reassociate iterated context extensions *)
  Local Definition instantiate
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
    : Closure.map_over (@Judgement.instantiate σ _ Σ Γ I)
        (structural_rule (Metavariable.extend Σ a))
        (structural_rule Σ).
  Proof.
    unfold Closure.map_over.
    apply structural_rule_rect.
    - (* rename*)
      intros [Δ [Δ' [α J]]].
      simple refine (derive_rename' _ _ _ _ _).
      4: { refine (Closure.hypothesis _ _ _). exact tt. }
      { apply instantiate_typed_renaming, α. }
      apply eq_by_expressions_hypothetical_judgement; intro.
      apply instantiate_rename.
    - (* subst_apply *)
      intros [Δ [Δ' [J [f f_triv]]]].
      simple refine (derive_subst_apply' _ _ _ _ _ _).
      + apply (Judgement.instantiate Γ I).
        exists Δ. exact J.
      + exact (instantiate_raw_substitution I f).
      + apply instantiate_substitute_hypothetical_judgement.
      + simpl. refine (coproduct_rect scope_is_sum _ _ _).
        * intros i; simpl.
          unfold instantiate_raw_substitution.
          repeat rewrite coproduct_comp_inj1.
          apply inl.
          exists (coproduct_inj1 scope_is_sum i).
          split; try apply idpath.
          eapply concat. { rapply coproduct_comp_inj1. }
          eapply concat. { apply inverse, substitute_raw_variable. }
          eapply concat. 2: { apply inverse, substitute_rename. }
          apply (ap_2back substitute), path_forall.
          intros j; apply inverse. rapply coproduct_comp_inj1.
        * intros i.
          destruct (some_or_is_none (f_triv i))
                     as [ [j [e_fi e_Γ'j]]| fi_nontriv ].
          -- apply inl.
            exists (coproduct_inj2 scope_is_sum j); split;
              refine (coproduct_comp_inj2 _ @ _).
            ++ eapply concat. { apply ap, e_fi. }
              apply idpath.
            ++ eapply concat. { apply ap, e_Γ'j. }
              eapply concat. { apply instantiate_substitute. }
              apply ap, inverse. rapply coproduct_comp_inj2.
          -- apply inr.
            simple refine (Closure.hypothesis' _ _).
            { apply Some. exists i. apply fi_nontriv. }
            apply Judgement.eq_by_expressions.
            { intros; apply idpath. }
            intros j; recursive_destruct j; simpl.
            ++ repeat rewrite coproduct_comp_inj2.
              apply instantiate_substitute.
            ++ unfold instantiate_raw_substitution.
              apply inverse; rapply coproduct_comp_inj2.
      + simple refine (Closure.hypothesis' _ _).
        { apply None. }
        apply idpath.
    - (* subst_equal *)
      simpl. intros [Δ [Δ' [[f g] [fg_triv [cl J]]]]].
      simple refine (derive_subst_equal' _ _ _ _ _ _ _ _).
      + apply (Judgement.instantiate Γ I).
        exists Δ. exact (Build_hypothetical_judgement _ J).
      + exact (instantiate_raw_substitution I f).
      + exact (instantiate_raw_substitution I g).
      + constructor.
      + apply eq_by_expressions_hypothetical_judgement.
        intros i; destruct cl; recursive_destruct i;
        apply instantiate_substitute.
      (* TODO: abstract as [instantiate_substitute_equal_hypothetical_judgement]? *)
      + simpl. refine (coproduct_rect scope_is_sum _ _ _).
        * intros i; simpl.
          unfold instantiate_raw_substitution.
          repeat rewrite coproduct_comp_inj1.
          apply inl.
          exists (coproduct_inj1 scope_is_sum i).
          repeat split; try apply idpath;
            refine (coproduct_comp_inj1 _ @ _);
            refine ((substitute_raw_variable _ _)^ @ _);
            refine (_ @ (substitute_rename _ _ _)^);
            apply (ap_2back substitute), path_forall;
            intros j; apply inverse; rapply coproduct_comp_inj1.
        * intros i.
          destruct (some_or_is_none (fg_triv i)) as [ fgi_triv | fgi_nontriv ].
          -- apply inl.
            destruct fgi_triv as [j [[e_fi e_gi] [e_fΓi e_gΓi]]].
            exists (coproduct_inj2 scope_is_sum j); split.
            ++ split; refine (coproduct_comp_inj2 _ @ _);
              (refine (ap _ _ @ _); [ try eassumption | ]); apply idpath.
            ++ split; refine (coproduct_comp_inj2 _ @ _);
                 refine (_ @ ap _ (coproduct_comp_inj2 _)^);
                 refine (_ @ instantiate_substitute _ _ _);
                 apply ap; assumption.
          -- apply inr.
            repeat split;
            (simple refine (Closure.hypothesis' _ _);
            [ apply Some; exists (i; fgi_nontriv) | ]);
            [ apply Some, Some, tt | | apply Some, None | | apply None | ];
            apply Judgement.eq_by_eta;
            unfold instantiate_raw_substitution;
              repeat rewrite coproduct_comp_inj2; simpl;
              rewrite instantiate_substitute;
              apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        { apply None. }
        apply idpath.
    - (* variable_rule *)
      intros [Δ i]; simpl.
      simple refine (derive_variable' _ _ _ _ _ _); try apply idpath.
      { apply inverse; refine (coproduct_comp_inj2 _). }
      simple refine (Closure.hypothesis' _ _).
      + exact tt.
      + apply Judgement.eq_by_expressions; intros j; try apply idpath.
        recursive_destruct j; apply inverse; refine (coproduct_comp_inj2 _).
    - (* equality_rule *)
      intros i_eq.
      destruct i_eq as [i [Δ J]].
      set (F := instantiate_raw_rule_closure_system I
                  ((RawRule.fmap (Signature.empty_rect _))
                     (equality_raw_rule i))).
      assert (D := F (Δ;J)); clear F.
      refine (Closure.derivation_fmap1 _ _).
      { refine (Closure.sum_rect _ _).
        - apply Closure.idmap.
        - refine (Closure.compose _ Closure.inl).
          refine (Closure.compose _ Closure.inr).
          apply Closure.map_from_family_map.
          refine (Family.bind_include _ _ _).
          exact i.
      }
      (* TODO: can we streamline the following somehow with e.g. [RawRule.fmap_compose]? *)
      refine (transport (fun c => derivation _ _ c) _
             (transport (fun H => derivation _ H _) _ D)).
      + apply (ap (Judgement.instantiate _ _)).
        apply (ap (Judgement.instantiate _ _)).
        eapply concat. { apply inverse, Judgement.fmap_compose. }
        rapply @ap_1back.
        apply Family.sum_unique.
        * apply Family.empty_rect_unique.
        * apply idpath.
      + eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. 2: { apply Family.fmap_compose. }
        eapply concat. 2: { apply Family.fmap_compose. }
        apply (ap_1back Family.fmap), path_forall; intros j.
        apply (ap (Judgement.instantiate _ _)).
        apply (ap (Judgement.instantiate _ _)).
        eapply concat. { apply inverse, Judgement.fmap_compose. }
        apply (ap_1back Judgement.fmap).
        apply Family.sum_unique.
        * apply Family.empty_rect_unique.
        * apply idpath.
  Defined.

End Instantiation.
