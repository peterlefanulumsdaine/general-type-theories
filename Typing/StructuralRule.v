Require Import HoTT.
Require Import Syntax.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.

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

Context {σ : shape_system}.
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
of flat rules will always have conclusion context shape of the form γ+δ, where
δ is the conclusion context shape of the flat rule; this lets us go from such
conclusions to arbitrary contexts.

The specific instances we really use are isomorphisms of the form γ <~> γ+0 and
(γ+δ)+χ <~> γ+(δ+χ), used for instance in the instantiation of derivations,
Over some specific shape systems, e.g. de Bruijn shapes, these isomorphisms are
identities, so this rule should never be required over such shape systems.
*)

(* TODO: naming of this rule not ideal.  Keep seeking better options? *)
(* TODO: would it work more cleanly if the direction of this rule was reversed? *)
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

(** General substitution along context maps:

  Γ' |- f(x) : A   [for each x in Γ, A := type of x in Γ]
  Γ |- J   [for J any hypothetical judgement]
  --------------------
  Γ' |- f^*J
*)
Definition subst_apply_instance : Closure.system (judgement Σ).
Proof.
  exists { Γ : raw_context Σ
    & { Γ' : raw_context Σ
    & { f : raw_context_map Σ Γ' Γ
    & hypothetical_judgement Σ Γ}}}.
  intros [Γ [Γ' [f hj]]].
  split.
  (* premises: *)
  - refine (Family.adjoin _ _).
    (* all components of [f] are suitably typed: *)
    + exists Γ.
      intros i. refine [! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* the target judgement holds over Γ *)
    + exists Γ; exact hj.
  (* conclusion: *)
  - exists Γ', (form_of_judgement hj).
    intros i. exact (substitute f (hj i)).
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
    & { f : raw_context_map Σ Γ' Γ
    & { g : raw_context_map Σ Γ' Γ
    & { cl : syntactic_class
    & hypothetical_judgement_expressions Σ (form_object cl) Γ}}}}}.
  intros [Γ [Γ' [f [g [cl hjfi]]]]].
  split.
  (* premises: *)
  - refine (Family.adjoin (_ + _ + _) _).
    (* f is a context morphism *)
    + exists Γ.
      intros i. refine [! Γ' |- _ ; _ !].
      * exact (f i).
      * exact (substitute f (Γ i)).
    (* g is a context morphism *)
    + exists Γ.
      intros i. refine [! Γ' |- _ ; _ !].
      * exact (g i).
      * exact (substitute g (Γ i)).
    (* f ≡ g *)
    + exists Γ.
      intros i. refine [! Γ' |- _ ≡ _ ; _ !].
    (* TODO: note inconsistent ordering of arguments in [give_Tm_ji] compared to
      other [give_Foo_ji]. Consider, consistentise? *)
      * exact (substitute f (Γ i)).
      * exact (f i).
      * exact (g i).
    (* the target judgement holds over Γ *)
    + exists Γ, (form_object cl).
      exact hjfi.
  (* conclusion: *)
  - exists Γ', (form_equality cl).
    intros [i | | ].
    + (* boundary *)
      exact (substitute f (hjfi (the_boundary _ i))).
    + (* LHS *)
      exact (substitute f (hjfi (the_head _))).
    + (* RHS *)
      exact (substitute g (hjfi (the_head _))).
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
(** The equality structural rules can all be specified as flat rules over the empty signature. 

(One could specify them directly over arbitrary signatures, but then one would have to prove naturality for them afterwards.)*)

(* rule tyeq_refl
    ⊢ A type
-----------------
    ⊢ A ≡ A
*)

Definition tyeq_refl_rule : flat_rule (Signature.empty σ).
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

Definition tyeq_sym_rule : flat_rule (Signature.empty σ).
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

Definition tyeq_trans_rule : flat_rule (Signature.empty σ).
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

Definition tmeq_refl_rule : flat_rule (Signature.empty σ).
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

Definition tmeq_sym_rule : flat_rule (Signature.empty σ).
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

Definition tmeq_trans_rule : flat_rule (Signature.empty σ).
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

Definition term_convert_rule : flat_rule (Signature.empty σ).
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

Definition tmeq_convert_rule : flat_rule (Signature.empty σ).
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

Definition equality_flat_rule : family (flat_rule (Signature.empty σ))
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
       (Family.fmap (FlatRule.fmap (Signature.empty_rect _)) equality_flat_rule)
       FlatRule.closure_system.

End Equality.

End HypotheticalStructuralRules.

Definition structural_rule : Closure.system (judgement Σ)
  := rename_instance + substitution_instance
     + variable_instance + equality_instance.

End StructuralRules.

Section StructuralRuleAccessors.
  (** Access functions, for selcting structural rules in derivations *)

  (* Note: in a separate section just so that [Σ] can be declared as implicit
   argument for them all, rather than needing to be all redeclared with
   [Arguments] afterwards. *)

Context {σ : shape_system} {Σ : signature σ}.

Local Definition rename : rename_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inl i)).
Definition subst_apply : subst_apply_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inr (inl i))).
Definition subst_equal : subst_equal_instance Σ -> structural_rule Σ
  := fun i => inl (inl (inr (inr i))).
Definition variable_rule : variable_instance Σ -> structural_rule Σ
  := fun i => inl (inr i).
Definition equality_rule : equality_instance Σ -> structural_rule Σ
  := fun i => inr i.
Definition tyeq_refl : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tyeq_refl_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some (Some (Some tt)))))) ; i).
Definition tyeq_sym : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tyeq_sym_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some (Some None))))) ; i).
Definition tyeq_trans : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tyeq_trans_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some (Some None)))) ; i).
Definition tmeq_refl : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tmeq_refl_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some (Some (Some None))) ; i).
Definition tmeq_sym : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tmeq_sym_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some (Some None)) ; i).
Definition tmeq_trans : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tmeq_trans_rule)
    -> structural_rule Σ
  := fun i => inr (Some (Some None) ; i).
Definition term_convert : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) term_convert_rule)
    -> structural_rule Σ
  := fun i => inr (Some None ; i).
Definition tmeq_convert : FlatRule.closure_system
      (FlatRule.fmap (Signature.empty_rect _) tmeq_convert_rule)
    -> structural_rule Σ
  := fun i => inr (None ; i).

End StructuralRuleAccessors.

Section StructuralRuleInd.

Context {σ : shape_system}.
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
          | [i_sub_ap | i_sub_eq] ]
        | i_var ]
      | i_eq ]
  ; eauto.
Defined.

Definition equality_instance_rect :
  forall (P : structural_rule Σ -> Type),
       (forall i_tyeq_refl : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tyeq_refl_rule),
         P (tyeq_refl i_tyeq_refl))
    -> (forall tyeq_sym_rule : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tyeq_sym_rule),
         P (tyeq_sym tyeq_sym_rule))
    -> (forall tyeq_trans_rule : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tyeq_trans_rule),
         P (tyeq_trans tyeq_trans_rule))
    -> (forall i_tmeq_refl : FlatRule.closure_system
          (FlatRule.fmap (Signature.empty_rect _) tmeq_refl_rule),
         P (tmeq_refl i_tmeq_refl))
    -> (forall i_tmeq_sym : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tmeq_sym_rule),
         P (tmeq_sym i_tmeq_sym))
    -> (forall i_tmeq_trans : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tmeq_trans_rule),
         P (tmeq_trans i_tmeq_trans))
    -> (forall i_term_convert : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) term_convert_rule),
         P (term_convert i_term_convert))
    -> (forall i_tmeq_convert : FlatRule.closure_system
           (FlatRule.fmap (Signature.empty_rect _) tmeq_convert_rule),
         P (tmeq_convert i_tmeq_convert))
  -> forall e : equality_instance Σ, P (equality_rule e).
Proof.
  intros P X X0 X1 X2 X3 X4 X5 X6.
  intros [ index element ].
  repeat destruct index as [ index | ];
  try destruct index; eauto.
Defined.

End StructuralRuleInd.

Section Renaming.
  (** Interface to the renaming structural rule,
   and some frequently-used special cases. *)

  Context `{H_Funext : Funext}
        {σ : shape_system} {Σ : signature σ}
        {C : Closure.system (judgement Σ)} (T := (structural_rule Σ + C))
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
    simple refine (Closure.deduce' _ _ _).
    { apply inl, rename. exists Γ, Γ', f; exact J. }
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
    simple refine (Closure.deduce' _ _ _).
    { apply inl, rename.
      refine (_;(_;(f;_))). exact J'. }
    { apply (ap (Build_judgement _)), inverse, e. }
    { intros; apply D. }
  Defined.

  Lemma derive_renaming_along_equiv
      (J : judgement Σ)
      {γ' : σ} (e : γ' <~> shape_of_judgement J)
    : Closure.derivation T H J
    -> Closure.derivation T H (Judgement.rename J e).
  Proof.
    simple refine (derive_rename' _ _ _ _).
    - apply Context.typed_renaming_to_rename_context.
    - apply idpath.
  Defined.

  Lemma derive_from_renaming_along_equiv
      (J : judgement Σ)
      {γ' : σ} (e : γ' <~> shape_of_judgement J)
    : Closure.derivation T H (Judgement.rename J e)
      -> Closure.derivation T H J.
  Proof.
    simple refine (derive_rename' _ _ _ _).
    - apply Context.typed_renaming_from_rename_context.
    - apply (ap (Build_hypothetical_judgement _)), inverse.
      apply path_forall; intros s.
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply rename_idmap. }
      apply (ap (fun r => Expression.rename r _)).
      apply path_forall; intro; apply eisretr.
  Defined.

(** A particularly common case: renaming along the equivalence [ Γ <~> Γ+0 ].

This arises with instantiations of flat rules: their conclusion is typically
over a context [ Γ + 0 ], not just [ Γ ] as one would want. *)

  Definition derive_reindexing_to_empty_sum
      (J : judgement Σ)
    : Closure.derivation T H J
    -> Closure.derivation T H
         (Judgement.rename J (equiv_inverse (shape_sum_empty_inl _))).
  Proof.
    apply derive_renaming_along_equiv.
  Defined.

  Definition derive_from_reindexing_to_empty_sum
      {Γ : raw_context Σ}
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation T H
          (Judgement.rename
             (Build_judgement Γ J) (equiv_inverse (shape_sum_empty_inl _)))
    -> Closure.derivation T H (Build_judgement Γ J).
  Proof.
    apply derive_from_renaming_along_equiv.
  Defined.

End Renaming.

Section InterfaceFunctions.
(** More convenient interface functions for using the rules in derivations *)

  Context `{H_Funext : Funext}
        {σ : shape_system} {Σ : signature σ}
        {C : Closure.system (judgement Σ)} (T := (structural_rule Σ + C))
        {H : family (judgement Σ) }.

  Lemma derive_variable
      (Γ : raw_context Σ) (i : Γ)
      (d_Γi : derivation T H [! Γ |- Γ i !])
    : derivation T H [! Γ |- raw_variable i ; Γ i !].
  Proof.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, variable_rule. exists Γ; exact i. }
    { apply idpath. }
    intro; apply d_Γi.
  Defined.

  (** A slightly technical lemma, useful under [Judgement.eq_by_expressions]
    for the types of a contexr reindexed under [shape_sum_empty_inl]. *)
  (* TODO: perhaps upstream to e.g. [Context]? *)
  Lemma instantiate_empty_ptwise
      (Γ : raw_context Σ)
      (f : shape_empty σ -> raw_type Σ _)
      (i : shape_sum Γ (shape_empty σ))
    : coproduct_rect (shape_is_sum) _
        (fun j:Γ => Expression.rename (shape_sum_empty_inl _) (Γ j))
        f i
    = Context.rename Γ (shape_sum_empty_inl _)^-1 i.
  Proof.
    revert i. cbn.
    apply (coproduct_rect shape_is_sum).
    + intros ?.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      cbn. apply ap, ap.
      apply inverse. refine (coproduct_comp_inj1 _).
    + exact (empty_rect _ shape_is_empty _).
  Defined.

  (** Another technical lemma, useful under [Judgement.eq_by_expressions]
      for instantiations of a metavariable with empty binder. *)
  (* TODO: perhaps upstream to e.g. [Metavariable]? *)
  Lemma instantiate_binderless_metavariable
      {γ : σ} {cl}
      (E : raw_expression Σ cl (shape_sum γ (shape_empty _)))
      {f}
    : substitute
        (coproduct_rect shape_is_sum _
                        (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
                        f)
        E
      = E.
  Proof.
    eapply concat. 2: { apply rename_idmap. }
    eapply concat. 2: { apply substitute_raw_variable. }
    apply (ap (fun g => substitute g _)).
    apply path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; refine (coproduct_comp_inj1 _).
    - apply (empty_rect _ shape_is_empty).
  Defined.

  Definition derive_tyeq_refl
      (Γ : raw_context Σ) (A : raw_expression Σ class_type Γ)
      (d_A : derivation T H [! Γ |- A !])
    : derivation T H [! Γ |- A ≡ A !].
  Proof.
    apply derive_from_reindexing_to_empty_sum.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, tyeq_refl. 
      exists Γ.
      intros i; recursive_destruct i. cbn.
      refine (Expression.rename _ A). 
      apply shape_sum_empty_inl. }
    { refine (Judgement.eq_by_expressions _ _).
      - intros i. apply instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          apply instantiate_binderless_metavariable.
    }
    intros [].
    refine (transport _ _
                      (derive_reindexing_to_empty_sum _ d_A)).
    apply Judgement.eq_by_expressions.
    - intros i. apply inverse, instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
        apply inverse, instantiate_binderless_metavariable.
  Defined.

  Definition derive_tyeq_sym
      (Γ : raw_context Σ) (A B : raw_expression Σ class_type Γ)
      (d_AB : derivation T H [! Γ |- A ≡ B !])
    : derivation T H [! Γ |- B ≡ A !].
  Proof.
  Admitted. (* [derive_tyeq_sym]: straightforward, similar to others in section *)

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
    simple refine (Closure.deduce' _ _ _).
    { apply inl, term_convert.
      exists Γ.
      intros i; recursive_destruct i;
        refine (Expression.rename (shape_sum_empty_inl _) _).
      + exact A.
      + exact B.
      + exact u.
    }
    { refine (Judgement.eq_by_expressions _ _).
      - apply instantiate_empty_ptwise.
      - intros i; recursive_destruct i;
          apply instantiate_binderless_metavariable.
    }
    intros p. set (p_keep := p).
    recursive_destruct p;
      [ set (d := d_A) | set (d := d_B) | set (d := d_AB) | set (d := d_u) ];
      refine (transport _ _ (derive_reindexing_to_empty_sum _ d));
      (apply Judgement.eq_by_expressions;
       [ intros; apply inverse, instantiate_empty_ptwise
       | intros i; recursive_destruct i;
         apply inverse, instantiate_binderless_metavariable]).
  Defined.

End InterfaceFunctions.


Section SignatureMaps.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (** For a given signature map [f] from [Σ] to [Σ'],
     the translations of structural rules of [Σ] are structural rules of [Σ']. *)
  Local Definition fmap
      {Σ Σ' : signature σ}
      (f : Signature.map Σ Σ')
    : Family.map_over (Closure.rule_fmap (Judgement.fmap f))
        (structural_rule Σ)
        (structural_rule Σ').
  Proof.
    (* TODO: possible better approach:
       - [Family.fmap] of families commutes with sums;
       - then use [repeat apply Family.fmap_sum.] or similar?  *)
    apply Family.Build_map'.
    apply structural_rule_rect ; intros.
    (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap_Family] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: try a few by hand, then consider this. *)
    - (* rename *)
      destruct i_rename as [Γ [Γ' [α J]]].
      simple refine (_;_).
      + apply rename.
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_typed_renaming f α).
        exact (fmap_hypothetical_judgement f J).
      + apply Closure.rule_eq.
        * apply idpath.
        * refine (Judgement.eq_by_expressions _ _); intros i.
          -- apply idpath.
          -- apply inverse, fmap_rename.
    - (* subst_apply *)
      destruct i_sub_ap as [ Γ [Γ' [g hj]]].
      simple refine (_;_).
      + refine (subst_apply _).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (raw_context_map_fmap f g).
        exact (Judgement.fmap_hypothetical_judgement f hj).
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          unfold Family.fmap.
          apply ap, path_forall; intros i.
          refine (Judgement.eq_by_expressions _ _);
            intros j; try apply idpath; recursive_destruct j;
            try apply idpath; apply fmap_substitute.
        * refine (Judgement.eq_by_expressions _ _);
            intros; try apply idpath.
          refine (fmap_substitute _ _ _)^.
    - (* subst_equal *)
      destruct i_sub_eq as [ Γ [Γ' [g [g' [jf hj]]]]].
      simple refine (_;_).
      + refine (subst_equal _).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (raw_context_map_fmap f g).
        exists (raw_context_map_fmap f g').
        exists jf.
        intros i. apply (Expression.fmap f), hj.
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_adjoin. }
          apply ap011; try apply idpath.
          eapply concat. { apply Family.fmap_sum. }
          eapply concat. { eapply (ap (fun K => K + _)), Family.fmap_sum. }
          apply ap2; try apply ap2; unfold Family.fmap.
          -- apply ap, path_forall; intros i.
            refine (Judgement.eq_by_expressions _ _);
            intros j; try apply idpath; recursive_destruct j;
              try apply idpath; apply fmap_substitute.
          -- apply ap, path_forall; intros i.
            refine (Judgement.eq_by_expressions _ _);
            intros j; try apply idpath; recursive_destruct j;
              try apply idpath; apply fmap_substitute.
          -- apply ap, path_forall; intros i.
            refine (Judgement.eq_by_expressions _ _);
            intros j; try apply idpath; recursive_destruct j;
              try apply idpath; apply fmap_substitute.
        * refine (Judgement.eq_by_expressions _ _);
            intros; try apply idpath.
          recursive_destruct i; refine (fmap_substitute _ _ _)^.
    - (* var rule *)
      destruct i_var as [Γ x].
      simple refine (variable_rule _ ; _).
      + exists (Context.fmap f Γ); exact x.
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.fmap_singleton. }
          apply ap.
          apply Judgement.eq_by_eta, idpath.
        * apply Judgement.eq_by_eta, idpath.
    - (* equality rules *)
      destruct i_eq as [r ΓI].
      simple refine (equality_rule _;_).
      + exists r.
        simple refine (FlatRule.closure_system_fmap' f _ ΓI).
        refine (_ @ _). { apply inverse, FlatRule.fmap_compose. }
        refine (ap (fun f => FlatRule.fmap f _) _).
        apply Signature.empty_rect_unique.
      + refine (Family.map_over_commutes
                  (FlatRule.closure_system_fmap' f _) _).
  Defined.

End SignatureMaps.

Section Instantiation.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** Given a flat rule [R] over a signature [Σ], an arity [a] specifying a
  metavariable extension, and an instantiation [I] of [a] in [Σ] over some
  context [Γ],

  any instance of [R] over the extended signature [extend Σ a] gets translated
  under [I] into an instance of [R] over [Σ], modulo renaming. 

  Note: this can’t be in [Typing.FlatRule], since it uses the structural rules,
  specifically the rule for renaming along shape isomorphisms.  Morally perhaps
  that should be seen as more primitive than the other structural rules, and be
  baked into the notion of derivations earlier, as e.g. “closure systems on a
  groupoid”.  (Indeed, if the shape system is univalent then this rule _will_
  come for free.)
  *)
  Definition instantiate_flat_rule_closure_system
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : flat_rule Σ)
    : Closure.map_over
        (Judgement.instantiate Γ I)
        (FlatRule.closure_system (FlatRule.fmap include_symbol r))
        (structural_rule Σ + FlatRule.closure_system r).
  Proof.
    intros [Δ J].
    (* The derivation essentially consists of the instance
     [(Context.instantiate _ I Δ
     ; instantiate_instantiation I J)]
     of the same flat rule, wrapped in renamings along [shape_assoc].
     *)
    simple refine (derive_rename' _ _ _ _ _).
    4: simple refine (Closure.deduce' _ _ _);
       [ apply inr; 
         exists (Context.instantiate _ I Δ);
         exact (instantiate_instantiation I J)
       | apply idpath | ].
    { apply Context.instantiate_instantiate_ltor. }
    { (* TODO: abstract as something like [instantiate_instantiate_hypothetical_judgement], and consider direction. *)
      apply (ap (Build_hypothetical_judgement _)), path_forall. intros i.
      cbn; apply inverse.
      eapply concat. { apply ap, instantiate_instantiate_expression. }
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply rename_idmap. }
      apply (ap (fun f => Expression.rename f _)).
      apply path_forall; intros j.
      apply Coproduct.assoc_rtoltor.
    }
    intros p.
    simple refine (derive_rename' _ _ _ _ _).
    4: refine (Closure.hypothesis _ _ _); apply p.
    { apply Context.instantiate_instantiate_rtol. }
    apply (ap (Build_hypothetical_judgement _)), path_forall. intros i.
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
    (* TODO: As with [fmap] above, there really should be a more uniform way to do this. *)
    unfold Closure.map_over.
    refine (structural_rule_rect _ _ _ _ _ _).
    - (* rename*)
      intros [Δ [Δ' [α J]]].
      simple refine (Closure.deduce' _ _ _).
      { apply rename.
        exists (Context.instantiate Γ I Δ),
               (Context.instantiate Γ I Δ'),
               (instantiate_typed_renaming Γ I α).
        exact (instantiate_hypothetical_judgement I J).
      }
      { apply Judgement.eq_by_expressions; intros;
          [ apply idpath | apply inverse, instantiate_rename ].
      }
      intros p; refine (Closure.hypothesis _ _ p).
    - (* subst_apply *) admit.
    - (* subst_equal *) admit.
    - (* variable_rule *) 
      intros [Δ i]; cbn.
      simple refine (Closure.deduce' _ _ _).
      { apply variable_rule.
        exists (Context.instantiate _ I Δ).
        exact (coproduct_inj2 shape_is_sum i).
      }
      { apply Judgement.eq_by_expressions.
        - intros; apply idpath.
        - intros [[] | ].
          + refine (coproduct_comp_inj2 _).
          + apply idpath.
      }
      intros p. simple refine (Closure.hypothesis' _ _).
      { exact p. }
      apply Judgement.eq_by_expressions.
      + intros; apply idpath.
      + intros [[] | ].
        apply inverse; refine (coproduct_comp_inj2 _).
    - (* equality_rule *)
      intros i_eq.
      destruct i_eq as [i [Δ J]].
      set (F := instantiate_flat_rule_closure_system I
                  ((FlatRule.fmap (Signature.empty_rect _))
                     (equality_flat_rule i))).
      assert (D := F (Δ;J)); clear F.
      refine (Closure.derivation_fmap1 _ _).
      { refine (Closure.sum_rect _ _).
        - apply Closure.idmap.
        - refine (Closure.compose _ Closure.inr).
          apply Closure.map_from_family_map.
          refine (Family.bind_include _ _ _).
          exact i.
      }
      (* TODO: can we streamline the following somehow with e.g. [FlatRule.fmap_compose]? *)
      refine (transport (fun c => derivation _ _ c) _ 
             (transport (fun H => derivation _ H _) _ D)).
      + apply (ap (Judgement.instantiate _ _)).
        apply (ap (Judgement.instantiate _ _)).
        eapply concat. { apply inverse, Judgement.fmap_compose. }
        refine (ap (fun f => (Judgement.fmap f _)) _).
        apply Family.sum_unique.
        * apply Family.empty_rect_unique.
        * apply idpath.
      + eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. { apply inverse, Family.fmap_compose. }
        eapply concat. 2: { apply Family.fmap_compose. }
        eapply concat. 2: { apply Family.fmap_compose. }
        refine (ap (fun f => (Family.fmap f _)) _).
        apply path_forall; intros j.
        apply (ap (Judgement.instantiate _ _)).
        apply (ap (Judgement.instantiate _ _)).
        eapply concat. { apply inverse, Judgement.fmap_compose. }
        refine (ap (fun f => (Judgement.fmap f _)) _).
        apply Family.sum_unique.
        * apply Family.empty_rect_unique.
        * apply idpath.
  Admitted. (* [StructuralRule.instantiate]: a bit thorny, substantial amount remaining. *)

End Instantiation.
