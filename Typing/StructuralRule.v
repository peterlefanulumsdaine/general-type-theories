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

  - variable-renaming rules: [rename_hypothetical]
  - variable rule: [variable_rule]
  - equivalence relation rules:
      [tyeq_refl, tyeq_sym, tyeq_trans,
      tmeq_refl, tmeq_sym, tmeq_trans,
  - conversion for term/term-eq judgments under type equalities:
      [term_convert, tmeq_convert].

  All of the above are then collected as a single family [structural_rule].

  A note on naming: each rule, e.g. [variable_rule] — which formally is not
  just a single rule, but a family of closure rules, one for each raw context
  [Γ] and position [i] thereof — has two things one might want to call
  [variable_rule]:

  - the definition of it as a family of rules;
  - the access function picking it out in the family [structural_rule].

  We use [variable_rule] for the access function, and call the family
  [variable_rule_instance], since an element of the family is a specific
  instance of the rule.  So to use this rule in a derivation, one will first
  say [apply variable_rule] to select the context extension rule, and then
  specify the particular instance desired, i.e. the context and the position
  desired.

  (An alternative convention could be to use [variable_rule] for the family,
  and [select_variable_rule] or similar for the access function.)
*)

Section StructuralRules.

Context {σ : shape_system}.
Context (Σ : signature σ).

Section RenamingRules.
(** Renaming of variables:

for any isomorphism of shapes [f : γ ≅ δ], we can rename variables along
[f] in any judgement with shape [γ], both hypothetical and context judgements:

  Γ |- J   [J any hypothetical judgement]
  --------------------
  f^* Γ |- f^*J

This is not traditionally explicitly given; we need it because our context
extension rule only extends by “the standard fresh variable” over a given
shape, and so to show that e.g. contexts whose shapes are given as coproducts
are contexts, we need a rule like this (or some other strengthening of the
context rules, or restrictions on the shape system).
*)
(* TODO: probably no longer needed. *)

(*
  Γ |- J   [J any judgement]
  -------------- [f : γ' <~> Γ]
  f^* Γ |- f^*J
*)
(* TODO: naming of this rule far from ideal (both in itself, and in how it interacts with our [_instance] convention).  Keep seeking better options? *)
(* TODO: would it work more cleanly if the direction of this rule was reversed? *)
Definition rename_instance : Closure.system (judgement Σ).
Proof.
  exists { J : judgement Σ
               & { γ' : shape_carrier σ & γ' <~> shape_of_judgement J }}.
  intros [J [γ' f]]. split.
  - (* premises: *)
    exact [< J >].
  - (* conclusion: *)
    exact (Judgement.rename J f).
Defined.

End RenamingRules.

Section VarRules.

(* The general variable rule:

  Γ ΓA type
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

End VarRules.

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

Definition structural_rule : Closure.system (judgement Σ)
  := rename_instance + variable_instance + equality_instance.

End StructuralRules.

Section StructuralRuleAccessors.
  (** Access functions, for selcting structural rules in derivations *)

  (* Note: in a separate section just so that [Σ] can be declared as implicit
   argument for them all, rather than needing to be all redeclared with
   [Arguments] afterwards. *)

Context {σ : shape_system} {Σ : signature σ}.

Local Definition rename : rename_instance Σ -> structural_rule Σ
  := fun i => inl (inl i).
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
  -> (forall i_var : variable_instance Σ, P (variable_rule i_var))
  -> (forall i_eq : equality_instance Σ, P (equality_rule i_eq))
  -> forall s : structural_rule Σ, P s.
Proof.
  intros P ? ? ? s.
  destruct s as [ [ i_rename | i_var ] | i_eq ]
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
      destruct i_rename as [J [γ' e]].
      simple refine (_;_).
      + apply rename.
        exists (Judgement.fmap f J).
        exact (γ'; e).
      + apply Closure.rule_eq.
        * apply idpath.
        * (* hypothetical judgement *)
          refine (Judgement.eq_by_expressions _ _); intros i;
            apply inverse, fmap_rename.
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

  (** Structural rules in a metavariable extension,
   translated under an instantiation,
   can always be derived from structural rules over the base signature.

  Essentially, any structural rule gets translated into an instance of the same structural rule, possibly wrapped in a variable-renaming to reassociate iterated context extensions *)
  (* TODO: do we have to assume some form of well-typedness of the context? *)
  Local Definition instantiate
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
    : Closure.map_over (@Judgement.instantiate σ _ Σ Γ I)
        (structural_rule (Metavariable.extend Σ a))
        (structural_rule Σ).
  Proof.
    (* TODO: As with [fmap] above, there really should be a more uniform way to do this. *)
    unfold Closure.map_over.
    refine (structural_rule_rect _ _ _ _).
    - (* rename*) admit.
    - (* variable_rule *) admit.
    - (* equality_rule *) admit.
  Admitted.

End Instantiation.
