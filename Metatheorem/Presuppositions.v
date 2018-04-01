Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.
Require Import Typed.TypedClosure.
Require Import Typed.Derivation.
Require Import Typed.TypedStructuralRule.
Require Import Typed.TypeTheory.
 
(** The goal of this file is the theorem that presuppositions of a derivable judgement are derivable, over any type theory: *)
Theorem closed_presupposition_derivation {σ} {T : raw_type_theory σ}
     {j : judgement_total (RawTypeTheory.signature T)}
     (dj : RawTypeTheory.derivation T [<>] j)
     {p : Judgement.presupposition j }
  : RawTypeTheory.derivation T [<>] (Judgement.presupposition j p).
Abort.
(** In order to establish this, we require a few bits of background machinery:
  - for the high level structure of the proof, abstractions of the notions of “closed under presuppositions” to flat type theories and closure systems;
  - for the lower level details, some lemmas on the interaction of derivations/presuppositions with translation under metavariable instantiations. *)

(** General background: establish some properties of how the syntactic translation given by metavariable instantiation preserves typing derivations.

  TODO: probably factor this out into a separate file. *)
Section Derivability_Under_Instantiation.

  Context {σ : shape_system}.

  Definition instantiate_derivation
      {Σ : signature σ} (T : flat_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (hyps : family _) (j : judgement_total (Metavariable.extend Σ a))
      (d : FlatTypeTheory.derivation
             (FlatTypeTheory.fmap include_symbol T)
             hyps j)
    : FlatTypeTheory.derivation T
           (Family.fmap (Metavariable.instantiate_judgement I) hyps)
           (Metavariable.instantiate_judgement I j).
  Proof.
  Admitted.

  Arguments Metavariable.instantiate_judgement : simpl nomatch.
  Arguments Metavariable.instantiate_expression : simpl nomatch.
  Arguments Metavariable.instantiate_context : simpl nomatch.


Local Ltac recursive_destruct x :=
    cbn in x;
    try match type of x with
    | hypothetical_form => destruct x as [ cl | cl ]; recursive_destruct cl  
    | syntactic_class => destruct x as [ | ]
    | option _ => destruct x as [ y | ]; [recursive_destruct y | idtac ] 
    | Empty => destruct x
    | Unit => destruct x as []
    | _ => idtac
    end.

  (* TODO: upstream, but to where? *)
  (* TODO consider whether [presupposition] could be refactored to make this easier. *)
  Definition presupposition_instantiate `{Funext}
      {Σ : signature σ}
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement_total _)
    : Judgement.presupposition (Metavariable.instantiate_judgement I j)
      = Family.fmap (Metavariable.instantiate_judgement I) (Judgement.presupposition j).
  Proof.
    destruct j as [[ | hjf] j].
    - simple refine (Family.eq _ _); try apply idpath.
      intros [].
    - simple refine (Family.eq _ _); try apply idpath.
      intros i. cbn in i. destruct i as [ i | ].
      + (* slots *)
        (* Do some computation by hand: *)
        simpl (equiv_path _ _ 1).
        eapply concat.
        Focus 2. { apply ap. exact (idpath (Some i)). } Unfocus.
        (* The judgement and context parts are judgementally equal: *)
        simple refine (path_sigma _ _ _ _ _); try apply idpath.
        simple refine (path_sigma _ _ _ _ _); try apply idpath.
        apply path_forall; intros k.
        recursive_destruct hjf;
        recursive_destruct i;
        recursive_destruct k;
        try apply idpath.
      + (* raw context *)
        apply idpath.
  Defined.

End Derivability_Under_Instantiation.

(** Main theorem: [presupposition_derivable]: the presuppositions of any derivable judgement are again derivable. *)
Section Presuppositions_Derivable.

  Context {σ : shape_system} `{Funext}.

  Definition presupposition_closed_structural_closure_system {Σ : signature σ}
      (P := fun (j : judgement_total Σ) => Judgement.presupposition j)
    : TypedClosure.well_typed_boundary P (structural_rule _).
  Proof.
    apply TypedClosure.well_typed_has_well_typed_boundary.
    apply TypedStructuralRule.well_typed.
  Defined.
 
  (* TODO: make Σ implicit in fields of [flat_rule] *)
  Definition presupposition_closed
      {Σ : signature σ} (T : flat_type_theory Σ)
    : Type.
  Proof.
    refine (forall r : T, _ (T r)). clear r; intros r.
    refine (FlatTypeTheory.presupposition_derivation _
              (boundary_of_judgement _) (flat_rule_premises _ r)).
    - exact (FlatTypeTheory.fmap include_symbol T). 
    - exact (pr2 (flat_rule_conclusion _ r)).
  Defined.

  Theorem closure_system_of_presupposition_closed_flat_type_theory
      {Σ : signature σ} {T : flat_type_theory Σ}
      (T_presup_closed : presupposition_closed T)
      (P := fun (j : judgement_total Σ) => Judgement.presupposition j)
    : TypedClosure.well_typed_boundary P (FlatTypeTheory.closure_system T).
  Proof.
    intros [r_str | r_log ].
    - intros p. 
      refine (Closure.map_derivation _ _).
      Focus 2. { apply presupposition_closed_structural_closure_system. } Unfocus.
      apply Closure.map_from_family_map, Family.map_inl.
    (* abstract out presup-closure of structural cc’s *) 
    - destruct r_log as [r r_inst]. cbn in r_inst. 
      destruct r_inst as [Γ r_args].
      cbn.
      set (Pr := P (Metavariable.instantiate_judgement r_args
                                             (flat_rule_conclusion _ (T r)))).
      assert (H_presup_inst : Pr =
          Family.fmap (Metavariable.instantiate_judgement r_args)
                      (Judgement.presupposition (flat_rule_conclusion _ (T r)))).
      { apply presupposition_instantiate. }
      clearbody Pr. destruct H_presup_inst^.
      intros p. apply instantiate_derivation, T_presup_closed.
  Defined.


   (** If a flat type theory T is presup-closed, then so is its associated closure system. *)
  (* TODO: perhaps change def of flat rules to allow only _hypothetical_ judgements? *)
  Theorem presupposition_derivation_from_flat
      {Σ : signature σ}
      {T : flat_type_theory Σ} (T_presup_closed : presupposition_closed T)
      {j : judgement_total Σ} {hyps : family _}
      (d_j : FlatTypeTheory.derivation T hyps j)
      (d_hyp_presups :
         forall (h : hyps) (p : Judgement.presupposition (hyps h)),
           FlatTypeTheory.derivation T hyps (Judgement.presupposition _ p))
      {p : Judgement.presupposition j }
    : FlatTypeTheory.derivation T hyps (Judgement.presupposition _ p).
  Proof.
    refine (TypedClosure.presupposition_derivation (fun j => Judgement.presupposition j) _ _ _ _).
    - apply closure_system_of_presupposition_closed_flat_type_theory.
      apply T_presup_closed.
    - apply d_hyp_presups.
    - apply d_j.
  Defined.

  Lemma presupposition_closed_flatten {T : raw_type_theory σ}
    : presupposition_closed (RawTypeTheory.flatten T).
  Proof.
  Admitted.

  (* TODO: at least make access function between [judgment] and [judgement_total]; perhaps make it a coercion? *)
  Theorem presupposition_derivation {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      {hyps : family _}
      (dj : RawTypeTheory.derivation T hyps j)
      (d_hyp_presups :
         forall (h : hyps) (p : Judgement.presupposition (hyps h)),
           RawTypeTheory.derivation T hyps (Judgement.presupposition _ p))
      {p : Judgement.presupposition j }
    : RawTypeTheory.derivation T hyps (Judgement.presupposition j p).
  Proof.
    apply presupposition_derivation_from_flat; try assumption.
    apply presupposition_closed_flatten.
  Defined.

  Corollary closed_presupposition_derivation {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      (dj : RawTypeTheory.derivation T [<>] j)
      {p : Judgement.presupposition j }
    : RawTypeTheory.derivation T [<>] (Judgement.presupposition j p).
  Proof.
    apply presupposition_derivation; try assumption.
    intros [].
  Defined.

End Presuppositions_Derivable.
