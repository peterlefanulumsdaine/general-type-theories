Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.
Require Import Raw.CongruenceRule.
Require Import Typed.TypedClosure.
Require Import Typed.TypedStructuralRule.
Require Import Typed.TypedRule.
Require Import Typed.TypeTheory.

(** The main goal of this file is the metatheorem that all presuppositions
    of a derivable judgement are derivable, over any type theory: *)
Theorem derive_presupposition_closed {σ} {T : raw_type_theory σ}
     {j : judgement_total (RawTypeTheory.signature T)}
     (dj : RawTypeTheory.derivation T [<>] j)
     {p : presupposition j }
  : RawTypeTheory.derivation T [<>] (presupposition j p).
Abort.
(** In outline, the high level structure of the proof consists of giving analogues of the notions of “closed under presuppositions” for flat rules/flat type theories and closure rules/closure systems, and then doing the main inductive construction purely in terms of closure systems.

The low-level hard work is showing that the flat rules / closure conditions arising from type theories really are presupposition-closed in the appropriate sense. *)


Section PresuppositionClosureFlat.
(** In this section, we show how “presupposition-closedness” transfers between the flat world and the closure-system world. *)

  Context {σ : shape_system} `{Funext}.

  (** A flat type theory is presupposition-closed if all its rules are (weakly) well-typed over it.

  (One might be tempted to call this “well-typed”, but we don’t, because it’s not really strong enough to imply much about the behaviour of the theory.) *)
  Definition presupposition_closed_flat_type_theory
      {Σ : signature σ} (T : flat_type_theory Σ)
    : Type
  := forall r : T, TypedFlatRule.weakly_well_typed T (T r).

  (** If a flat type theory T is presup-closed, then so is its associated closure system. *)
  Theorem closure_system_of_presupposition_closed_flat_type_theory
      {Σ : signature σ} {T : flat_type_theory Σ}
      (T_presup_closed : presupposition_closed_flat_type_theory T)
    : TypedClosure.weakly_well_typed_system presupposition
        (FlatTypeTheory.closure_system T).
  Proof.
    intros [r_str | r_log ].
    - intros p.
      refine (Closure.fmap_derivation _ _).
      2: { apply TypedStructuralRule.well_typed. }
      + apply Closure.map_from_family_map.
        apply Family.fmap_of_sum.
        * apply Family.idmap.
        * apply Family.Build_map'; intros [[]].
    - destruct r_log as [r r_inst]. cbn in r_inst.
      destruct r_inst as [Γ r_args].
      apply TypedFlatRule.closure_system_weakly_well_typed.
      apply T_presup_closed.
  Defined.

  (** Putting the above together: all presuppositions of a derivable judgement
      over a presupposition-closed flat tpye theory are again derivable,
      assuming additionally all presuppositions of the original hypotheses. *)
  Theorem derive_presupposition_from_flat
      {Σ : signature σ}
      {T : flat_type_theory Σ} (H_T : presupposition_closed_flat_type_theory T)
      {j : judgement_total Σ} {hyps : family _}
      (d_j : FlatTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : FlatTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    simple refine
      (TypedClosure.presupposition_derivation presupposition _ d_j _).
    apply closure_system_of_presupposition_closed_flat_type_theory.
    apply H_T.
  Defined.

End PresuppositionClosureFlat.

Section PresuppositionClosure.

  Context {σ : shape_system} `{Funext}.

  Lemma rule_of_well_typed_type_theory_is_well_typed
      {T : raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      (r : T)
    : TypedRule.is_well_typed (RawTypeTheory.flatten T)
        (RawRule.fmap (RawTypeTheory.include_rule_signature r) (tt_rule r)).
  Proof.
    assert (r_WT := T_WT r).
    assert (r'_WT := TypedRule.fmap_is_well_typed
                    (RawTypeTheory.include_rule_signature _) r_WT).
    refine (TypedRule.fmap_is_well_typed_in_theory _ r'_WT).
    eapply FlatTypeTheory.compose.
    2: { eapply FlatTypeTheory.map_from_eq, inverse, FlatTypeTheory.fmap_compose. }
    apply FlatTypeTheory.map_from_family_map.
    apply (Family.map_vs_map_over _ _ _)^-1.
    apply RawTypeTheory.flatten_initial_segment.
  Admitted.
  (* Proof here is complete; [Admitted] is just to avoid universe
  proliferation causing terrible slowdown downstream. *)

  (** For any raw type theory [T] and a rule [r] of the flattened [T], every
      presupposition in the boundary of the conclusion of [r] can be derived. *)
  Lemma presupposition_closed_flatten
      {T : raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
    : presupposition_closed_flat_type_theory (RawTypeTheory.flatten T).
  Proof.
    (* The flattened [T] has logical and congruence rules, two cases to consider. *)
    (* Do these have to be treated separately, or can they be unified better? *)
    intros [r|r]; apply TypedRule.weakly_well_typed_flatten.
    - (* logical rules *)
      apply rule_of_well_typed_type_theory_is_well_typed, T_WT.
    - (* congruence rules *)
      apply congruence_rule_is_well_typed.
      apply rule_of_well_typed_type_theory_is_well_typed, T_WT.
  Defined.

  (** Working in a type theory [T], given a judgement [j] which is derivable
      from hypotheses [hyps], suppose every presupposition [q] of every hypothesis [h : hyps]
      is derivable from [hyps], then every presuppsition [p] of [j] is derivable from
      [hyps]. *)
  Theorem derive_presupposition
      {T : raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      {j : judgement_total (RawTypeTheory.signature T)}
      {hyps : family _}
      (dj : RawTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : RawTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    apply derive_presupposition_from_flat; try assumption.
    apply presupposition_closed_flatten, T_WT.
  Defined.

  (** Working in a type theory [T], given a judgment [j] which is derivable
      without hypotheses, ever presupposition of [j] is derivable. *)
  Corollary derive_presupposition_closed
      {T : raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      {j : judgement_total (RawTypeTheory.signature T)}
      (dj : RawTypeTheory.derivation T [<>] j)
      {p : presupposition j }
    : RawTypeTheory.derivation T [<>] (presupposition j p).
  Proof.
    refine (Closure.graft _ _ _).
    - refine (derive_presupposition T_WT dj).
    - intros i; recursive_destruct i.
  Defined.

End PresuppositionClosure.
