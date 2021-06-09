Require Import HoTT.HoTT.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.PresentedRawRule.
Require Import Presented.PresentedRawTypeTheory.
Require Import Typing.Presuppositions.
Require Import Typing.StructuralRule.
Require Import Typing.RawRule.
Require Import Typing.RawTypeTheory.
Require Import Presented.CongruenceRule.
Require Import Typing.StructuralRulePresuppositions.
Require Import Presented.TypedRule.
Require Import Presented.TypeTheory.

(* TODO: upstream the raw parts of this file to [Typing.Presuppositions]?? *)


(** The main goal of this file is the “presuppositivity metatheorem”:
    the presuppositions of a derivable judgement are also derivable,
    over any well-typed type theory: *)
Theorem derive_presupposition {σ} {Σ : signature σ}
    {T : presented_raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
    {j : judgement (PresentedRawTypeTheory.signature T)}
    (dj : PresentedRawTypeTheory.derivation T [<>] j)
    {p : presupposition j }
  : PresentedRawTypeTheory.derivation T [<>] (presupposition j p).
Abort.

(** In outline, the high level structure of the proof consists of giving notions of presuppositivity for raw rules/raw type theories and closure rules/closure systems, and doing the main inductive construction purely in terms of closure systems.

The low-level hard work is showing that the raw rules / closure conditions arising from type theories really are presuppositive in the appropriate sense. *)


Section PresuppositivityRaw.
(** In this section, we show how presuppositivity transfers between the raw world and the closure-system world. *)

  Context {σ : scope_system} `{Funext}.

  (** A raw type theory is presuppositive if all its rules are (weakly) presuppositive over it.

  (One might be tempted to call this “well-typed”, but we don’t, because it’s not really strong enough to imply much about the behaviour of the theory.) *)
  Definition presuppositive_raw_type_theory
      {Σ : signature σ} (T : raw_type_theory Σ)
    : Type
  := forall r : T, weakly_presuppositive_raw_rule T (T r).

  (** If a raw type theory T is presup-closed, then so is its associated closure system. *)
  Theorem closure_system_of_presuppositive_raw_type_theory
      {Σ : signature σ} {T : raw_type_theory Σ}
      (T_presup_closed : presuppositive_raw_type_theory T)
    : Closure.weakly_presuppositive_system presupposition
        (RawTypeTheory.closure_system T).
  Proof.
    intros [r_str | r_log ].
    - intros p.
      refine (Closure.derivation_fmap1 _ _).
      2: { apply is_presuppositive_structural_rule. }
      + apply Closure.map_from_family_map.
        apply Family.sum_fmap.
        * apply Family.idmap.
        * apply Family.Build_map'; intros [[]].
    - destruct r_log as [r r_inst]. cbn in r_inst.
      destruct r_inst as [Γ r_args].
      apply raw_rule_closure_system_weakly_presuppositive.
      apply T_presup_closed.
  Defined.

  (** Putting the above together: all presuppositions of a derivable judgement
      over a presuppositive raw tpye theory are again derivable,
      assuming additionally all presuppositions of the original hypotheses. *)
  Theorem derive_presupposition_from_raw
      {Σ : signature σ}
      {T : raw_type_theory Σ} (H_T : presuppositive_raw_type_theory T)
      {j : judgement Σ} {hyps : family _}
      (d_j : RawTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : RawTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    simple refine
      (Closure.presupposition_derivation presupposition _ d_j _).
    apply closure_system_of_presuppositive_raw_type_theory.
    apply H_T.
  Defined.

End PresuppositivityRaw.

Section Presuppositivity.

  Context {σ : scope_system} `{Funext}.

  Lemma rule_of_well_typed_type_theory_is_well_typed
      {T : presented_raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      (r : T)
    : TypedRule.is_well_typed (PresentedRawTypeTheory.flatten T)
        (PresentedRawRule.fmap (PresentedRawTypeTheory.include_rule_signature r) (tt_rule r)).
  Proof.
    assert (r_WT := T_WT r).
    assert (r'_WT := TypedRule.fmap_is_well_typed
                    (PresentedRawTypeTheory.include_rule_signature _) r_WT).
    refine (TypedRule.fmap_is_well_typed_in_theory _ r'_WT).
    apply RawTypeTheory.map_from_simple_map,
          RawTypeTheory.simple_map_from_family_map.
    eapply Family.compose.
    2: { apply Family.map_from_eq, inverse, RawTypeTheory.fmap_compose. }
    (* - simple map of raw TT’s
       - induces a map (not nec fam map) of raw tt’s
       - simple map f : T —> T':
         for each r : T, some (f r) : T', and something implying flatten
         (T r) derivable from flatten (T r'), stably (i.e. regardless of
         ambient theory)
       - so: simple map of _raw rules_: f : R' —> R: must implies R stably derivable from R'; so, is simple map (premises R —> premises R'), and then conclusion must agree. *)
    apply (Family.map_vs_map_over _ _ _)^-1.
    apply PresentedRawTypeTheory.flatten_initial_segment.
  Defined.

  (** For any raw type theory [T] and a rule [r] of the flattened [T], every
      presupposition in the boundary of the conclusion of [r] can be derived. *)
  Lemma presuppositive_flatten
      {T : presented_raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
    : presuppositive_raw_type_theory (PresentedRawTypeTheory.flatten T).
  Proof.
    (* The flattened [T] has logical and congruence rules, two cases to consider. *)
    (* Do these have to be treated separately, or can they be unified better? *)
    intros [r|r]; apply TypedRule.weakly_presuppositive_flatten.
    - (* logical rules *)
      apply rule_of_well_typed_type_theory_is_well_typed, T_WT.
    - (* congruence rules *)
      apply congruence_rule_is_well_typed.
      apply rule_of_well_typed_type_theory_is_well_typed, T_WT.
  Defined.

  (** Working in a type theory [T], given a judgement [j] which is derivable
      from hypotheses [hyps], suppose every presupposition [q] of every
      hypothesis [h : hyps] is derivable from [hyps], then every presuppsition
      [p] of [j] is derivable from [hyps].
   \cref{thm:presuppositions}
   *)
  Theorem derive_presupposition
      {T : presented_raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      {j : judgement (PresentedRawTypeTheory.signature T)}
      {hyps : family _}
      (dj : PresentedRawTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : PresentedRawTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    apply derive_presupposition_from_raw; try assumption.
    apply presuppositive_flatten, T_WT.
  Defined.

  (** Over a well-typed type theory [T],
      if a judgment [j] is derivable without hypotheses,
      then every presupposition of [j] is also derivable. *)
  Corollary derive_presupposition_closed
      {T : presented_raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
      {j : judgement (PresentedRawTypeTheory.signature T)}
      (dj : PresentedRawTypeTheory.derivation T [<>] j)
      {p : presupposition j }
    : PresentedRawTypeTheory.derivation T [<>] (presupposition j p).
  Proof.
    refine (Closure.graft _ _ _).
    - refine (derive_presupposition T_WT dj).
    - intros i; recursive_destruct i.
  Defined.

End Presuppositivity.
