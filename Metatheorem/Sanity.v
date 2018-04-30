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
Require Import Typed.TypedClosure.
Require Import Typed.TypedStructuralRule.
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


  (** For any raw type theory [T] and a rule [r] of the flattened [T], every
      presupposition in the boundary of the conclusion of [r] can be derived. *)
  Lemma presupposition_closed_flatten
      {T : raw_type_theory σ} (T_WT : TypeTheory.is_well_typed T)
    : presupposition_closed_flat_type_theory (RawTypeTheory.flatten T).
  Proof.
    (* The flattened [T] has logical and congruence rules, two cases to consider. *)
    (* Hopefully these cases can be treated uniformly by a lemma that [RawRule.flatten]
       applied to a well-typed rule is presupposition-closed; but that is a bit subtle
       to state/use, due to the translation between signatures involved. *)
    intros [r|r]; apply TypedRule.weakly_well_typed_flatten.
    - assert (r_WT := T_WT r).
      admit.
  (* Detailed sketch:
We need to get from

  TypedRule.is_well_typed_rule
    (FlatTypeTheory.fmap (RawTypeTheory.subtheory_signature T r)
       (RawTypeTheory.flatten (RawTypeTheory.subtheory T r))) 
    (T.(tt_rule) r)

to

  TypedRule.is_well_typed_rule (RawTypeTheory.flatten T)
    (RawRule.fmap (RawTypeTheory.include_rule_signature r) (T.(tt_rule) r)).

We have signature maps

  RawTypeTheory.subtheory_signature
    : (RawTypeTheory.signature (RawTypeTheory.subtheory T i))
    -> (tt_rule_signature i)

  RawTypeTheory.include_rule_signature 
    : (tt_rule_signature i)
    -> (RawTypeTheory.signature (RawTypeTheory.subtheory T i))

So from fmap of rule well-typedness along the latter, get

  TypedRule.is_well_typed_rule
    (FlatTypeTheory.fmap (RawTypeTheory.subtheory_signature T r)
       (RawTypeTheory.flatten (RawTypeTheory.subtheory T r))) 
    (T.(tt_rule) r)
  ->
  TypedRule.is_well_typed_rule
    (FlatTypeTheory.fmap (RawTypeTheory.include_rule_signature r)
    (FlatTypeTheory.fmap (RawTypeTheory.subtheory_signature T r)
       (RawTypeTheory.flatten (RawTypeTheory.subtheory T r))))
    (RawRule.fmap (RawTypeTheory.include_rule_signature r) (T.(tt_rule) r))

then by a commutativity, this is

  TypedRule.is_well_typed_rule
    (FlatTypeTheory.fmap (RawTypeTheory.include_subtheory_signature T r)
       (RawTypeTheory.flatten (RawTypeTheory.subtheory T r))))
    (RawRule.fmap (RawTypeTheory.include_rule_signature r) (T.(tt_rule) r))

  and then there should be a flat type theory map 
    (FlatTypeTheory.fmap (RawTypeTheory.include_subtheory_signature T r)
       (RawTypeTheory.flatten (RawTypeTheory.subtheory T r))))
  -> 
    (RawTypeTheory.flatten T)

which we can map the well-typedness along.
  *)
    - admit. (* TODO: same as the above, plus lemma that associated congruence rule is well-typed *)
  Admitted.

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
