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
Require Import Raw.FlatTypeTheoryMap.
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

  (* TODO: make Σ implicit in fields of [flat_rule] *)
  (** A flat rule is presupposition-closed, over an ambient flat theory [R],
     if all presuppositions of its conclusion are derivable from
     the premises together with their presuppositions,
     over [T] (translated up to the metavariable-extension signature) *)
  Definition presupposition_closed_flat_rule {Σ : signature σ}
      (T : flat_type_theory Σ) (r : flat_rule Σ)
    : Type
  := forall i : presupposition (flat_rule_conclusion _ r), 
      FlatTypeTheory.derivation
        (FlatTypeTheory.fmap include_symbol T)
        (flat_rule_premises _ r + (Family.bind (flat_rule_premises _ r) presupposition))
        (presupposition _ i).

  (** A flat type theory is presupposition-closed if all its rules are. *)
  Definition presupposition_closed_flat_type_theory
      {Σ : signature σ} (T : flat_type_theory Σ)
    : Type
  := forall r : T, presupposition_closed_flat_rule T (T r).

  (** If a flat type theory T is presup-closed, then so is its associated closure system. *)
  Theorem closure_system_of_presupposition_closed_flat_type_theory
      {Σ : signature σ} {T : flat_type_theory Σ}
      (T_presup_closed : presupposition_closed_flat_type_theory T)
    : TypedClosure.weakly_well_typed_system presupposition (FlatTypeTheory.closure_system T).
  Proof.
    intros [r_str | r_log ].
    - intros p.
      refine (Closure.map_derivation _ _).
      Focus 2. { apply TypedStructuralRule.well_typed. } Unfocus.
      apply Closure.map_from_family_map, Family.inl.
    - destruct r_log as [r r_inst]. cbn in r_inst.
      destruct r_inst as [Γ r_args].
      unfold TypedClosure.weakly_well_typed_rule.
      intros p.
      eapply transport. 
      { apply instantiate_presupposition. }
      refine (Closure.graft _ _ _).
      + refine (FlatTypeTheory.instantiate_derivation _ _ _ _).
        apply T_presup_closed.
      + intros [ i | [ i i_presup]]. 
        * eapply (flip (transport _)).
          { refine (Closure.hypothesis _ _ _). exact (inl i). }
          apply idpath.
        * eapply (flip (transport _)).
          { refine (Closure.hypothesis _ _ _). refine (inr (i;_)).
            exact i_presup. }
          apply inverse, instantiate_presupposition.
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
  Lemma presupposition_closed_flatten {T : raw_type_theory σ}
    : presupposition_closed_flat_type_theory (RawTypeTheory.flatten T).
  Proof.
    (* The flattened [T] has logical and congruence rules, two cases to consider. *)
    intros [r|r].
    - {
        (* [r] is a logical rule, we consider one of the presuppositions [p] of the conclusion. *)
        intros p.
        (* We must show that [p] has a derivation. *)
        destruct (flat_rule_conclusion _ ((RawTypeTheory.flatten T) (inl r))) as [[|hjf] j].
        - (* [p] is in the boundary of the presupposition that the context of the conclusion
            is well -formed, whose boundary is empty. There is no such [p]. *)
            elim p.
        - { destruct hjf as [[|]|eq].
            + (* p is a position in the boundary of "is a type" judgement.
                There is one position, namely the context. *)
              destruct p as [[]|].
              (* We need to show that the context of the conclusion is well-formed. *)
              destruct j as [j_ctx j_jdg].
              admit.
            + admit.
            + admit.
          }
      }
  Admitted.

  (* TODO: at least make access function between [judgment] and [judgement_total]; perhaps make it a coercion? *)
  (** Working in a type theory [T], given a judgement [j] which is derivable
      from hypotheses [hyps], suppose every presupposition [q] of every hypothesis [h : hyps]
      is derivable from [hyps], then every presuppsition [p] of [j] is derivable from
      [hyps]. *)
  Theorem derive_presupposition {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      {hyps : family _}
      (dj : RawTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : RawTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    apply derive_presupposition_from_flat; try assumption.
    apply presupposition_closed_flatten.
  Defined.

  (** Working in a type theory [T], given a judgment [j] which is derivable
      without hypotheses, ever presupposition of [j] is derivable. *)
  Corollary derive_presupposition_closed {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      (dj : RawTypeTheory.derivation T [<>] j)
      {p : presupposition j }
    : RawTypeTheory.derivation T [<>] (presupposition j p).
  Proof.
    refine (Closure.graft _ _ _).
    - refine (derive_presupposition dj).
    - intros i. recursive_destruct i.
  Defined.

End PresuppositionClosure.
