Require Import HoTT.
Require Import Syntax.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.RawRule.
Require Import Typing.FlatTypeTheory.

(* TODO: upstream to [Closure]?  Perhaps make some names local? *)
Section Derivation_Step.
(* Definition of the steps of a derivation, and various utility functions around them. *)

  (** Specialised types for indexing steps of a derivation *)
  Inductive step_unit : Type := step_hypothesis.
  Inductive step_deduce {X : Type} (Y : X -> Type)
    := step_conclusion | step_premise (x:X) (y : Y x).

  (** Steps of a derivation (in a general closure system) *)
  Fixpoint step {X} {C : Closure.system X}
      {H} {x} (d : derivation C H x)
    : Type.
  Proof.
    destruct d as [ h | r d_prems ].
    - exact step_unit.
    - exact (step_deduce (fun p => step _ _ _ _ (d_prems p))).
  Defined.
  (* NOTE: a possible alternative that might give better computational behaviour, but seems conceptually less accurate:

   always use [step_deduce], before destructing on [d], and then give the empty family of premises in case [d] is a hypothesis.  (Of course in this case [step_unit] should be deleted, and [step_deduce] probably renamed.)

  Advantage: [step] is a more usable type without having to always destruct [d].*)

  (** The justification of each step of a derivation, i.e. either a hypothesis or a rule *)
  Fixpoint justification {X} {C : Closure.system X}
      {H} {x} {d : derivation C H x} (i : step d) {struct d}
    : H + C.
  Proof.
    destruct d as [ h | r d_prems ].
    - exact (inl h).
    - destruct i as [ | p j].
      + exact (inr r).
      + exact (justification _ _ _ _ (d_prems p) j). 
  Defined.

  (** The label at each step of a derivation (e.g. the judgement, in the case of typing derivations). *)
  (* TODO: name not ideal; think of better one? “state”?  “judgement”? *)
  Fixpoint step_label {X} {C : Closure.system X}
      {H} {x} {d : derivation C H x} (i : step d) {struct d}
    : X.
  Proof.
    set (e := fun x => x = d).
    destruct d as [ h | r ? ].
    - exact (H h).
    - destruct i as [ | p j].
      + exact (conclusion (C r)).
      + exact (step_label _ _ _ _ _ j).
  Defined.

  (** Property of _being a rule_, for steps of a derivation. *)
  (* NOTE: should probably be upgraded to go via booleans, or decidable hprops, or a custom 2-element type… *)  
  Definition is_rule {X} {C : Closure.system X}
      {H} {x} {d : derivation C H x} (i : step d)
    := match (justification i) with inr _ => Unit | inl _ => Empty end.

  (** Family of occurrences of rules in a derivation. *)
  Definition rule_occurrence {X} {C : Closure.system X}
      {H} {x} (d : derivation C H x)
    : family C.
  Proof.
    exists { i : step d & is_rule i }.
    intros [i H_i]. unfold is_rule in H_i.
    destruct (justification i) as [ h | r ] in *.
    - destruct H_i.
    - exact r.
  Defined.

  (** Property of _being a hypothesis_, for steps of a derivation. *)
  (* NOTE: should probably be upgraded to go via booleans, or decidable hprops, or a custom 2-element type… *)  
  Definition is_hypothesis {X} {C : Closure.system X}
      {H} {x} {d : derivation C H x} (i : step d)
    := match (justification i) with inl _ => Unit | inr _ => Empty end.

  (** Family of occurrences of hypotheses in a derivation. *)
  Definition hypothesis_occurrence {X} {C : Closure.system X}
      {H} {x} (d : derivation C H x)
    : family H.
  Proof.
    exists { i : step d & is_hypothesis i }.
    intros [i H_i]. unfold is_hypothesis in H_i.
    destruct (justification i) as [ h | r ] in *.
    - exact h.
    - destruct H_i.
  Defined.
  
End Derivation_Step.




Section Cut_Freeness.
  
  Context {σ : shape_system}.

  (* Is a rule an instance of [cut] ? *)
  Definition is_cut {Σ : signature σ}
      {T : flat_type_theory Σ} (r : FlatTypeTheory.closure_system T)
    : Type.
  Admitted.

  (* NOTE: “occurrence” is included because “cut_main_premise” would more naturally refer to the judgement that’s the main premise in the rule (independent of any particular derivation). *)
  Definition cut_occurrence_main_premise {Σ} {T : flat_type_theory Σ}
       {j} {H} {d : FlatTypeTheory.derivation T H j}
       (r : rule_occurrence d) (r_cut : is_cut (rule_occurrence d r))
    : step d.
  Admitted.

  (** Cut-freeness of derivations.

  For closed derivations, “cut-free” really means cut-free.

  For derivations with arbitrary hypotheses, completely cut-free would be too strong a property to require; so in general we allow cut, but only directly into hypotheses. *)
  Definition cut_free {Σ : signature σ} {T : flat_type_theory Σ}
      {j} {H} (d : FlatTypeTheory.derivation T H j)
    : Type
  := (forall (r : rule_occurrence d) (r_cut : is_cut (rule_occurrence d r)),
         is_hypothesis (cut_occurrence_main_premise _ r_cut)).

End Cut_Freeness.

Section Cut_Elimination.

  Context {σ : shape_system}.

  Theorem cut_elimination {Σ : signature σ} {T : flat_type_theory Σ}
      {j} {H} (d : FlatTypeTheory.derivation T H j)
    : { d' : FlatTypeTheory.derivation T H j & cut_free d' }.
  Proof.
(* Sketch proof: start by roughly paralleling our definition of substitution, then do the main induction.  In detail,

  Lemma 1. given a cut-free derivation of a judgement J and a renaming of variables of the context of J, can rename throughout derivation to get a cut-free derivartion of the renamed judgement.

  Lemma 2. given a cut-free derivation of a judgement J, and a context map into the context of J with cut-free typing derivations of the terms in the context map, can substitute throughout derivation to get a cut-free derivartion of the substituted judgement, using Lemma 1 when going under binders.

  Lemma 3. the main induction to cut-eliminate in all proofs: if the last rule is anything apart from cut, then just cut-eliminate the subderivations inductively; if last rule is a cut into a hypothesis, then cut-eliminate the subderivations of well-typedness of the substitution; if last rule is a cut into a non-hypothesis, then cut-eliminate the derivations of the substitution and the main premise, and then substitute the substitution into the cut-free derivation of the main premise using Lemma 2. *)

  Admitted.

End Cut_Elimination.

