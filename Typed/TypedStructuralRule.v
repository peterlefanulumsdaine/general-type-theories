Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawStructuralRule.
Require Import Typed.TypedClosure.
Require Import Raw.FlatTypeTheoryMap.
Require Import Typed.FlatRule.

(** Main goal for this file: show all the structural rules are well-typed.

   For the ones stated as flat rules, this means showing they’re well-typed as such: i.e.
   showing that whenever their premises hold, then all the presuppositions of both their
   premises and conclusion hold.
*)

Section TypedStructuralRule.

  Context {σ : shape_system} {Σ : signature σ}.

  (** Main goal of this section: show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)
  Lemma well_typed
    : TypedClosure.well_typed Judgement.presupposition (structural_rule Σ).
  Abort.

  Context (C := structural_rule Σ).


  Lemma context_ccs_well_typed
    : forall r : RawStructuralRule.context Σ,
      TypedClosure.well_typed_rule Judgement.presupposition C (RawStructuralRule.context _ r).
  Proof.
    intros r. destruct r as [  [Γ A] | ].
    - split. (* context extension *)
      + intros [ [ [] | ] | ]. (* two premises *)
        * intros []. (* context hypothesis: no presups *)
        * intros [ [] | ]. (* type hypothesis: one presup *)
          eapply transport. 
          Focus 2. { refine (Closure.hypothesis _ _ _). 
            cbn. apply (Some (None)). } Unfocus.
          apply idpath.
      + intros []. (* conclusion: no presups *)
    - split. (* empty context rule *)
      + intros []. (* no premises *)
      + intros []. (* no presups for conclusion *)
  Defined.

  Lemma subst_ccs_well_typed
    : forall r : RawStructuralRule.substitution Σ,
      TypedClosure.well_typed_rule Judgement.presupposition C (RawStructuralRule.substitution _ r).
  Admitted.

  Lemma var_rule_ccs_well_typed
    : forall r : RawStructuralRule.variable Σ,
      TypedClosure.well_typed_rule Judgement.presupposition C (RawStructuralRule.variable _ r).
  Proof.
    (* deduce from showing this is well-typed as flat rule *)
  Admitted.

  Lemma equality_rule_ccs_well_typed
    : forall r : RawStructuralRule.equality Σ,
      TypedClosure.well_typed_rule Judgement.presupposition C (RawStructuralRule.equality _ r).
  Proof.
    (* deduce from showing these are well-typed as flat rules *)
  Admitted.

  (** Putting the above components together, we obtain the main section goal:
  all structural rules are well-typed. *)
  Local Lemma well_typed
    : TypedClosure.well_typed Judgement.presupposition (structural_rule Σ).
  Proof.
    intros [ [ [ r_cxt | r_subst ] | r_var ] | r_eq ].
    - apply context_ccs_well_typed.
    - apply subst_ccs_well_typed.
    - apply var_rule_ccs_well_typed.
    - apply equality_rule_ccs_well_typed.
  Defined.

End TypedStructuralRule.
