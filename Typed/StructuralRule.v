Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.StructuralRule.
Require Import Typed.Closure.
Require Import Typed.Derivation.
Require Import Typed.FlatRule.

(** Main goal for this file: show all the structural rules are well-typed.

For the ones stated as flat rules, this means showing they’re well-typed as such: i.e. showing that whenever their premises hold, then all the presuppositions of both their premises and conclusion hold. *)

Section Welltypedness.

  Context {σ : shape_system} {Σ : signature σ}.

  (** Main goal of this section: show that all structural rules are well-typed,
  in the sense that whenever their premises are derivable, all the presuppositions of their premises/conclusion are derivable. *)
  Lemma well_typed
    : Closure.well_typed presupposition (StructuralRule.Structural_CCs Σ).
  Abort.

  Context (C := Structural_CCs Σ).

  (* TODO: upstream, and fold into [Structural_CCs] *)
  Definition var_ccs := FlatRule.closure_system (var_flat_rule Σ).

  (* TODO: upstream, and fold into [Structural_CCs] *)
  Definition equality_ccs := 
    Family.bind (Equality_Flat_Rules Σ) FlatRule.closure_system.

  Lemma context_ccs_well_typed
    : forall r : context_ccs Σ,
      Closure.rule_well_typed presupposition C (context_ccs _ r).
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
    : forall r : subst_ccs Σ,
      Closure.rule_well_typed presupposition C (subst_ccs _ r).
  Admitted.

  Lemma var_rule_ccs_well_typed
    : forall r : var_ccs,
      Closure.rule_well_typed presupposition C (var_ccs r).
  Proof.
    (* deduce from showing this is well-typed as flat rule *)
  Admitted.

  Lemma equality_rule_ccs_well_typed
    : forall r : equality_ccs,
      Closure.rule_well_typed presupposition C (equality_ccs r).
  Proof.
    (* deduce from showing these are well-typed as flat rules *)
  Admitted.

  (** Putting the above components together, we obtain the main section goal:
  all structural rules are well-typed. *)
  Local Lemma well_typed
    : Closure.well_typed presupposition (Structural_CCs Σ).
  Proof.
    unfold Structural_CCs.
    intros [ [ [ r_cxt | r_subst ] | r_var ] | r_eq ].
    - apply context_ccs_well_typed.
    - apply subst_ccs_well_typed.
    - apply var_rule_ccs_well_typed.
    - apply equality_rule_ccs_well_typed.
  Defined.

End Welltypedness.