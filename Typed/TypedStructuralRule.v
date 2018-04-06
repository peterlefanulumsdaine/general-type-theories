Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawStructuralRule.
Require Import Typed.TypedClosure.
Require Import Raw.FlatTypeTheoryMap.
Require Import Raw.FlatRule.

(** We show that all the structural rules are well-typed.

   For the ones stated as flat rules, this means showing they’re well-typed as such: i.e.
   showing that whenever their premises hold, then all the presuppositions of both their
   premises and conclusion hold.
*)

Section TypedStructuralRule.

  Context {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement well-typed in the sense
      that its presuppositions are derivable using structural rules? *)
  Local Definition is_well_typed : Closure.rule (judgement_total Σ) -> Type
  := TypedClosure.weakly_well_typed_rule Judgement.presupposition (structural_rule Σ).

  (** Context rules are well typed. *)
  Local Definition ctx_is_well_typed (r : RawStructuralRule.context Σ)
    : is_well_typed (RawStructuralRule.context _ r).
  Proof.
    apply TypedClosure.weakly_from_strongly_well_typed_rule.
    destruct r as [  [Γ A] | ].
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

  (** Substitution rules are well typed *)
  Local Definition subst_is_well_typed (r : RawStructuralRule.substitution Σ)
    : is_well_typed (RawStructuralRule.substitution _ r).
  Proof.
    cbn in r.
    destruct r as [Γ [ Γ' [ f [ hjf J]]] | Γ [Γ' [f [f' [cl j]]]]].
    - admit. (* substituting into a judgment *)
    - admit. (* comparing substitutions along equal context maps *)
  (* NOTE: this is not currently true, since premises of subst rules are NOT presupposition-closed!
           
  They satisfy instead a weaker property, which suffices for the presupposition-closure metatheorem: assuming all premises *and their presuppositions*, then all premises of the conclusion are derivable.

  TODO: should we change the statement of the substitution rules to explicitly include presuppositions? *)
  Admitted.

  (** Variable rules are well typed *)
  Local Definition variable_is_well_typed (r : RawStructuralRule.variable Σ)
    : is_well_typed (RawStructuralRule.variable _ r).
  Proof.
    (* deduce from showing this is well-typed as flat rule *)
  Admitted.

  (** Equality rules are well typed *)
  Local Definition equality_is_well_typed (r : RawStructuralRule.equality Σ)
    : is_well_typed (RawStructuralRule.equality _ r).
  Proof.
    (* deduce from showing these are well-typed as flat rules *)
  Admitted.

  (** Putting the above components together, we obtain the main result:
      all structural rules are well-typed. *)
  Local Definition well_typed
    : TypedClosure.weakly_well_typed_system Judgement.presupposition (structural_rule Σ).
  Proof.
    intros [ [ [ r_cxt | r_subst ] | r_var ] | r_eq ].
    - apply ctx_is_well_typed.
    - apply subst_is_well_typed.
    - apply variable_is_well_typed.
    - apply equality_is_well_typed.
  Defined.

End TypedStructuralRule.
