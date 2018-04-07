Require Import HoTT.
Require Import Auxiliary.General.
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

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement well-typed in the sense
      that its presuppositions are derivable using structural rules? *)
  Local Definition is_well_typed : Closure.rule (judgement_total Σ) -> Type
  := TypedClosure.weakly_well_typed_rule presupposition (structural_rule Σ).

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
          eapply (flip (transport _)). 
          { refine (Closure.hypothesis _ _ _). 
            cbn. apply (Some (None)). }
          apply idpath.
      + intros []. (* conclusion: no presups *)
    - split. (* empty context rule *)
      + intros []. (* no premises *)
      + intros []. (* no presups for conclusion *)
  Defined.

  (** Substitution-application rules are well typed *)
  Local Definition subst_apply_is_well_typed
        (r : RawStructuralRule.subst_apply Σ)
    : is_well_typed (RawStructuralRule.subst_apply _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ hjf J]]]].
    intros p.
    transparent assert (j : (judgement_total Σ)).
      { exists (form_hypothetical hjf). refine (Γ;J). }
    transparent assert (p' : (presupposition j)).
      { exact p. }
    destruct p as [ p | ].
    - (* [p] a hypothetical presupposition *)
      eapply (flip (transport _)).
      + simple refine (Closure.deduce _ _ _ _).
        (* Aim here: apply the same substitution rule, with the same substition,
           but with target the presupposition [p] of the original target. *)
        * refine (inl (inl (inr _))).
          (* TODO: give access functions for locating the structural rules! *)
          apply inl. exists Γ, Γ', f.
          exists (form_object (Judgement.boundary_slot _ p)).
          exact (pr2 (pr2 (presupposition _ p'))).
        * intros [ q | ].
          -- (* premises: show the substitution OK. *)
            eapply (flip (transport _)).
            ++ refine (Closure.hypothesis _ _ _). exact (inl (Some q)).
            ++ apply idpath.
          -- (* premises: new presupposition *)
            eapply (flip (transport _)).
            ++ refine (Closure.hypothesis _ _ _). exact (inr (None; p')).
            ++ apply idpath.
      + simple refine (path_sigma _ _ _ _ _).
        { apply idpath. } (* judgement form of new conclusion is same as old *)
        simple refine (path_sigma _ _ _ _ _).
        { apply idpath. } (* context of new conclusion also the same *)
        refine (path_forall _ _ _).
        intros i.
        recursive_destruct hjf; recursive_destruct p; recursive_destruct i;
          apply idpath.
    - (* [p] the context presupposition [Γ'] *)
      eapply (flip (transport _)).
      { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
      apply idpath.
  Defined.

  (** Substitution-equality rules are well typed *)
  Local Definition subst_equal_is_well_typed
        (r : RawStructuralRule.subst_equal Σ)
    : is_well_typed (RawStructuralRule.subst_equal _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ f' [cl J]]]]].
  Admitted.

  (** All substitution rules are well typed *)
  Local Definition subst_is_well_typed (r : RawStructuralRule.substitution Σ)
    : is_well_typed (RawStructuralRule.substitution _ r).
  Proof.
    destruct r as [ r_apply | r_equal ].
    - apply subst_apply_is_well_typed.
    - apply subst_equal_is_well_typed.
  Defined.

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
    : TypedClosure.weakly_well_typed_system presupposition (structural_rule Σ).
  Proof.
    intros [ [ [ r_cxt | r_subst ] | r_var ] | r_eq ].
    - apply ctx_is_well_typed.
    - apply subst_is_well_typed.
    - apply variable_is_well_typed.
    - apply equality_is_well_typed.
  Defined.

End TypedStructuralRule.
