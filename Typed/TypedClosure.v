Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.

(** Some general machinery stated purely in terms of closure systems, but given
    here rather than in [Auxiliary.Closure] since it is motivated very
    specifically by the example of typing derivations.
*)

Section WellTypedClosureSystem.

  Context {X : Type} (P : X -> family X).
  (* Throughout, the motivating example is
     [X := judgement Σ]
     [P j := presupposition j]. *)

  (** A closure rule [r] is well-typed with respect to [P] and a closure system
      [C] when

      - for every premise [p] of [r], if [p_presup] is a proof that [P] holds
        for [p], then there is a [C]-derivation of [p_presup] from the premises
        of [r]

      - if [p_presup] is a proof that [P] holds for the conclusion of [r], then
        there is a [C]-derivation of [p_presup] from the premises of [r] *)
  Local Definition well_typed_rule (C : Closure.system X) (r : Closure.rule X)
    : Type
  := (forall (p : Closure.rule_premises r) (p_presup : P (Closure.rule_premises r p)),
      Closure.derivation C (Closure.rule_premises r) (P _ p_presup))
     *
     (forall (c_presup : P (Closure.rule_conclusion r)),
       Closure.derivation C (Closure.rule_premises r) (P _ c_presup)).

  (** A cosure system [C] is well-typed if every rule [r] of [C] is well typed. *)
  Local Definition well_typed (C : Closure.system X) : Type
  := forall r : C, well_typed_rule C (C r).

  (** Weaker form of well-typedness where we require only that the premises of
      each rule are suitably closed. (Note: the premises of a rule should be
      thught of as the boundary of the conclusion.) *)
  Local Definition well_typed_boundary (C : Closure.system X) : Type
  := forall (r : C) (c_presup : P (Closure.rule_conclusion (C r))),
      Closure.derivation C (Closure.rule_premises (C r)) (P _ c_presup).

  (** If  *)
  Local Definition well_typed_has_well_typed_boundary (C : Closure.system X)
    : well_typed C -> well_typed_boundary C.
  Proof.
    intros H_w r p.
    refine (snd (H_w r) p).
  Defined.

  (** Given a closure system [C] with a well-typed boundary and hypotheses [H]
      that are also closed for [P], any derivation [d] of [x] from [H] is
      also closed for [P]. *)
  Theorem presupposition_derivation
      {C : Closure.system X}
      (C_b_closed : well_typed_boundary C)
      {H : family X}
      (H_P_closed : forall (h : H) (p : P (H h)),
          Closure.derivation C H (P _ p))
      {x : X} (d : Closure.derivation C H x) (p : P x)
    : Closure.derivation C H (P _ p).
  Proof.
    destruct d as [ x_hyp | r d_r_prems].
    - (* case: derivqtion was just finding [j] as a hypothesis *)
      apply H_P_closed.
    - (* case: derivation ended with a rule of [T] *)
      simple refine (Closure.graft _ _ _).
      + exact (Closure.rule_premises (C r)).
      + apply C_b_closed.
      + apply d_r_prems.
  Defined.

End WellTypedClosureSystem.
