Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.

(** Some general machinery stated purely in terms of closure systems, but given
    here rather than in [Auxiliary.Closure] since it is motivated very
    specifically by the example of typing derivations.

    Generally, this file consideres closure conditions on a type [X] equipped
    additionally with a map [presup : X -> family X], where [presup x] is
    thought of as the _presuppositions_ of an element [x : X].

    Throughout, the motivating example is the type-theoretic case:
    [X := judgement_total Σ]
    [presup j := presupposition j].
*)

Section WellTypedClosureSystem.

  Context {X : Type} (presup : X -> family X).

  (** A closure rule [r] is (strongly) well-typed over a closure system [C]
      when all presuppositions of both the premises and the conclusion are
      derivable from [C] plus the premises.  Spelled out in more detail:

      - for each presupposition [p_presup] of a premise [p] of [r], there is a
        [C]-derivation of [p_presup] from the premises of [r]

      - for each presupposition [c_presup] of the conclusion of [r],
        there is a [C]-derivation of [c_presup] from the premises of [r].
  *)
  Local Definition well_typed_rule (C : Closure.system X) (r : Closure.rule X)
    : Type
  := (forall (p : Closure.rule_premises r) (p_presup : presup (Closure.rule_premises r p)),
      Closure.derivation C (Closure.rule_premises r) (presup _ p_presup))
     *
     (forall (c_presup : presup (Closure.rule_conclusion r)),
       Closure.derivation C (Closure.rule_premises r) (presup _ c_presup)).

  (** A closure system [C] is well-typed if every rule [r] of [C] is well typed. *)
  Local Definition well_typed (C : Closure.system X) : Type
  := forall r : C, well_typed_rule C (C r).

  (** Weaker form of well-typedness, where we just require derivations of the
   presuppositions of the conclusion (not also of the presuppositions of the
   premises) *)
  Local Definition weakly_well_typed (C : Closure.system X) : Type
  := forall (r : C) (c_presup : presup (Closure.rule_conclusion (C r))),
      Closure.derivation C (Closure.rule_premises (C r)) (presup _ c_presup).

  (** Strongly well-typed implies weakly well-typed. *)
  Local Definition weakly_from_strongly_well_typed (C : Closure.system X)
    : well_typed C -> weakly_well_typed C.
  Proof.
    intros H_w r p.
    refine (snd (H_w r) p).
  Defined.

  (** Given a closure system [C] with a well-typed boundary and hypotheses [H]
      that are also closed for [presup], any derivation [d] of [x] from [H] is
      also closed for [presup]. *)
  Theorem presupposition_derivation
      {C : Closure.system X}
      (C_weakly_well_typed : weakly_well_typed C)
      {H : family X}
      (H_presup_closed : forall (h : H) (p : presup (H h)),
          Closure.derivation C H (presup _ p))
      {x : X} (d : Closure.derivation C H x) (p : presup x)
    : Closure.derivation C H (presup _ p).
  Proof.
    destruct d as [ x_hyp | r d_r_prems].
    - (* case: derivqtion was just finding [j] as a hypothesis *)
      apply H_presup_closed.
    - (* case: derivation ended with a rule of [T] *)
      simple refine (Closure.graft _ _ _).
      + exact (Closure.rule_premises (C r)).
      + apply C_weakly_well_typed.
      + apply d_r_prems.
  Defined.

End WellTypedClosureSystem.
