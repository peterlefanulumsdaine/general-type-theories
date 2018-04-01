Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.

(** Some general machinery stated purely in terms of closure systems, but given here rather than in [Auxiliary.Closure] since it is motivated very specifically by the example of typing derivations. *)

Section Welltypedness.

  Context {X : Type} (P : X -> family X).
  (* Throughout, the motivating example is
     [X := judgement Σ]
     [P j := presupposition j]. *)

  (** Well-typedness of a closure condition, under an ambient closure system:
  derivations of the presuppositions of all the premises + conclusion,
  assuming the premises. *)
  (* TODO: possible make record type? *)
  Local Definition rule_well_typed (C : Closure.system X) (r : Closure.rule X)
    : Type
  := (forall (p : Closure.rule_premises r) (p_presup : P (Closure.rule_premises r p)),
      Closure.derivation C (Closure.rule_premises r) (P _ p_presup))
     *
     (forall (c_presup : P (Closure.rule_conclusion r)),
       Closure.derivation C (Closure.rule_premises r) (P _ c_presup)).

  (** Well-typedness of a closure system: well-typedness of all the rules, under the whole system. *)
  Local Definition well_typed (C : Closure.system X) : Type
  := forall r : C, rule_well_typed C (C r).

  (** Weaker form of well-typedness: only check the boundary of the conclusion. *)
  Local Definition presupposition_closed (C : Closure.system X)
    : Type
  := forall (r : C) (concl_presup : P (Closure.rule_conclusion (C r))),
          Closure.derivation C (Closure.rule_premises (C r)) (P _ concl_presup).

  (** Presupposition-closedness is a weakening of well-typedness: *)
  Local Lemma well_typed_implies_presupposition_closed (C : Closure.system X)
    : well_typed C -> presupposition_closed C.
  Proof.
    intros H_w r p.
    refine (snd (H_w r) p).
  Defined.

  (** Given a presupposition-closed closure system and hypotheses,
   the set of derivable judgements from these is also presupposition-closed. *)
  Theorem presupposition_derivation
      {C : Closure.system X}
      (C_P_closed : presupposition_closed C)
      {H : family X}
      (H_P_closed : forall (h : H) (p : P (H h)),
          Closure.derivation C H (P _ p))
      {x : X} (d_x : Closure.derivation C H x) (p : P x)
    : Closure.derivation C H (P _ p).
  Proof.
    destruct d_x as [ x_hyp | r d_r_prems].
    - (* case: derivqtion was just finding [j] as a hypothesis *)
      apply H_P_closed.
    - (* case: derivation ended with a rule of [T] *)
      simple refine (Closure.graft _ _ _).
      + exact (Closure.rule_premises (C r)).
      + apply C_P_closed.
      + apply d_r_prems.
  Defined.

End Welltypedness.