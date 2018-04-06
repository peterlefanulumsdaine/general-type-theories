Require Import HoTT.
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

  (** A closure rule [r] is strongly well-typed over a closure system [C]
      when all presuppositions of both the premises and the conclusion are
      derivable over [C] from the premises.  Spelled out in more detail:

      - for each presupposition [p_presup] of a premise [p] of [r], there is a
        [C]-derivation of [p_presup] from the premises of [r]; and

      - for each presupposition [c_presup] of the conclusion of [r],
        there is a [C]-derivation of [c_presup] from the premises of [r].
  *)
  Local Definition strongly_well_typed_rule (C : Closure.system X) (r : Closure.rule X)
    : Type
  := (forall (p : Closure.rule_premises r) (p_presup : presup (Closure.rule_premises r p)),
      Closure.derivation C (Closure.rule_premises r) (presup _ p_presup))
     *
     (forall (c_presup : presup (Closure.rule_conclusion r)),
       Closure.derivation C (Closure.rule_premises r) (presup _ c_presup)).

  (** A closure rule [r] is weakly well-typed over a closure system [C] if
      all presuppositions of the conclusion are derivable over [C] from 
      the premises plus all their presuppositions. 

      So compared to strong well-typedness, we only derive the presuppositions
      of the conclusion (not of the premises); and in those derivations, we
      additionally assume all presuppositions of the premises.
   *)
  Local Definition weakly_well_typed_rule (C : Closure.system X) (r : Closure.rule X)
    : Type
  := (forall (c_presup : presup (Closure.rule_conclusion r)),
         Closure.derivation C
           (Closure.rule_premises r + (Family.bind (Closure.rule_premises r) presup))
           (presup _ c_presup)).

  (** Strongly well-typed implies weakly well-typed. *)
  Local Definition weakly_from_strongly_well_typed_rule
      (C : Closure.system X) (r : Closure.rule X)
    : strongly_well_typed_rule C r -> weakly_well_typed_rule C r.
  Proof.
    intros H_r. apply snd in H_r. (* we only need the second half of [H_r] *)
    intro c_presup.
    apply (Closure.graft _ (H_r c_presup)).
    intros i. refine (Closure.hypothesis _ (_ + _) (inl i)).
  Defined.

  (** A closure system [C] is strongly well-typed if all its rules are. *)
  Local Definition strongly_well_typed_system (C : Closure.system X) : Type
  := forall r : C, strongly_well_typed_rule C (C r).

  (** Similarly, a closure system [C] is weakly well-typed if all its rules are. *)
  Local Definition weakly_well_typed_system (C : Closure.system X) : Type
  := forall r : C, weakly_well_typed_rule C (C r).

  (** Strongly well-typed implies weakly well-typed. *)
  Local Definition weakly_from_strongly_well_typed_system (C : Closure.system X)
    : strongly_well_typed_system C -> weakly_well_typed_system C.
  Proof.
    intros H_C r. apply weakly_from_strongly_well_typed_rule, H_C.
  Defined.

  (** Given a weakly well-typed closure system [C], and a derivation [D] over [C]
      with conclusion [x] and hypotheses [H], we can also derive any
      presupposition of [x], from [H] plus its presuppositions. *)
  Theorem presupposition_derivation
      {C : Closure.system X}
      (C_weakly_well_typed : weakly_well_typed_system C)
      {H : family X} {x : X} (d : Closure.derivation C H x)
      (x_presup : presup x)
    : Closure.derivation C (H + (Family.bind H presup)) (presup _ x_presup).
  Proof.
    induction d as [ x_hyp | r d_r_prems IH].
    - (* case: derivqtion was just finding [p] as a hypothesis *)
      refine (hypothesis _ (_ + Family.bind _ _) (inr (_ ; _))).
    - (* case: derivation ended with a rule of [T] *)
      refine (Closure.graft _ _ _).
      + apply C_weakly_well_typed.
      + intros [ p | [p p_presup]].
        * refine (Closure.graft _ (d_r_prems _) _).
          intros i. refine (Closure.hypothesis _ (_ + _) (inl i)).
        * apply IH.
  Defined.

End WellTypedClosureSystem.
