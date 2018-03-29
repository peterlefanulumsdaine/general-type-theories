Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.

(** Main theorem: [presupposition_derivable]: the presuppositions of any derivable judgement are again derivable. *)
Section Presuppositions_Derivable.

  Context {σ : shape_system}.

  (* TODO: make Σ implicit in fields of [flat_rule] *)
  Definition presupposition_closed
      {Σ : signature σ} (T : flat_type_theory Σ)
    : Type.
  Proof.
    refine (forall r : T, _ (T r)). clear r; intros r.
    refine (Derivation_Judgt_Bdry_Instance _
              (boundary_of_judgement _) (flat_rule_premises _ r)).
    - exact (fmap_flat_type_theory include_symbol T). 
    - exact (pr2 (flat_rule_conclusion _ r)).
  Defined.

  Theorem closure_system_of_presupposition_closed_flat_type_theory
      {Σ : signature σ} {T : flat_type_theory Σ}
      (T_presup_closed : presupposition_closed T)
      (C := CCs_of_Flat_Type_Theory T)
      (P := fun (j : judgement_total Σ) => presupposition (pr2 j))
    : forall (r : C) (p : P (Closure.rule_conclusion (C r))),
          Closure.derivation C (Closure.rule_premises (C r)) (P _ p).
  Proof.
    
  Admitted.

   (* if a flat type theory T is presup-closed, then so is its associated closure system. *)

  Theorem presupposition_derivation_from_closure_system
      {X : Type} (P : X -> family X)
      {C : Closure.system X}
      (C_P_closed : forall (r : C) (p : P (Closure.rule_conclusion (C r))),
          Closure.derivation C (Closure.rule_premises (C r)) (P _ p))
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

  (* TODO: perhaps change def of flat rules to allow only _hypothetical_ judgements? *)
  Theorem presupposition_derivation_from_flat
      {Σ : signature σ}
      {T : flat_type_theory Σ} (T_presup_closed : presupposition_closed T)
      {j : judgement_total Σ} {hyps : family _}
      (d_j : Derivation_from_Flat_Type_Theory T hyps j)
      (d_hyp_presups :
         forall (h : hyps) (p : presupposition (pr2 (hyps h))),
           Derivation_from_Flat_Type_Theory T hyps (presupposition _ p))
      {p : presupposition (pr2 j) }
    : Derivation_from_Flat_Type_Theory T hyps (presupposition _ p).
  Proof.
    refine (presupposition_derivation_from_closure_system
              (fun j => presupposition j.2) _ _ _ _).
    - apply closure_system_of_presupposition_closed_flat_type_theory.
      apply T_presup_closed.
    - apply d_hyp_presups.
    - apply d_j.
    (* Idea: abstract out to the level of closure systems first. *)
  Defined.

  Lemma presupposition_closed_flatten {T : Type_Theory σ}
    : presupposition_closed (TypeTheory.flatten T).
  Proof.
  Admitted.

  (* TODO: at least make access function between [judgment] and [judgement_total]; perhaps make it a coercion? *)
  Theorem presupposition_derivation {T : Type_Theory σ}
      {j : judgement_total (Signature_of_Type_Theory T)}
      {hyps : family _}    
      (dj : Derivation_from_Type_Theory T hyps j)
      (d_hyp_presups :
         forall (h : hyps) (p : presupposition (pr2 (hyps h))),
           Derivation_from_Type_Theory T hyps (presupposition _ p))
      {p : presupposition (pr2 j) }
    : Derivation_from_Type_Theory T hyps (presupposition (pr2 j) p).
  Proof.
    apply presupposition_derivation_from_flat; try assumption.
    apply presupposition_closed_flatten.
  Defined.

  Corollary closed_presupposition_derivation {T : Type_Theory σ}
      {j : judgement_total (Signature_of_Type_Theory T)}
      (dj : Derivation_from_Type_Theory T [<>] j)
      {p : presupposition (pr2 j) }
    : Derivation_from_Type_Theory T [<>] (presupposition (pr2 j) p).
  Proof.
    apply presupposition_derivation; try assumption.
    intros [].
  Defined.

  (* Sketch proof:

  - this should hold for flat type theories, provided their flat rules have the property that all the presuppositions of the conclusion are derivable assuming the premises
  - then, all flat rules produced from real rules should have that property.
  *)

End Presuppositions_Derivable.
  