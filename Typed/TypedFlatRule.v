Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Typed.TypedClosure.
Require Import Raw.Syntax.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.

Section WellTyped.

  Context {σ : shape_system} {Σ : signature σ}.

  (** A flat rule [r] (in ambient signature [Σ], with metavariables [a])
      is well-typed over a flat type theory [T] if all presuppositions of
      the conclusion are derivable from the premises plus their presuppositions, 
      over the translation of [T] to [Σ + a].
   *)
  Local Definition weakly_well_typed (T : flat_type_theory Σ)
      (r : flat_rule Σ)
    : Type
  := forall c_presup : presupposition (flat_rule_conclusion _ r),
      (FlatTypeTheory.derivation
         (FlatTypeTheory.fmap include_symbol T)
         (let H := flat_rule_premises _ r in H + Family.bind H presupposition)
         (presupposition _ c_presup)).

  (** Note: we could give (as we have for closure rules) a stronger notion of
  well-typedness, where we derive the presuppositions of premises as well
  as of the conclusion, and (in all these derivations) we assume just the
  premises as hypotheses, not also their presuppositions.
  *)
End WellTyped.

Section Instantiations.

  Context {σ : shape_system} {Σ : signature σ}.

  Local Lemma closure_system_weakly_well_typed
       (T : flat_type_theory Σ)
       (r : flat_rule Σ) (D_r : weakly_well_typed T r)
       {Γ : raw_context Σ} (I : Metavariable.instantiation (flat_rule_metas _ r) Σ Γ)
    : TypedClosure.weakly_well_typed_rule presupposition
        (FlatTypeTheory.closure_system T)
        (FlatRule.closure_system r (Γ;I)).
  Proof.
    (* Rough idea: derivations translate along the instantiation of syntax,
    so the derivations provided by well-typedness of [r] translate into 
    the derivations required for well-typedness of its instantiations. *)
  Admitted.

End Instantiations.
