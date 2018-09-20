Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.ShapeSystem.
Require Import Typing.TypedClosure.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.

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
  := forall c_presup : presupposition (flat_rule_conclusion r),
      (FlatTypeTheory.derivation
         (FlatTypeTheory.fmap include_symbol T)
         (let H := flat_rule_premise r in H + Family.bind H presupposition)
         (presupposition _ c_presup)).

  (** Note: we could give (as we have for closure rules) a stronger notion of
  well-typedness, where we derive the presuppositions of premises as well
  as of the conclusion, and (in all these derivations) we assume just the
  premises as hypotheses, not also their presuppositions.
  *)

End WellTyped.

Section Instantiations.

  Context {σ : shape_system} {Σ : signature σ} `{Funext}.

  (** If a flat rule [r] is well-typed over a type theory [T],
      then each instantiation of [r] as a closure condition is well-typed
      over the associated closure system of [T]. *)
  Local Lemma closure_system_weakly_well_typed
       (T : flat_type_theory Σ)
       (r : flat_rule Σ) (D_r : weakly_well_typed T r)
       {Γ : raw_context Σ} (I : Metavariable.instantiation (flat_rule_metas r) Σ Γ)
    : TypedClosure.weakly_well_typed_rule presupposition
        (FlatTypeTheory.closure_system T)
        (FlatRule.closure_system r (Γ;I)).
  Proof.
    (* Rough idea: derivations translate along the instantiation of syntax,
    so the derivations provided by well-typedness of [r] translate into 
    the derivations required for well-typedness of its instantiations. *)
      unfold TypedClosure.weakly_well_typed_rule.
      intros p.
      eapply transport. 
      { apply instantiate_presupposition. }
      refine (Closure.graft _ _ _).
      + refine (FlatTypeTheory.instantiate_derivation _ _ _ _).
        apply D_r.
      + intros [ i | [ i i_presup]]. 
        * simple refine (Closure.hypothesis' _ _).
          -- exact (inl i).
          -- apply idpath.
        * simple refine (Closure.hypothesis' _ _).
          -- refine (inr (i;_)). exact i_presup.
          -- apply inverse, instantiate_presupposition.
  Defined.


End Instantiations.

