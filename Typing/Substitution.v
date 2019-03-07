Require Import HoTT.
Require Export Syntax.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.StructuralRule.
Require Import Typing.FlatTypeTheory.

(** We show in this file that “substitution is admissible”: that is, that if [f] is a context morphism from [Γ'] to [Γ], then whenever one can derive a judgement [ Γ |- J ], one can also derive [ Γ' |- f^* J ].  *)

Section Renaming_Admissible.

(** As usual, we prepare for a result about substitution by giving an anlogous result for renaming. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** A renaming function between raw contexts, respecting the given types
  up to literal syntactic equality. *)
  Record typed_renaming (Γ Γ' : raw_context Σ)
  := { map_of_typed_renaming :> Γ -> Γ'
     ; typed_renaming_commutes :
       forall i, Γ' (map_of_typed_renaming i)
                 = rename (map_of_typed_renaming) (Γ i) }. 

  (** “Typed renaming” preserves derivability of hypothetical judgements *)
  Definition derivation_rename {T}
    (J : judgement Σ)
    {Γ'} (f : typed_renaming (context_of_judgement J) Γ')
  : Closure.derivation (structural_rule Σ + T) [<>] J
  -> Closure.derivation (structural_rule Σ + T) [<>]
                        (Build_judgement Γ' (rename_hypothetical_judgement f J)).
  Proof.
    intros d.
    induction d as [ [] | [r_struc | r_log ] d_hyps IH_hyps ].
    (* no hypotheses to cover *)
    - (* structural rules *)
      revert r_struc f d_hyps IH_hyps.
      refine (structural_rule_rect _ _ _ _).
      + (* renaming rules *)
        admit.
      + (* variable rule *)
        intros [Γ i]; cbn. intros.
      + (* equality rules *)
    - (* logical rules *)
  Defined.

End Renaming_Admissible.
