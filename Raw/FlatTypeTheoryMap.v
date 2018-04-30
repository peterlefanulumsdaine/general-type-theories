Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.RawSubstitution.
Require Import Raw.FlatRule.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatTypeTheory.
Require Import Raw.RawTypeTheory.

Section FlatTypeTheoryMap.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* A flat type theory map [ff : T -> T'] over a map [f : Σ -> Σ'] of their signatures consists of derivations exhibiting the translation of each rule of [T] as a derivable rule of [T']. *)
  Definition flat_type_theory_map_over
    {Σ Σ': signature σ} (f : Signature.map Σ Σ')
    (T : flat_type_theory Σ) (T' : flat_type_theory Σ')
  := forall R : T,
      FlatTypeTheory.flat_rule_derivation T' (FlatRule.fmap f (T R)).

  (* TODO: upstream to [Auxiliary.Closure] *)
  Lemma one_step_derivation {X} {T : Closure.system X} (r : T)
    : Closure.derivation T
              (Closure.premises (T r)) (Closure.conclusion (T r)).
  Proof.
    refine (deduce T _ r _).
    intros i. exact (hypothesis T _ i).
  Defined.

  Definition fmap_closure_system
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
    (ff : flat_type_theory_map_over f T T')
  : Closure.map_over (fmap_judgement_total f)
      (FlatTypeTheory.closure_system T)
      (FlatTypeTheory.closure_system T').
  Proof.
    apply Closure.fmap_sum.
    { (* structural rules *)
      apply Closure.map_from_family_map.
      apply RawStructuralRule.fmap.
    }
    (* Logical rules *)
    intros [r [Γ I]].
    cbn.
    set (D := ff r).
    admit.
    (* some lemmas we want here:
    - can map an instantiation of variables under map of signatures
    - from [FlatTypeTheory.flat_rule_derivation], can get a [Closure.derivation] of any instantiation of the rule (using [instantiate_derivation]);
    - …?

    set (D_inst := FlatTypeTheory.instantiate_derivation T' I _ D). 
    unfold FlatTypeTheory.flat_rule_derivation in D.
    cbn in D.
    *)
  Admitted.

  (* TODO: maps of type theories preserve derivability. *)
End FlatTypeTheoryMap.
