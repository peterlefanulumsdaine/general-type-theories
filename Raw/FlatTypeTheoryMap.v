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

  (* TODO: upstream to [Family]. *)
  Lemma family_fmap_comp {X Y Z} (f : X -> Y) (g : Y -> Z) (K : family X)
    : Family.fmap (g o f) K = Family.fmap g (Family.fmap f K).
  Proof.
    apply idpath.
  Defined.

  (* TODO: upstream to [Closure] (and add analogue in [Family]?) *)
  Lemma closure_sum_rect {X} {Y} {f : X -> Y}
      {K1 K2 : Closure.system X} {L : Closure.system Y}
      (ff1 : Closure.map_over f K1 L) (ff2 : Closure.map_over f K2 L)
    : Closure.map_over f (K1 + K2) L.
  Proof.
    intros [ x | x ]; [apply ff1 | apply ff2].
  Defined.

  Definition fmap_closure_system
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
    (ff : flat_type_theory_map_over f T T')
  : Closure.map_over (fmap_judgement_total f)
      (FlatTypeTheory.closure_system T)
      (FlatTypeTheory.closure_system T').
  Proof.
    apply closure_sum_rect.
    { (* structural rules *)
      apply Closure.map_from_family_map.
      refine (Family.compose_over (Family.inl) _).
      apply RawStructuralRule.fmap.
    }
    (* Logical rules *)
    intros [r [Γ I]]. cbn.
    (* From here, want to get goal into a form where it can be obtained
     by [instantiate_derivation]. *)
    eapply transport. { apply inverse, fmap_instantiate_judgement. }
    eapply (transport (fun H => derivation _ H _)).
    { apply inverse.
      eapply concat. { apply inverse, family_fmap_comp. }
      eapply concat.
      { refine (ap10 _ _). apply ap, path_forall; intros i.
        apply fmap_instantiate_judgement. }
      apply family_fmap_comp.
    }
    apply instantiate_derivation.
    apply ff.
  Defined.

  (* TODO: maps of type theories preserve derivability. *)
End FlatTypeTheoryMap.
