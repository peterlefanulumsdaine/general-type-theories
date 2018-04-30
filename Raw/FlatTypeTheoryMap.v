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
    (* TODO: unnecessarily complicated!
       Should start with [apply Closure.map_from_family_map.] *)
    intros r. (* We need to unfold [r] a bit here, bit not too much. *)
    unfold Family.fmap, family_index, FlatTypeTheory.closure_system in r.
    destruct r as [ r_str | r_from_rr ].
    - (* Structural rules *)
      (* an instance of a structural rule is translated to an instance of the same structural rule *)
      set (f_r := RawStructuralRule.fmap f r_str).
      set (e_f_r := Family.map_over_commutes
                      (RawStructuralRule.fmap f) r_str).
      set (e_prems := ap (@Closure.premises _) e_f_r).
      set (e_concl := ap (@Closure.conclusion _) e_f_r).
      refine (transport _ e_concl _).
      refine (transport (fun H => derivation _ H _) e_prems _).
      refine (Closure.fmap_derivation _ (one_step_derivation f_r)).
      apply Closure.map_from_family_map.
      apply Family.inl.
     - (* Logical rules *)
       cbn in r_from_rr. rename r_from_rr into r.
       destruct r as [i [Γ A]].
       cbn.
       set (fc := ff i).
       set (c := T i) in *.
       set (a := flat_rule_metas Σ c) in *.
       unfold FlatTypeTheory.flat_rule_derivation in fc. cbn in fc.
       transparent assert (f_a : (Signature.map
             (Metavariable.extend Σ a) (Metavariable.extend Σ' a))).
       { apply Metavariable.fmap1, f. }
      (*
      Very concretely: fc is over Σ+a.  Must map to Σ'+a, then instantiate.

      *)
      (* OK, this can be all abstracted a bit better:
       - “derivable cc’s” gives a “monad” on closure systems; so “deduce-bind” or something, like “deduce” but with a derivable cc instead of an atomic one
       - any instantiation of a derivable flat rule gives a derivable closure condition over CCs_of_TT.
       - fmap on derivable closure conditions
       - fmap on ?? *)
  Admitted.

  (* TODO: maps of type theories preserve derivability. *)
End FlatTypeTheoryMap.
