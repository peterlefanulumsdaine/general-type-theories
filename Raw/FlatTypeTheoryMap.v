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

(* TODO: probably this section should be broken out to a separate file. *)
Section FlatTypeTheoryMap.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* TODO:
    possibly the [Signature.map] should be extracted as a parameter,
    à la displayed categories?
  *)
  Record flat_type_theory_map
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
  := { fttm_signature_map :> Signature.map Σ Σ'
     ; fttm_rule_derivation
       : forall R : T, FlatTypeTheory.flat_rule_derivation
                         (FlatRule.fmap fttm_signature_map (T R))
                         T'
     }.

  Local Definition fmap
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
    (f : flat_type_theory_map T T')
  : Closure.map
      (Family.fmap (Closure.fmap (Judgement.fmap_judgement_total f)) (FlatTypeTheory.closure_system T))
      (FlatTypeTheory.closure_system T').
  Proof.
    intros c. (* We need to unfold [c] a bit here, bit not too much. *)
    unfold Family.fmap, family_index, FlatTypeTheory.closure_system in c.
    destruct c as [ c_str | c_from_rr ].
    - (* Structural rules *)
      (* an instance of a structural rule is translated to an instance of the same structural rule *)
      admit. (* temporarily giving up on this, it seems unfinished anyhow. *)
      (* eapply paths_rew. *)
      (* + refine (Simple_Derivation_of_CC _). *)
      (*   refine (Family.inl _). *)
      (*   exact (Fmap_Structural_CCs f c_str). *)
      (* + eapply concat. { apply Family.map_commutes. } *)
      (*   refine (Family.map_commutes _ _).  *)
    (* - (* Logical rules *) *)
    (*   cbn in c_from_rr. rename c_from_rr into c. *)
    (*   destruct c as [i [Γ A]]. *)
    (*   unfold Derivation_of_CC; cbn. *)
    (*   set (fc := fttm_rule_derivation _ _ f i). (* TODO: implicits! *) *)
    (*   set (c := T i) in *. *)
    (*   set (a := flat_rule_metas Σ c) in *. *)
    (*   unfold flat_rule_derivation in fc. cbn in fc. *)
    (*   transparent assert (f_a : (Signature.map *)
    (*         (Metavariable.extend Σ a) (Metavariable.extend Σ' a))). *)
    (*     apply Metavariable.fmap1, f. *)
      (*
      Very concretely: fc is over Σ+a.  Must map to Σ'+a, then instantiate.

      *)
      (* OK, this can be all abstracted a bit better:
       - “derivable cc’s” gives a “monad” on closure systems; so “deduce-bind” or something, like “deduce” but with a derivable cc instead of an atomic one
       - any instantiation of a derivable flat rule gives a derivable closure condition over CCs_of_TT.
       - fmap on derivable closure conditions
       - fmap on *)
  Admitted.

  (* TODO: the above shows that we need some serious extra tools for building derivations, in several ways:
  - access functions for picking out structural rules (and recursing over)
  - lemma/tactic for showing judgment instances are equal if all their syntactic parts are equal.
    (only the proto-contexts can generally be expected to be judgementally equal)
  - lemma/tactic for showing raw contexts are equal if all their types are equal
  *)

  (* TODO: maps of type theories preserve derivability. *)
End FlatTypeTheoryMap.
