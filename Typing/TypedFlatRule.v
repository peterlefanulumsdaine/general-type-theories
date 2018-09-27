Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.
Require Import Typing.UtilityDerivations.

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

Section SignatureMaps.

  Context {σ : shape_system} `{Funext}.

  Local Definition fmap_weakly_well_typed
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T} {T'} (ff : FlatTypeTheory.map_over f T T')
      (r : flat_rule Σ) (r_wt : weakly_well_typed T r)
    : weakly_well_typed T' (FlatRule.fmap f r).
  Proof.
    intros p.
    refine (transport _ _ _).
    - apply Judgement.fmap_presupposition.
    - simple refine (Closure.derivation_fmap2 _
        (FlatTypeTheory.derivation_fmap1_over _ (r_wt p))).
      + cbn.
        (* TODO: rewrite [Family.fmap_sum] as an iso, for better behaviour? *)
        refine (transport (fun K => Family.map K _) _ _).
        { apply inverse, Family.fmap_sum. }
        apply (Family.sum_fmap (Family.idmap _)).
        refine (Family.compose _ (Family.fmap_bind _ _ _)).
        refine (Family.compose (Family.bind_fmap_mid _ _ _) _).
        apply Family.bind_fmap2. intros a.
        apply Judgement.fmap_presupposition_family.
      + (* TODO: the following could possibly be better abstracted in terms of the fibrational properties of flat type theory maps? *)
        intros R.
        refine (transport _ _
          (FlatTypeTheory.flat_rule_derivation_fmap _ (ff R))).
        refine (_ @ FlatRule.fmap_compose _ _ _).
        refine ((FlatRule.fmap_compose _ _ _)^ @ _).
        apply ap10, ap. apply Metavariable.include_symbol_after_map.
  Defined.

End SignatureMaps.

Section Instantiations.

  Context {σ : shape_system} {Σ : signature σ} `{Funext}.

  (** If a flat rule [r] is well-typed over a type theory [T],
      then each instantiation of [r] as a closure condition is well-typed
      over the associated closure system of [T]. *)
  Local Lemma closure_system_weakly_well_typed
       (T : flat_type_theory Σ)
       (r : flat_rule Σ) (D_r : weakly_well_typed T r)
       {Γ : raw_context Σ} (I : Metavariable.instantiation (flat_rule_metas r) Σ Γ)
    : Closure.weakly_well_typed_rule presupposition
        (FlatTypeTheory.closure_system T)
        (FlatRule.closure_system r (Γ;I)).
  Proof.
    (* Rough idea: derivations translate along the instantiation of syntax,
    so the derivations provided by well-typedness of [r] translate into 
    the derivations required for well-typedness of its instantiations. *)
      unfold Closure.weakly_well_typed_rule.
      intros p.
      eapply transport. 
      { apply instantiate_presupposition. }
      refine (Closure.graft _ _ _).
      + refine (FlatTypeTheory.instantiate_derivation _ _ _ _).
        apply D_r.
      + intros [[ i | [ i i_presup]] | []]. 
        * simple refine (Closure.hypothesis' _ _).
          -- exact (inl (inr i)).
          -- apply idpath.
        * simple refine (Closure.hypothesis' _ _).
          -- refine (inr ((inr i);_)). exact i_presup.
          -- apply inverse. refine (instantiate_presupposition _ _ _).
        * simple refine (Closure.hypothesis' _ _).
          -- apply inl, inl, tt.
          -- apply idpath.
  Defined.

End Instantiations.

