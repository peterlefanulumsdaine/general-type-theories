Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystems.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.DeductiveClosure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMaps.
Require Import Raw.Substitution.
Require Import Raw.StructuralRules.

Section Derivability_from_Raw_TT.

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  Definition CCs_of_Raw_TT (T : Raw_Type_Theory Σ)
    : Family (closure_condition (Judgt_Instance Σ))
  := Structural_CCs Σ
     + Family.Bind T CCs_of_RR.

  Definition Derivation_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Judgt_Instance Σ -> Type
  := Derivation (CCs_of_Raw_TT T).
  
End Derivability_from_Raw_TT.

Section Derivable_Rules.
  (* “Derivable rules” over a type theory;
  or, to be precise, _derivations_ of raw rules over a raw type theory. *)

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  Definition Derivation_Raw_Rule_from_Raw_TT
      (R : Raw_Rule Σ) (T : Raw_Type_Theory Σ)
    : Type.
  Proof.
    refine (Derivation_from_premises _ (RR_prem _ R) (RR_concln _ R)).
    apply CCs_of_Raw_TT.
    refine (Fmap_Raw_TT _ T).
    apply inl_Family. (* TODO: make this a lemma about signature maps,
                         so it’s more findable using “SearchAbout” etc *)
  Defined.

End Derivable_Rules.

Section TT_Maps.

  Context `{H : Funext}.
  Context {σ : Shape_System}.

  (* TODO:
    possibly the [Signature_Map] should be extracted as a parameter,
    à la displayed categories?
  *)
  Record TT_Map
    {Σ : Signature σ} (T : Raw_Type_Theory Σ)
    {Σ' : Signature σ} (T' : Raw_Type_Theory Σ')
  := { Signature_Map_of_TT_Map :> Signature_Map Σ Σ'
     ; rule_derivation_of_TT_Map
       : forall R : T, Derivation_Raw_Rule_from_Raw_TT
                         (Fmap_Raw_Rule Signature_Map_of_TT_Map (T R))
                         T'
     }.

  (** An alternative to [deduce], for use in interactive proofs.  [apply deduce] rarely works, since until the rule to be used is fully specified, the conclusion will not typically unify with the “current goal” (and even then, it may not unify judgementally). *)
  (* TODO: consider if there might be better ways to handle this issue? *)
  Definition deduce' {X : Type} {C : Family (closure_condition X)}
      (c : C) (f : forall p : cc_premises (C c),
                  Derivation C ((cc_premises (C c)) p))
      {x : X} (p : cc_conclusion (C c) = x)
  : Derivation C x.
  Proof.
    exact (transport _ p (deduce _ c f)).
  Defined.
  
  Definition Fmap_CCs_of_Raw_TT
    {Σ : Signature σ} (T : Raw_Type_Theory Σ)
    {Σ' : Signature σ} (T' : Raw_Type_Theory Σ')
    (f : TT_Map T T')
  : CC_system_map
      (Fmap (Fmap_cc (Fmap_Judgt_Instance f)) (CCs_of_Raw_TT T))
      (CCs_of_Raw_TT T').
  Proof.
    intros c. (* We need to unfold [c] a bit here, bit not too much. *)
    unfold Fmap, fam_index, CCs_of_Raw_TT in c.
    destruct c as [ c_str | c_from_rr ].
    - (* Structural rules *)
      (* an instance of a structural rule is translated to an instance of the same structural rule *)
      unfold Derivation_of_CC, Derivation_from_premises.      
      cbn in c_str.
      (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: consider this. *)
      destruct c_str as [ [ [ [ ΓA | ] | [c2 | c3] ] | c4 ]  | c5 ].
      + (* context extension *)
        simple refine (deduce' _ _ _).
        * (* pick which rule to use, and which instantiation *)
          refine (inl (inl _)). (* use a structural rule *)
          refine (inl (inl (inl (Some _)))). (* pick “context extension” *)
          exists (Fmap_Raw_Context f ΓA.1).
          exact (Fmap_Raw_Syntax f ΓA.2).
        * (* derive the premises *)
          cbn. intros p.
          simple refine (deduce' _ _ _). 
          -- exact (inr p).
          -- destruct p as [ [ [] | ] | ]; intros [].
          -- destruct p as [ [ [] | ] | ].
             ++ apply idpath.
             ++ apply (ap (fun x => (_; x))).
                apply (ap (fun x => (_; x))).
                apply path_forall. intros [ [] | ];
                apply idpath.
        * (* show the conlusion is correct *)
          cbn. apply (ap (fun x => (_; x))).
          apply (ap (Build_Raw_Context _)).
          apply path_forall.
          refine (plusone_rect _ _ (shape_is_plusone _ _) _ _ _).
          -- eapply concat. { refine (plusone_comp_one _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_one _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Fmap_Raw_Weaken. 
          -- intros x. cbn in x.
             eapply concat. { refine (plusone_comp_inj _ _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_inj _ _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Fmap_Raw_Weaken. 
      + (* empty context *)
        simple refine (deduce' _ _ _).
        * refine (inl (inl _)). (* use a structural rule *)
          refine (inl (inl (inl None))). (* pick “empty context” *)
        * cbn. intros [].
        * cbn. apply (ap (fun x => (_; x))).
          apply (ap (Build_Raw_Context _)).
          apply path_forall. refine (empty_rect _ shape_is_empty _).
      + admit.
      + admit.
      + admit.
      + admit.
    - (* Logical rules *)
      admit.
  Admitted.

  (* TODO: the above shows that we need some serious extra tools for building derivations, in several ways:
  - access functions for picking out structural rules (and recursing over)
  - lemma/tactic for showing judgment instances are equal if all their syntactic parts are equal.
    (only the proto-contexts can generally be expected to be judgementally equal)
  - lemma/tactic for showing raw contexts are equal if all their types are equal
  *)

  (* TODO: maps of type theories preserve derivability. *)
End TT_Maps.
