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
  
  Definition Fmap_Derivation_from_premises {X Y} (f : X -> Y)
      {C : Family (closure_condition X)} {P : Family X} {x}
      (D : Derivation_from_premises C P x)
    : Derivation_from_premises (Fmap_Family (Fmap_cc f) C) (Fmap_Family f P) (f x). 
  Proof.
    (* TODO: give better lemma on gluing derivations-with-premises:
     given a derivation of (f x) with premises Γ, and derivations of all of Γ from Δ, then get defivation of (f x) from Δ.  Or in this case, an alternative would be just: show Γ = Δ. *)
  Admitted.

  (* TODO: upstream! and consider naming conventions for such lemmas. *)
  Definition closure_condition_eq {X} {c c' : closure_condition X}
    : cc_premises c = cc_premises c'
    -> cc_conclusion c = cc_conclusion c'
    -> c = c'.
  Proof.
    destruct c, c'; cbn.
    intros e e'; destruct e, e'.
    apply idpath.
  Defined.

  (* TODO: upstream! and consider naming conventions for such lemmas. *)
  Definition Family_eq `{Funext} {X} {c c' : Family X}
    (e : fam_index c = fam_index c')
    (e' : forall i:c, c i = c' (equiv_path _ _ e i) )
    : c = c'.
  Proof.
    destruct c, c'; cbn in *.
    destruct e. apply ap.
    apply path_forall; intros i; apply e'.
  Defined.

  (* TODO: abstract [Family_Map_over] or something, i.e. a displayed-category version of family maps, for use in definitions like this? *)
  Definition Fmap_Structural_CCs
      {Σ Σ' : Signature σ}
      (f : Signature_Map Σ Σ')
    : Family_Map (Fmap_Family (Fmap_cc (Fmap_Judgt_Instance f)) (Structural_CCs Σ))
                 (Structural_CCs Σ'). 
  Proof.
    (* TODO: possible better approach:
       - [Fmap_Family] of families commutes with sums;
       - then use [repeat apply Fmap_Family_Sum.] or similar.  *)
    (* TODO: intermediate approach: at least allow family map to be constructed as a single function, to avoid duplicated destructing. *)
    simple refine (_;_).
    - intros [ [ [ [ c1 | ] | [c2 | c3] ] | c4 ]  | c5 ].
      (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap_Family] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: try a few by hand, then consider this. *)
      + (* context extension *)
        rename c1 into ΓA.
        refine (inl (inl (inl (Some _)))).
        exists (Fmap_Raw_Context f ΓA.1).
        exact (Fmap_Raw_Syntax f ΓA.2).
      + (* empty context *) 
        refine (inl (inl (inl None))).
      + admit.        
      + admit.        
      + admit.        
      + admit.        
    - intros [ [ [ [ c1 | ] | [c2 | c3] ] | c4 ]  | c5 ].
      + (* context extension *)
        cbn. apply closure_condition_eq. 
        * simple refine (Family_eq _ _). { apply idpath. }
          cbn. intros [ [ [] | ] | ].
          -- apply idpath.
          -- apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros [ [] | ];
             apply idpath.
        * cbn. apply (ap (fun x => (_; x))).
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
        cbn. apply closure_condition_eq.
        * simple refine (Family_eq _ _). { apply idpath. }
          intros [].
        * cbn. apply (ap (fun x => (_; x))).
          apply (ap (Build_Raw_Context _)).
          apply path_forall. refine (empty_rect _ shape_is_empty _).
      + admit.        
      + admit.        
      + admit.        
      + admit.        
  Admitted.

  (* TODO: upstream *)
  (* TODO: consider name! *)
  Definition Simple_Derivation_of_CC
      {X} {C : Family (closure_condition X)} (i : C)
    : Derivation_of_CC C (C i).
  Proof.
    refine (deduce (_+_) (inl i) _). intros p.
    simple refine (deduce' _ _ _). 
    - exact (inr p).
    - intros [].
    - apply idpath.
  Defined.

  (* TODO: upstream *)
  (* closure_system maps are really a sort of Kelisli map, and this is essentially just the unit.  TODO: abstract this out more clearly! *)
  Definition closure_system_map_of_Family_map
      {X} {C C' : Family (closure_condition X)} (f : Family_Map C C')
    : closure_system_map C C'.
  Proof.
    intros c. eapply paths_rew.
    - exact (Simple_Derivation_of_CC (f c)).
    - apply commutes_Family_Map.
  Defined.

  Definition Fmap_CCs_of_Raw_TT
    {Σ : Signature σ} (T : Raw_Type_Theory Σ)
    {Σ' : Signature σ} (T' : Raw_Type_Theory Σ')
    (f : TT_Map T T')
  : closure_system_map
      (Fmap_Family (Fmap_cc (Fmap_Judgt_Instance f)) (CCs_of_Raw_TT T))
      (CCs_of_Raw_TT T').
  Proof.
    intros c. (* We need to unfold [c] a bit here, bit not too much. *)
    unfold Fmap_Family, fam_index, CCs_of_Raw_TT in c.
    destruct c as [ c_str | c_from_rr ].
    - (* Structural rules *)
      (* an instance of a structural rule is translated to an instance of the same structural rule *)
      eapply paths_rew.
      + refine (Simple_Derivation_of_CC _).
        refine (inl_Family _).
        exact (Fmap_Structural_CCs f c_str).
      + eapply concat. { apply commutes_Family_Map. }
        refine (commutes_Family_Map _ _). 
    - (* Logical rules *)
      cbn in c_from_rr. rename c_from_rr into c.
      destruct c as [i [Γ A]].
      unfold Derivation_of_CC; cbn.
      set (fc := rule_derivation_of_TT_Map _ _ f i). (* TODO: implicits! *)
      set (c := T i) in *.
      set (a := RR_metas Σ c) in *.
      unfold Derivation_Raw_Rule_from_Raw_TT in fc. cbn in fc.
      transparent assert (f_a : (Signature_Map
            (Metavariable_Extension Σ a) (Metavariable_Extension Σ' a))).
        apply Fmap1_Metavariable_Extension, f.
      (*
      Very concretely: fc is over Σ+a.  Must map to Σ'+a, then instantiate.
      
      *)
      (* OK, this can be all abstracted a bit better:
       - “derivable cc’s” gives a “monad” on closure systems; so “deduce-bind” or something, like “deduce” but with a derivable cc instead of an atomic one 
       - any instantiation of a derivable raw rule gives a derivable closure condition over CCs_of_TT.
       - fmap on derivable closure conditions
       - fmap on *) 
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
