Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMap.
Require Import Raw.SubstitutionFacts.
Require Import Raw.StructuralRule.

Section Derivability_from_Flat_Type_Theory.

  Context {σ : shape_system}
          {Σ : signature σ}.

  Definition CCs_of_Flat_Type_Theory (T : flat_type_theory Σ)
    : Closure.system (judgement_total Σ)
    := Structural_CCs Σ + Family.bind T FlatRule.closure_system.

  Definition Derivation_from_Flat_Type_Theory (T : flat_type_theory Σ) H
    : judgement_total Σ -> Type
    := Closure.derivation (CCs_of_Flat_Type_Theory T) H.

End Derivability_from_Flat_Type_Theory.

Section Derivable_Rules.
  (* “Derivable rules” over a type theory;
  or, to be precise, _derivations_ of raw rules over a raw type theory. *)

  Context {σ : shape_system}
          {Σ : signature σ}.

  Definition Derivation_Raw_Rule_from_Flat_Type_Theory
      (R : flat_rule Σ) (T : flat_type_theory Σ)
    : Type.
  Proof.
    refine (Closure.derivation _ (flat_rule_premises _ R) (flat_rule_conclusion _ R)).
    apply CCs_of_Flat_Type_Theory.
    refine (fmap_flat_type_theory _ T).
    apply Family.map_inl. (* TODO: make this a lemma about signature maps,
                            so it’s more findable using “SearchAbout” etc *)
  Defined.

End Derivable_Rules.

Section TT_Maps.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* TODO:
    possibly the [Signature_Map] should be extracted as a parameter,
    à la displayed categories?
  *)
  Record TT_Map
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
  := { Signature_Map_of_TT_Map :> Signature_Map Σ Σ'
     ; rule_derivation_of_TT_Map
       : forall R : T, Derivation_Raw_Rule_from_Flat_Type_Theory
                         (Fmap_Raw_Rule Signature_Map_of_TT_Map (T R))
                         T'
     }.

  (* TODO: upstream! and consider naming conventions for such lemmas. *)
  Definition closure_condition_eq {X} {c c' : Closure.rule X}
    : Closure.rule_premises c = Closure.rule_premises c'
    -> Closure.rule_conclusion c = Closure.rule_conclusion c'
    -> c = c'.
  Proof.
    destruct c, c'; cbn.
    intros e e'; destruct e, e'.
    apply idpath.
  Defined.

  (* TODO: upstream! and consider naming conventions for such lemmas. *)
  Definition Family_eq `{Funext} {X} {c c' : family X}
    (e : family_index c = family_index c')
    (e' : forall i:c, c i = c' (equiv_path _ _ e i) )
    : c = c'.
  Proof.
    destruct c, c'; cbn in *.
    destruct e. apply ap.
    apply path_forall; intros i; apply e'.
  Defined.

  (* TODO: upstream! *)
  Definition Build_Family_Map' {A} (K L : family A)
      (f : forall i:K, { j:L & L j = K i })
    : Family.map K L.
  Proof.
    exists (fun i => pr1 (f i)).
    intros i. exact (pr2 (f i)).
  Defined.

  (* TODO: upstream! *)
  Definition Fmap_Raw_Context_Map
      {Σ Σ' : signature σ} (f : Signature_Map Σ Σ')
      {γ γ'} (g : Context.map Σ γ' γ)
    : Context.map Σ' γ' γ
  := fun i => (Fmap_Raw_Syntax f (g i)).

  (* TODO: upstream! *)
  Lemma Fmap_Raw_Syntax_Raw_Subst
      {Σ Σ' : signature σ}
      (f : Signature_Map Σ Σ')
      {γ γ'} (g : Context.map Σ γ' γ)
      {cl} (e : raw_expression Σ cl γ)
    : Fmap_Raw_Syntax f (substitute g e)
    = substitute (Fmap_Raw_Context_Map f g) (Fmap_Raw_Syntax f e).
  Proof.
  Admitted.

  (* *)
  Lemma Fmap_Family_Snoc
      {X Y} (f : X -> Y)
      (K : family X) (x : X)
    : Family.fmap f (Family.adjoin K x) = Family.adjoin (Family.fmap f K) (f x).
  Proof.
    simple refine (Family_eq _ _).
    - apply idpath.
    - intros [? | ]; apply idpath.
  Defined.

  (* TODO: abstract [Family_Map_over] or something, i.e. a displayed-category version of family maps, for use in definitions like this? *)
  Definition Fmap_Structural_CCs
      {Σ Σ' : signature σ}
      (f : Signature_Map Σ Σ')
    : Family.map
        (Family.fmap (Closure.fmap (Fmap_Judgt_Instance f)) (Structural_CCs Σ))
        (Structural_CCs Σ').
  Proof.
    (* TODO: possible better approach:
       - [Fmap_Family] of families commutes with sums;
       - then use [repeat apply Fmap_Family_Sum.] or similar.  *)
    (* TODO: intermediate approach: at least allow family map to be constructed as a single function, to avoid duplicated destructing. *)
    apply Build_Family_Map'.
    intros [ [ [ [ c1 | ] | [c2 | c3] ] | c4 ]  | c5 ].
    (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap_Family] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: try a few by hand, then consider this. *)
    - (* context extension *)
      simple refine (_;_).
      + rename c1 into ΓA.
        refine (inl (inl (inl (Some _)))).
        exists (Fmap_Raw_Context f ΓA.1).
        exact (Fmap_Raw_Syntax f ΓA.2).
      + cbn. apply closure_condition_eq.
        * simple refine (Family_eq _ _). { apply idpath. }
          cbn. intros [ [ [] | ] | ].
          -- apply idpath.
          -- apply (ap (fun x => (_; x))).
             apply (ap (fun x => (_; x))).
             apply path_forall. intros [ [] | ];
             apply idpath.
        * cbn. apply (ap (fun x => (_; x))).
          apply (ap (Build_raw_context _)).
          apply path_forall.
          refine (plusone_rect _ _ (shape_is_extend _ _) _ _ _).
          -- eapply concat. { refine (plusone_comp_one _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_one _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Fmap_Raw_Weaken.
          -- intros x. cbn in x.
             eapply concat. { refine (plusone_comp_inj _ _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_inj _ _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply Fmap_Raw_Weaken.
    - (* empty context *)
      exists (inl (inl (inl None))).
      cbn. apply closure_condition_eq.
      * simple refine (Family_eq _ _). { apply idpath. }
        intros [].
      * cbn. apply (ap (fun x => (_; x))).
        apply (ap (Build_raw_context _)).
        apply path_forall. refine (empty_rect _ shape_is_empty _).
    - (* substitution *)
      destruct c2 as [ Γ [Γ' [g [hjf hjfi]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inl _)))).
        exists (Fmap_Raw_Context f Γ).
        exists (Fmap_Raw_Context f Γ').
        exists (Fmap_Raw_Context_Map f g).
        exists hjf.
        exact (Fmap_Hyp_Judgt_Form_Instance f hjfi).
      + cbn. apply closure_condition_eq; cbn.
        * apply inverse.
          eapply concat. { apply Fmap_Family_Snoc. }
          apply ap011.
          -- unfold Family.fmap.
            apply ap, path_forall; intros i.
            apply (ap (fun x => (_; x))).
            apply (ap (fun x => (_; x))).
            apply path_forall. intros [ [ [] | ] | ].
            ++ refine (Fmap_Raw_Syntax_Raw_Subst _ _ _).
            ++ apply idpath.
          -- apply idpath.
          (* Family_fmap_adjoin *)
        * apply (ap (fun x => (_; x))). cbn.
          apply (ap (fun x => (_; x))).
          apply path_forall. intros i.
          unfold Fmap_Hyp_Judgt_Form_Instance.
          refine (Fmap_Raw_Syntax_Raw_Subst _ _ _)^.
    - (* substitution equality *)
      destruct c3 as [ Γ [Γ' [g [g' [hjf hjfi]]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inr _)))).
        exists (Fmap_Raw_Context f Γ).
        exists (Fmap_Raw_Context f Γ').
        exists (Fmap_Raw_Context_Map f g).
        exists (Fmap_Raw_Context_Map f g').
        exists hjf.
        exact (Fmap_Hyp_Judgt_Form_Instance f hjfi).
      + admit.
    - (* var rule *)
      simple refine (inl (inr _) ; _); admit.
    - (* equality rules *)
      simple refine (inr _; _); admit.
      (* Thest last two should be doable cleanly by the same lemmas
      used for logical rules in [Fmap_CCs_of_Flat_Type_Theory] below, once that’s done. *)
  Admitted.

  (* TODO: upstream *)
  (* closure_system maps are really a sort of Kelisli map, and this is essentially just the unit.  TODO: abstract this out more clearly! *)
  (* Definition closure_system_map_of_Family_map *)
  (*     {X} {C D : Closure.system X} (f : Family.map C D) *)
  (*   : Closure.map C D. *)
  (* Proof. *)
  (*   intro i. eapply paths_rew. *)
  (*   - exact (Simple_Derivation_of_CC (f c)). *)
  (*   - apply Family.map_commutes. *)
  (* Defined. *)

  Definition Fmap_CCs_of_Flat_Type_Theory
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
    (f : TT_Map T T')
  : Closure.map
      (Family.fmap (Closure.fmap (Fmap_Judgt_Instance f)) (CCs_of_Flat_Type_Theory T))
      (CCs_of_Flat_Type_Theory T').
  Proof.
    intros c. (* We need to unfold [c] a bit here, bit not too much. *)
    unfold Family.fmap, family_index, CCs_of_Flat_Type_Theory in c.
    destruct c as [ c_str | c_from_rr ].
    - (* Structural rules *)
      (* an instance of a structural rule is translated to an instance of the same structural rule *)
      admit. (* temporarily giving up on this, it seems unfinished anyhow. *)
      (* eapply paths_rew. *)
      (* + refine (Simple_Derivation_of_CC _). *)
      (*   refine (Family.map_inl _). *)
      (*   exact (Fmap_Structural_CCs f c_str). *)
      (* + eapply concat. { apply Family.map_commutes. } *)
      (*   refine (Family.map_commutes _ _).  *)
    (* - (* Logical rules *) *)
    (*   cbn in c_from_rr. rename c_from_rr into c. *)
    (*   destruct c as [i [Γ A]]. *)
    (*   unfold Derivation_of_CC; cbn. *)
    (*   set (fc := rule_derivation_of_TT_Map _ _ f i). (* TODO: implicits! *) *)
    (*   set (c := T i) in *. *)
    (*   set (a := flat_rule_metas Σ c) in *. *)
    (*   unfold Derivation_Raw_Rule_from_Flat_Type_Theory in fc. cbn in fc. *)
    (*   transparent assert (f_a : (Signature_Map *)
    (*         (Metavariable.extend Σ a) (Metavariable.extend Σ' a))). *)
    (*     apply Fmap1_Metavariable_Extension, f. *)
      (*
      Very concretely: fc is over Σ+a.  Must map to Σ'+a, then instantiate.

      *)
      (* OK, this can be all abstracted a bit better:
       - “derivable cc’s” gives a “monad” on closure systems; so “deduce-bind” or something, like “deduce” but with a derivable cc instead of an atomic one
       - any instantiation of a derivable raw rule gives a derivable closure condition over CCs_of_TT.
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
End TT_Maps.
