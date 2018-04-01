Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.Substitution.
Require Import Raw.FlatRule.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatTypeTheory.
Require Import Raw.RawTypeTheory.

(* TODO: probably this section should be broken out to a separate file. *)
Section TT_Maps.

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* TODO:
    possibly the [Signature.map] should be extracted as a parameter,
    à la displayed categories?
  *)
  Record TT_Map
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
  := { Signature_map_of_TT_Map :> Signature.map Σ Σ'
     ; rule_derivation_of_TT_Map
       : forall R : T, FlatTypeTheory.Derivation_Flat_Rule_from_Flat_Type_Theory
                         (FlatRule.fmap Signature_map_of_TT_Map (T R))
                         T'
     }.

  (* TODO: perhaps abstract [Family_Map_over] or something, i.e. a displayed-category version of family maps, for use in definitions like this? *)
  Local Definition Fmap_Structural_CCs
      {Σ Σ' : signature σ}
      (f : Signature.map Σ Σ')
    : Family.map
        (Family.fmap (Closure.fmap (Judgement.fmap_judgement_total f)) (structural_rule Σ))
        (structural_rule Σ').
  Proof.
    (* TODO: possible better approach:
       - [Fmap_Family] of families commutes with sums;
       - then use [repeat apply Fmap_Family_Sum.] or similar.  *)
    (* TODO: intermediate approach: at least allow family map to be constructed as a single function, to avoid duplicated destructing. *)
    apply Family.Build_map'.
    intros [ [ [ [ c1 | ] | [c2 | c3] ] | c4 ]  | c5 ].
    (* MANY cases here!  Really would be better with systematic way to say “in each case, apply [Fmap_Family] to the syntactic data”; perhaps something along the lines of the “judgement slots” approach? TODO: try a few by hand, then consider this. *)
    - (* context extension *)
      simple refine (_;_).
      + rename c1 into ΓA.
        refine (inl (inl (inl (Some _)))).
        exists (Context.fmap f ΓA.1).
        exact (Expression.fmap f ΓA.2).
      + cbn. apply Closure.rule_eq.
        * simple refine (Family.eq _ _). { apply idpath. }
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
             apply inverse. apply fmap_rename.
          -- intros x. cbn in x.
             eapply concat. { refine (plusone_comp_inj _ _ _ _ _ _ _). }
             eapply concat. Focus 2.
               { apply ap. refine (plusone_comp_inj _ _ _ _ _ _ _)^. } Unfocus.
             apply inverse. apply fmap_rename.
    - (* empty context *)
      exists (inl (inl (inl None))).
      cbn. apply Closure.rule_eq.
      * simple refine (Family.eq _ _). { apply idpath. }
        intros [].
      * cbn. apply (ap (fun x => (_; x))).
        apply (ap (Build_raw_context _)).
        apply path_forall. refine (empty_rect _ shape_is_empty _).
    - (* substitution *)
      destruct c2 as [ Γ [Γ' [g [hjf hjfi]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inl _)))).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + cbn. apply Closure.rule_eq; cbn.
        * apply inverse.
          eapply concat. { apply Family.map_adjoin. }
          apply ap011.
          -- unfold Family.fmap.
            apply ap, path_forall; intros i.
            apply (ap (fun x => (_; x))).
            apply (ap (fun x => (_; x))).
            apply path_forall. intros [ [ [] | ] | ].
            ++ refine (fmap_substitute _ _ _).
            ++ apply idpath.
          -- apply idpath.
          (* Family_fmap_adjoin *)
        * apply (ap (fun x => (_; x))). cbn.
          apply (ap (fun x => (_; x))).
          apply path_forall. intros i.
          unfold Judgement.fmap_hypothetical_judgement.
          refine (fmap_substitute _ _ _)^.
    - (* substitution equality *)
      destruct c3 as [ Γ [Γ' [g [g' [hjf hjfi]]]]].
      simple refine (_;_).
      + refine (inl (inl (inr (inr _)))).
        exists (Context.fmap f Γ).
        exists (Context.fmap f Γ').
        exists (fmap_raw_context_map f g).
        exists (fmap_raw_context_map f g').
        exists hjf.
        exact (Judgement.fmap_hypothetical_judgement f hjfi).
      + admit.
    - (* var rule *)
      simple refine (inl (inr _) ; _); admit.
    - (* equality rules *)
      simple refine (inr _; _); admit.
      (* Thest last two should be doable cleanly by the same lemmas
      used for logical rules in [fmap] below, once that’s done. *)
  Admitted.

  Local Definition fmap
    {Σ : signature σ} (T : flat_type_theory Σ)
    {Σ' : signature σ} (T' : flat_type_theory Σ')
    (f : TT_Map T T')
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
    (*   unfold Derivation_Flat_Rule_from_Flat_Type_Theory in fc. cbn in fc. *)
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
End TT_Maps.
