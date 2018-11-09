Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.
Require Import Typing.StructuralRule.
Require Import Typing.UtilityDerivations.
Require Import Typing.TypedFlatRule.

(** We show that all the structural rules are well-typed.

   In general this means only _weak_ well-typedness: for each rule, we derive
   the presuppositions of its conclusion, from its premises together with
   their presuppositions.
 *)

Section TypedStructuralRule.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement well-typed in the sense
      that its presuppositions are derivable, using just structural rules? 

  In fact, we ask for derivations not over just the structural rules but over the closure system associated to the empty flat type theory, so that infrastructure for derivations over general flat type theories can be used. *)
  Local Definition is_well_typed : Closure.rule (judgement Σ) -> Type
    := Closure.weakly_well_typed_rule
         presupposition (FlatTypeTheory.closure_system [<>]).

  (** Rules for variable-renaming are well typed *)
  Local Definition rename_is_well_typed
      (r : rename_instance Σ)
    : is_well_typed (rename_instance _ r).
  Proof.
    destruct r as [J [γ' f]]; cbn.
    set (J_orig := J); destruct J as [Γ [jf J]].
    intros p.
    set (p_orig := p : presupposition J_orig).
    (* In all cases, we just rename along [f] in the corresponding original
    presupposition.  However, this will require a different rule — either
    [rename_context] or [rename_hypotherical] — depending on whether [p] is
    the context presup or a hypothetical presup. *)
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exact (presupposition _ p_orig; (γ'; f)).
    - apply (ap (Build_judgement _)),
        (ap (Build_hypothetical_judgement _)).
      apply path_forall; intros i.
      recursive_destruct jf; recursive_destruct p; recursive_destruct i;
        apply idpath.
    - intros []. 
      simple refine (Closure.hypothesis' _ _).
      + apply inr. (* go for a presup *)
        exact (tt; p_orig). (* select corresponding original presup *)
      + apply idpath.
  Defined.

  (** Substitution-application rules are well typed *)
  Local Definition subst_apply_is_well_typed
        (r : subst_apply_instance Σ)
    : is_well_typed (subst_apply_instance _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f J]]].
    set (J_orig := Build_judgement Γ J); destruct J as [jf J].
    intros p.
    transparent assert (p' : (presupposition J_orig)). { exact p. }
    (* [p] a hypothetical presupposition *)
    simple refine (Closure.deduce' _ _ _).
    (* Aim here: apply the same substitution rule, with the same substition,
       but with target the presupposition [p] of the original target. *)
    - apply inl, subst_apply.
      exists Γ, Γ', f.
      exists (form_object (Judgement.boundary_slot _ p)).
      exact (hypothetical_part (presupposition _ p')).
    - recursive_destruct jf; recursive_destruct p;
        apply Judgement.eq_by_eta; apply idpath.
    - intros [ q | ].
      + (* premises: show the substitution OK. *)
        simple refine (Closure.hypothesis' _ _).
        * exact (inl (Some q)).
        * apply idpath.
      + (* premises: new presupposition *)
        simple refine (Closure.hypothesis' _ _).
        * exact (inr (None; p')).
        * apply idpath.
  Defined.


  (** Substitution-equality rules are well typed *)
  Local Definition subst_equal_is_well_typed
        (r : subst_equal_instance Σ)
    : is_well_typed (subst_equal_instance _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ g [cl J]]]]].
    intros p.
    transparent assert (J_orig : (judgement Σ)).
    { exists Γ, (form_object cl). exact J. }
    (* [p] a hypothetical presupposition *)
    (* What we do here genuinely depends on [cl]. *)
    destruct cl as [ | ].
    (* Case 1: substitutions are into a type judgement.
         Then the presups of [ Γ |- f^*A = g^*A ] are just
         [ Γ |- f^*A type ] and [ Γ |- g^*A type ].
         In each case, we get them by the [substitution_apply] rule. *)
    - simple refine (Closure.deduce' _ _ _).
      + apply inl, subst_apply.
        exists Γ, Γ'. simple refine (_;_). 2: { exact J_orig. }
        destruct p as [ [] | | ].
        * exact f.
        * exact g.
      + recursive_destruct p;
          apply Judgement.eq_by_eta; apply idpath.
      + intros h; cbn in h.
        destruct h as [ x | ].
        * (* premise: [f] / [g] is a context map *)
          destruct p as [ [] | | ].
          -- simple refine (Closure.hypothesis' _ _).
             ** apply inl, Some, inl, inl, x.
             ** apply idpath.
          -- simple refine (Closure.hypothesis' _ _).
             ** apply inl, Some, inl, inr, x.
             ** apply idpath.
        * (* premise: [Γ |- J]  *)
          simple refine (Closure.hypothesis' _ _).
          -- exact (inl None).
          -- apply idpath.
             
    (* Case 2: substitutions are into a term judgement [ Γ |- a : A].
         Then the presups of [ Γ |- f^*a = g^*a : f^* A] are
         [ Γ |- f^*A type ], [ Γ |- f^*a : f^*A ], and [ Γ |- g^*A : f^*A ].
         The first two, we get by the [substitution_apply] rule; the third 
         additionally requires the [term_convert] and [substitution_equal]
         rules. *)
    - set (A := J (the_boundary class_term the_term_type)).
      set (a := J (the_head class_term)).
      recursive_destruct p.
      + (* presup [ Γ |- f^*A type ] *)
        simple refine (Closure.deduce' _ _ _).
        * apply inl, subst_apply.
           (* subst-apply rule: substitute f into Γ |- A *)
           exists Γ, Γ', f, (form_object class_type).
           intros [[] | ]. exact A.
        * apply Judgement.eq_by_eta; apply idpath.
        * intros [ x | ].
           -- (* premise: [f] is a context map *)
             simple refine (Closure.hypothesis' _ _).
             ** apply inl, Some, inl, inl, x.
             ** apply idpath.
           -- (* premise: [Γ |- A type ]  *)
             simple refine (Closure.hypothesis' _ _).
             ** apply inr. exists None. exact (the_term_type).
             ** apply Judgement.eq_by_eta; apply idpath.
      + (* presup [ Γ' |- f^*a : f^*A ] *)
        simple refine (Closure.deduce' _ _ _).
        * apply inl, subst_apply.
           (* subst-apply rule: substitute f into Γ |- a : A *)
           exists Γ, Γ', f, (form_object class_term).
           exact J.
        * apply Judgement.eq_by_eta; apply idpath.
        * intros [ x | ].
           -- (* premise: [f] is a context map *)
             simple refine (Closure.hypothesis' _ _).
             ** apply inl, Some, inl, inl, x.
             ** apply idpath.
           -- (* premise: [Γ |- a : A type ]  *)
             simple refine (Closure.hypothesis' _ _).
             ** exact (inl None).
             ** apply idpath.
      + (* presup [ Γ' |- g^*a : f^*A ] *)
        apply Judgement.canonicalise.
        (* We want to apply [term_convert], but its conclusion is not exactly
   the judgement we want: its conclusion is the renaming *)
        apply derive_from_reindexing_to_empty_sum.
        simple refine (Closure.deduce' _ _ _).
        (*      Γ' |- g^*a : g^*A    Γ' |- g^*A = f^*A  
               ------------------------------------------ 
                        Γ' |- g^*a : f^*A                    *)
        * apply inl, term_convert.
           exists Γ'. cbn.
           intros i; recursive_destruct i; cbn.
           -- refine (rename _ (substitute g A)). (* [g^*A] *)
              apply shape_sum_empty_inl.
           -- refine (rename _ (substitute f A)). (* [f^*A] *)
              apply shape_sum_empty_inl.
           -- refine (rename _ (substitute g a)). (* [g^*a] *)
              apply shape_sum_empty_inl.
        * refine (Judgement.eq_by_expressions _ _).
           -- apply (coproduct_rect shape_is_sum).
              ** intros i. cbn.
                 eapply concat.
                 { refine (coproduct_comp_inj1 _). }
                 apply ap, ap, inverse.
                 apply (@eissect _ _ _ (shape_sum_empty_inl_is_equiv _)).
              ** apply (empty_rect _ shape_is_empty).
           -- intros i; recursive_destruct i; cbn.
              ** eapply concat.
                 2: { apply substitute_idmap. }
                 apply ap10; refine (apD10 _ _); apply ap.
                 apply path_forall.
                 refine (coproduct_rect shape_is_sum _ _ _).
                 2: { refine (empty_rect _ shape_is_empty _). }
                 intros i. refine (coproduct_comp_inj1 _).
              ** eapply concat.
                 2: { apply substitute_idmap. }
                 apply ap10; refine (apD10 _ _); apply ap.
                 apply path_forall.
                 refine (coproduct_rect shape_is_sum _ _ _).
                 2: { refine (empty_rect _ shape_is_empty _). }
                 intros i. refine (coproduct_comp_inj1 _).
        (* TODO: all the above gunk is from a single problem: the instantiation of a rule with empty local contexts doesn’t give you quite what you think it should!
   [derivation_from_reindexing_to_empty_sum] and [derivation_of_reindexing_to_empty_sum] help a bit, but still it’s pretty nasty.  How can we improve this?? *)
        * intros i; recursive_destruct i.
           -- (* [ Γ' |- g^*A type ] *)
             apply derive_judgement_over_empty_sum.
             simple refine (Closure.deduce' _ _ _).
             { apply inl, subst_apply.
               exists Γ, Γ', g, (form_object class_type).
               intros [ [] | ]. exact A.
             }
             { refine (Judgement.eq_by_expressions _ _).
               - intros i. apply inverse.
                 eapply concat.
                 { apply ap. refine (coproduct_comp_inj1 _). }
                 eapply concat. 2: { apply rename_idmap. }
                 eapply concat. 
                 { apply inverse, rename_comp. }
                 apply ap10. refine (apD10 _ _). apply ap.
                 apply path_forall. refine (eissect _).
               - intros i; recursive_destruct i. apply inverse.
                 eapply concat.
                 + cbn. apply ap. refine (_ @ substitute_idmap _).
                   apply ap10. refine (apD10 _ _). apply ap, path_forall.
                   refine (coproduct_rect shape_is_sum _ _ _).
                   * intros x. refine (coproduct_comp_inj1 _).
                   * apply (empty_rect _ shape_is_empty).
                 + eapply concat.
                   { apply inverse, rename_comp. }
                   eapply concat. 2: { apply rename_idmap. }
                   apply ap10. refine (apD10 _ _). apply ap, path_forall. 
                   refine (@eissect _ _ _ (shape_sum_empty_inl_is_equiv _)).
             }
             intros [ x | ].
             ** (* premise: [g] is a context map *)
               simple refine (Closure.hypothesis' _ _).
               --- cbn. apply inl, Some, inl, inr, x.
               --- apply idpath.
             ** (* premise: [Γ |- a : A type ]  *)
               simple refine (Closure.hypothesis' _ _).
               --- apply inr. (* use a presupposition… *)
                   exists None. (* …of the original target judgement… *)
                   apply the_term_type.
               --- apply Judgement.eq_by_eta, idpath.
           -- (* [ Γ' |- f^*A type ] *)
             refine (Closure.graft' _ _ _).
             { simple refine (derivation_of_reindexing_to_empty_sum _).
               exists Γ', (form_object class_type).
               intros [ [] | ]; cbn.
               exact (substitute f A). }
             { refine (Judgement.eq_by_expressions _ _).
               - refine (coproduct_rect shape_is_sum _ _ _).
                 2: { refine (empty_rect _ shape_is_empty _). }
                 intros i. apply inverse.
                 eapply concat. { refine (coproduct_comp_inj1 _). }
                 apply ap, ap, inverse. refine (coproduct_comp_inj1 _).
               - intros i; recursive_destruct i.
                 cbn. apply inverse.
                 eapply concat.
                 2: { apply substitute_idmap. }
                 apply ap10; refine (apD10 _ _); apply ap.
                 apply path_forall.
                 refine (coproduct_rect shape_is_sum _ _ _).
                 2: { refine (empty_rect _ shape_is_empty _). }
                 intros i. refine (coproduct_comp_inj1 _).
             }
             intros [].
             {
               transparent assert (instance : (subst_apply_instance Σ)).
               { exists Γ, Γ', f, (form_object class_type).
                 intros i. recursive_destruct i. exact A. }
               
               simple refine (Closure.deduce'
                                (inl (subst_apply instance) : (_ + _)%family)
                                _ _).
               - apply Judgement.eq_by_eta, idpath.
               - intros premise.
                 pose premise as p.
                 destruct premise as [ x | ]; rename p into premise;
                   fold premise; simpl (_ premise).
                 + admit.    (* the variables have types *)
                 + admit.    (* Γ ⊢ A *)
             }

           (* This should be almost identical to the preceding derivation of
     [ Γ' |- f^*A type ]. *)
           -- (* [ Γ' |- g^*A = f^*A ] *)
             admit.
           (* This should be quite similar to the derivation of [ Γ' |- g^*A = f^*A ]
   that follows it: essentially two steps, first using
   [derivation_of_reindexing_to_empty_sum], and then using [subst_equal]. *)
           -- (* Γ' |- g^*a : g^*A *)
             refine (Closure.graft' _ _ _).
             { simple refine (derivation_of_reindexing_to_empty_sum _).
               exists Γ', (form_object class_term).
               intros i; recursive_destruct i.
               - exact (substitute g A).
               - exact (substitute g a). }
             { refine (Judgement.eq_by_expressions _ _).
               (* TODO: can we find lemmas/tactics that simplify
                   something like this? *)
               - refine (coproduct_rect shape_is_sum _ _ _).
                 2: { refine (empty_rect _ shape_is_empty _). }
                 intros i. apply inverse.
                 eapply concat. { refine (coproduct_comp_inj1 _). }
                 apply ap, ap, inverse. refine (coproduct_comp_inj1 _).
               - intros i; recursive_destruct i.
                 + cbn. apply inverse.
                   eapply concat.
                   2: { apply substitute_idmap. }
                   apply ap10; refine (apD10 _ _); apply ap.
                   apply path_forall.
                   refine (coproduct_rect shape_is_sum _ _ _).
                   2: { refine (empty_rect _ shape_is_empty _). }
                   intros i. refine (coproduct_comp_inj1 _).
                 + cbn. apply inverse.
                   eapply concat.
                   2: { apply substitute_idmap. }
                   apply ap10; refine (apD10 _ _); apply ap.
                   apply path_forall.
                   refine (coproduct_rect shape_is_sum _ _ _).
                   2: { refine (empty_rect _ shape_is_empty _). }
                   intros i. refine (coproduct_comp_inj1 _).
             }
             intros [].
             simple refine (Closure.deduce' _ _ _).
             ** apply inl, subst_apply. (* subst-apply rule:
                                        substitute g into Γ |- a : A *)
                exists Γ, Γ', g, (form_object class_term). exact J.
             ** apply Judgement.eq_by_eta. apply idpath.
             ** intros [ x | ].
                --- (* premise: [g] is a context map *)
                  simple refine (Closure.hypothesis' _ _).
                  +++ cbn. apply inl, Some, inl, inr, x.
                  +++ apply idpath.
                --- (* premise: [Γ |- a : A type ]  *)
                  simple refine (Closure.hypothesis' _ _).
                  +++ exact (inl None).
                  +++ apply idpath.
  Admitted.

  (** Variable rules are well typed *)
  Local Definition variable_is_well_typed (r : variable_instance Σ)
    : is_well_typed (variable_instance _ r).
  Proof.
    destruct r as [Γ x].
    intros i; recursive_destruct i.
    (* type presupposition *)
    simple refine (Closure.hypothesis' _ _).
    - apply inl, tt.
    - apply Judgement.eq_by_eta; apply idpath.
  Defined.

  Section Equality_Flat_Rules.
  (** For the equality rules, we first show that they are well-typed as _flat_
  rules; it follows that their instantiations as closure conditions are well-
  typed as such. 

  We give most together in [equality_flat_rule_is_well_typed], but break out
  the particularly long cases beforehand individually. *)

  Local Definition tmeq_convert_is_well_typed
    : TypedFlatRule.weakly_well_typed [<>] (@tmeq_convert_rule σ). 
  Proof.
    (* tmeq_convert: 
       ⊢ A, B type
       ⊢ A ≡ B type
       ⊢ u, u' : A
       ⊢ u = u' : A
       -------------
       ⊢ u = u' : B
       *)
    set (metas := flat_rule_metas (@tmeq_convert_rule σ)).
    pose (A := Some (Some (Some tt)) : metas).
    pose (B := Some (Some None) : metas).
    pose (u := Some None : metas).
    pose (u' := None : metas).
    subst metas.
    intros [ [] | | ].
    - (* type presup :  |- B type *)
      simple refine (Closure.hypothesis' _ _).
      + apply inl. refine (Some (Some (Some (Some None)))).
      + apply Judgement.eq_by_eta, idpath.
    - (* LHS presup :   |- u : B *)
      apply derive_from_reindexing_to_empty_sum.
      simple refine (Closure.deduce' _ _ _).
      + apply inl, term_convert.
        exists [::]. intros [ [ [] | ] | ].
        * exact [M/ A /].
        * exact [M/ B /].
        * exact [M/ u /].
      + refine (Judgement.eq_by_expressions _ _).
        * apply (coproduct_rect shape_is_sum);
            exact (empty_rect _ shape_is_empty _).
        * intros [ [] | ]; cbn; apply ap, path_forall;
            exact (empty_rect _ shape_is_empty _).
      + intros i. set (i_keep := i).
   (* Note: the following chain, though slow, is substantially faster than I (PLL)
   was able to get any other way. To compare this with solving the goals
   individually, see commit f648e3e. *)
        destruct i as [[[[] | ] | ] | ];
          apply derive_judgement_over_empty_sum;
          (simple refine (Closure.hypothesis' _ _);
           [ exact (inl (Some (Some i_keep)))
           | refine (Judgement.eq_by_expressions _ _);
             [ refine (empty_rect _ shape_is_empty _)
             | intros i; recursive_destruct i;
               cbn; apply ap, path_forall;
               refine (empty_rect _ shape_is_empty _)
             ]
          ] ).
    - (* RHS presup :   |- u' : B *)
      apply derive_from_reindexing_to_empty_sum.
      simple refine (Closure.deduce' _ _ _).
      + apply inl, term_convert.
        exists [::]. intros [ [ [] | ] | ].
        * exact [M/ A /].
        * exact [M/ B /].
        * exact [M/ u' /].
      + refine (Judgement.eq_by_expressions _ _).
        * apply (coproduct_rect shape_is_sum);
            exact (empty_rect _ shape_is_empty _).
        * intros [ [] | ]; cbn; apply ap, path_forall;
            exact (empty_rect _ shape_is_empty _).
      + intros i. set (i_keep := i).
        destruct i as [[[[] | ] | ] | ];
          apply derive_judgement_over_empty_sum;
          try (simple refine (Closure.hypothesis' _ _);
               [ exact (inl (Some (Some i_keep)))
               | refine (Judgement.eq_by_expressions _ _);
                 [ refine (empty_rect _ shape_is_empty _)
                 | intros i; recursive_destruct i;
                   cbn; apply ap, path_forall;
                   refine (empty_rect _ shape_is_empty _)
                 ]
              ] ).
        (* remaining hypothesis : |- b : B *)
        simple refine (Closure.hypothesis' _ _).
        * exact (inl (Some None)).
        * refine (Judgement.eq_by_expressions _ _);
            [ refine (empty_rect _ shape_is_empty _)
            | intros i; recursive_destruct i;
              cbn; apply ap, path_forall;
              refine (empty_rect _ shape_is_empty _)
            ].
  Defined.

  Local Definition equality_flat_rule_is_well_typed
      (r : @equality_flat_rule σ)
    : TypedFlatRule.weakly_well_typed [<>] (equality_flat_rule r).
  Proof.
    destruct r as [[[[[[[ ] | ] | ] | ] | ] | ] | ]; cbn.
    - (* tyeq_refl: Γ |- A  // Γ |- A = A *)
      intros [ [] | | ].
      + (* left-hand side presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
      + (* right-hand side presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
    - admit. (* tyeq_sym *)
    - admit. (* tyeq_trans *)
    - admit. (* tmeq_refl *)
    - (* tmeq_sym :  |- a = b : A //  |- b = a : A *)
      set (metas := flat_rule_metas (@tmeq_sym_rule σ)).
      set (A := Some (Some tt) : metas).
      set (a := Some None : metas).
      set (b := None : metas).
      subst metas.
      intros [ [] | | ].
      + (* type presup :  |- A type *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt.
          refine (the_equality_sort class_term the_term_type).
        * apply Judgement.eq_by_eta, idpath.
      + (* LHS presup :   |- a : A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. exact (the_equality_rhs _).
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup :   |- b : A*)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. exact (the_equality_lhs _).
        * apply Judgement.eq_by_eta, idpath. 
    - admit. (* tmeq_trans *)
    - admit. (* term_convert *)
    - (* tmeq_convert *)
      apply tmeq_convert_is_well_typed.
  Admitted.
  (* TODO: some thoughts from this proof:
  - rename [the_equality_sort], to eg [the_equality_boundary]? 
  - make presuppositions less option-blind? 
  - maybe make structural rule accessors take value in closure systems of type theories, not in [structural_rules] itself?  (More convenient for giving derivations; but then recursion over structural rules is less clear.) 
*)


  
  End Equality_Flat_Rules.

  (** Equality rules are well typed (as closure rules) *)
  Local Definition equality_is_well_typed (r : equality_instance Σ)
    : is_well_typed (equality_instance _ r).
  Proof.
    destruct r as [r [Γ I]].
    set (r_flat_rule := equality_flat_rule r).
    intros c_presup.
    refine (TypedFlatRule.closure_system_weakly_well_typed _ _ _ _ _).
    (* TODO: [TypedFlatRule.fmap_weakly_well_typed],
     then apply to [equality_flat_rule_is_well_typed]. *)
  Admitted.

  (** Putting the above components together, we obtain the main result:
      all structural rules are well-typed. *)
  Local Definition well_typed
    : forall r : structural_rule Σ, is_well_typed (structural_rule Σ r).
  Proof.
    apply structural_rule_rect.
    - apply rename_is_well_typed.
    - apply subst_apply_is_well_typed.
    - apply subst_equal_is_well_typed.
    - apply variable_is_well_typed.
    - apply equality_is_well_typed.
  Defined.

End TypedStructuralRule.
