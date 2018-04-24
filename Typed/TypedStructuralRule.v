Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawStructuralRule.
Require Import Typed.TypedClosure.
Require Import Raw.FlatTypeTheoryMap.
Require Import Raw.FlatRule.

(** We show that all the structural rules are well-typed.

   For the ones stated as flat rules, this means showing they’re well-typed as such: i.e.
   showing that whenever their premises hold, then all the presuppositions of both their
   premises and conclusion hold.
*)

Section TypedStructuralRule.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are well-typed, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement well-typed in the sense
      that its presuppositions are derivable using structural rules? *)
  Local Definition is_well_typed : Closure.rule (judgement_total Σ) -> Type
  := TypedClosure.weakly_well_typed_rule presupposition (structural_rule Σ).

  (** Context rules are well typed. *)
  Local Definition ctx_is_well_typed (r : RawStructuralRule.context Σ)
    : is_well_typed (RawStructuralRule.context _ r).
  Proof.
    apply TypedClosure.weakly_from_strongly_well_typed_rule.
    destruct r as [  [Γ A] | ].
    - split. (* context extension *)
      + intros [ [] | ]. (* two premises *)
        * intros []. (* context hypothesis: no presups *)
        * intros [ [] | ]. (* type hypothesis: one presup *)
          eapply (flip (transport _)).
          { refine (Closure.hypothesis _ _ _).
            cbn. apply (Some tt). }
          apply idpath.
      + intros []. (* conclusion: no presups *)
    - split. (* empty context rule *)
      + intros []. (* no premises *)
      + intros []. (* no presups for conclusion *)
  Defined.

  (** Substitution-application rules are well typed *)
  Local Definition subst_apply_is_well_typed
        (r : RawStructuralRule.subst_apply Σ)
    : is_well_typed (RawStructuralRule.subst_apply _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ hjf J]]]].
    intros p.
    transparent assert (j : (judgement_total Σ)).
      { exists (form_hypothetical hjf). refine (Γ;J). }
    transparent assert (p' : (presupposition j)).
      { exact p. }
    destruct p as [ p | ].
    - (* [p] a hypothetical presupposition *)
      eapply (flip (transport _)).
      + simple refine (Closure.deduce _ _ _ _).
        (* Aim here: apply the same substitution rule, with the same substition,
           but with target the presupposition [p] of the original target. *)
        * apply inl, inl, inr, inl.
          (* TODO: give access functions for locating the structural rules! *)
          exists Γ, Γ', f.
          exists (form_object (Judgement.boundary_slot _ p)).
          exact (pr2 (pr2 (presupposition _ p'))).
        * intros [ q | ].
          -- (* premises: show the substitution OK. *)
            eapply (flip (transport _)).
            ++ refine (Closure.hypothesis _ _ _). exact (inl (Some q)).
            ++ apply idpath.
          -- (* premises: new presupposition *)
            eapply (flip (transport _)).
            ++ refine (Closure.hypothesis _ _ _). exact (inr (None; p')).
            ++ apply idpath.
      + recursive_destruct hjf; recursive_destruct p;
          apply Judgement.eq_by_eta; apply idpath.
    - (* [p] the context presupposition [Γ'] *)
      eapply (flip (transport _)).
      { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
      apply idpath.
  Defined.

  (* TODO: upstream *)
  Definition shape_sum_empty (γ : σ) : σ
  := shape_sum γ (shape_empty σ).

  (* TODO: upstream *)
  Definition raw_context_sum_empty_inl (γ : σ)
    : Context.map Σ (shape_sum_empty γ) γ.
  Proof.
    intros x. apply raw_variable, (coproduct_inj1 shape_is_sum), x.
  Defined.    

  (* TODO: upstream *)
  Definition raw_context_sum_empty (Γ : raw_context Σ)
    : raw_context Σ.
  Proof.
    exists (shape_sum_empty Γ).
    apply (coproduct_rect shape_is_sum).
    - intros i; refine (substitute _ (Γ i)).
      apply raw_context_sum_empty_inl.
    - apply (empty_rect _ shape_is_empty).
  Defined.

  (* TODO: upstream *)
  Definition reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical hjf).
    exists (raw_context_sum_empty Γ).
    intros i. exact (substitute (raw_context_sum_empty_inl _) (J i)).
  Defined.

  (* TODO: upstream *)
  (** To derive a judgement [ Γ |- J ],
      it’s sufficient to derive [ Γ;[] |- r^* J ],
   where [Γ;[]] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to that context. *)
  Definition derive_from_reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ)
        [< reindexing_to_empty_sum J >] 
        (form_hypothetical hjf ; (Γ ; J)).
  Proof.
    (* substitution rule, along the _inverse_ context morphism of
       [raw_context_sum_empty_inl], plus substitution functoriality lemma
       to show that the conclusion of that is the original judgement. *)
  Admitted.

  (** Substitution-equality rules are well typed *)
  Local Definition subst_equal_is_well_typed
        (r : RawStructuralRule.subst_equal Σ)
    : is_well_typed (RawStructuralRule.subst_equal _ r).
  Proof.
    destruct r as [Γ [ Γ' [ f [ g [cl J]]]]].
    intros p.
    transparent assert (j : (judgement_total Σ)).
      { exists (form_hypothetical (form_object cl)). refine (Γ;J). }
    destruct p as [ p | ].
    - (* [p] a hypothetical presupposition *)
      (* What we do here genuinely depends on [cl]. *)
      destruct cl as [ | ].
      (* Case 1: substitutions are into a type judgement.
         Then the presups of [ Γ |- f^*A = g^*A ] are just
         [ Γ |- f^*A type ] and [ Γ |- g^*A type ].
         In each case, we get them by the [substitution_apply] rule. *)
      + eapply (flip (transport _)).
        { simple refine (Closure.deduce _ _ _ _).
          * apply inl, inl, inr, inl.
            exists Γ, Γ'. refine (_;(form_object class_type; J)).
            destruct p as [ [] | | ].
            -- exact f.
            -- exact g.
          * intros h; cbn in h.
            destruct h as [ [ x | ] | ].
            -- (* premise: [f] / [g] is a context map *)
              destruct p as [ [] | | ].
              ++ eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _).
                   apply inl, Some, Some, inl, inl, x. }
                 apply idpath.
              ++ eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _).
                   apply inl, Some, Some, inl, inr, x. }
                 apply idpath.
            -- (* premise: [Γ'] is a context *)
              eapply (flip (transport _)).
              { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
              apply idpath.
            -- (* premise: [Γ |- J]  *)
              eapply (flip (transport _)).
              { refine (Closure.hypothesis _ _ _). exact (inl None). }
              apply idpath.
        }
        recursive_destruct p;
          apply Judgement.eq_by_eta; apply idpath.
      (* Case 2: substitutions are into a term judgement [ Γ |- a : A].
         Then the presups of [ Γ |- f^*a = g^*a : f^* A] are
         [ Γ |- f^*A type ], [ Γ |- f^*a : f^*A ], and [ Γ |- g^*A : f^*A ].
         The first two, we get by the [substitution_apply] rule; the third 
         additionally requires the [term_convert] and [substitution_equal]
         rules. *)
   (* TODO: to make the following clearer, and reduce use of [transport], consider giving lemmas that “standardise” the hypothetical part of a judgement, in the conclusion of a derivation. *)
      + recursive_destruct p.
        * (* presup [ Γ |- f^*A type ] *)
          eapply (flip (transport _)).
          { simple refine (Closure.deduce _ _ _ _).
            -- apply inl, inl, inr, inl.
               exists Γ, Γ', f. refine (form_object class_type; _).
               intros [[] | ].
               exact (J (the_boundary class_term the_term_type)).
            -- intros [ [ x | ] | ].
               ++ (* premise: [f] is a context map *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _).
                   apply inl, Some, Some, inl, inl, x. }
                 apply idpath.
               ++ (* premise: [Γ'] is a context *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
                 apply idpath.
               ++ (* premise: [Γ |- A type ]  *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _).
                 apply inr. exists None. exact (Some the_term_type). }
                 apply Judgement.eq_by_eta; apply idpath.
          }
          apply Judgement.eq_by_eta; apply idpath.
        * (* presup [ Γ' |- f^*a : f^*A ] *)
          eapply (flip (transport _)).
          { simple refine (Closure.deduce _ _ _ _).
            -- apply inl, inl, inr, inl. (* apply substitution rule:
                                            substitute f into Γ |- a : A *)
               exists Γ, Γ', f. refine (form_object class_term; _).
               exact J.
            -- intros [ [ x | ] | ].
               ++ (* premise: [f] is a context map *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _).
                   apply inl, Some, Some, inl, inl, x. }
                 apply idpath.
               ++ (* premise: [Γ'] is a context *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
                 apply idpath.
               ++ (* premise: [Γ |- a : A type ]  *)
                 eapply (flip (transport _)).
                 { refine (Closure.hypothesis _ _ _). exact (inl None). }
                 apply idpath.
          }
          apply Judgement.eq_by_eta; apply idpath.
        * (* presup [ Γ' |- g^*a : f^*A ] *)
          apply Judgement.canonicalise. unfold Judgement.eta_expand; cbn.
          eapply (flip (transport _)).
          { refine (Closure.graft _ _ _).
            -- simple refine (derive_from_reindexing_to_empty_sum _).
               exact Γ'. exact (form_object class_term).
               intros i; recursive_destruct i.
               ++ exact (substitute f (J (the_boundary class_term the_term_type))).
               ++ exact (substitute g (J (the_head class_term))).
            -- intros [].
               eapply (flip (transport _)).
               { simple refine (Closure.deduce _ _ _ _).
                 ++ apply inr. cbn. exists (Some None). (* term_convert rule *)
                    exists Γ'. cbn.
                    intros i; recursive_destruct i; cbn.
                    ** refine (substitute _ (substitute f
                         (J (the_boundary class_term the_term_type)))). (* [f^*A] *)
                       apply raw_context_sum_empty_inl.
                    ** refine (substitute _ (substitute g
                         (J (the_boundary class_term the_term_type)))). (* [g^*A] *)
                       apply raw_context_sum_empty_inl.
                    ** refine (substitute _ (substitute g
                         (J (the_head _)))). (* [g^*a] *)
                       apply raw_context_sum_empty_inl.
   (* TODO: all the above three are the same problem: renaming between a proto-context and its sum with the empty shape.  Think about how to make a utility lemma to deal with this situation!
   E.g. given an “algebraic” flat rule, can get a derivable equivallent that doesn’t add this damn thing to the context? *)
                 ++ admit. (* from hypotheses, via an inverse to
                              [derive_from_reindexing_to_empty_sum]. *)
               }
               apply Judgement.eq_by_eta.
               apply ap.
               admit. (*functoriality of substitution *)
          }
          apply idpath.
    - (* [p] the context presupposition [Γ'] *)
      eapply (flip (transport _)).
      { refine (Closure.hypothesis _ _ _). exact (inl (Some None)). }
      apply idpath.
  Admitted.

  (** All substitution rules are well typed *)
  Local Definition subst_is_well_typed (r : RawStructuralRule.substitution Σ)
    : is_well_typed (RawStructuralRule.substitution _ r).
  Proof.
    destruct r as [ r_apply | r_equal ].
    - apply subst_apply_is_well_typed.
    - apply subst_equal_is_well_typed.
  Defined.

  (** Variable rules are well typed *)
  Local Definition variable_is_well_typed (r : RawStructuralRule.variable Σ)
    : is_well_typed (RawStructuralRule.variable _ r).
  Proof.
    destruct r as [Γ x].
    intros i; recursive_destruct i.
    (* type presupposition *)
    - eapply (flip (transport _)). 
      + refine (Closure.hypothesis _ _ _).
        cbn.
        apply inl, None.
      + apply Judgement.eq_by_eta; apply idpath.
    (* context presupposition *)
    - eapply (flip (transport _)). 
      + refine (Closure.hypothesis _ _ _).
        cbn. apply inl, Some, tt.
      + cbn. apply idpath.
  Defined.

  (** Equality rules are well typed *)
  Local Definition equality_is_well_typed (r : RawStructuralRule.equality Σ)
    : is_well_typed (RawStructuralRule.equality _ r).
  Proof.
    (* deduce from showing these are well-typed as flat rules *)
  Admitted.

  (** Putting the above components together, we obtain the main result:
      all structural rules are well-typed. *)
  Local Definition well_typed
    : TypedClosure.weakly_well_typed_system presupposition (structural_rule Σ).
  Proof.
    intros [ [ [ r_cxt | r_subst ] | r_var ] | r_eq ].
    - apply ctx_is_well_typed.
    - apply subst_is_well_typed.
    - apply variable_is_well_typed.
    - apply equality_is_well_typed.
  Defined.

End TypedStructuralRule.
