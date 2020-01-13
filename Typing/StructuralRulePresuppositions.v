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
Require Import Typing.Presuppositions.
(* TODO: rename file to “presuppositive…”; perhaps roll into [Typing.Presuppositions]? *)

(** We show that all the structural rules are presuppositive.

   In general this means only _weak_ presuppositivity: for each rule, we derive
   the presuppositions of its conclusion, from its premises together with
   their presuppositions.
 *)

Section TypedStructuralRule.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** In this section we show that all structural rules are presuppositive, in the
  sense that whenever their premises are derivable, all the presuppositions of their
  premises/conclusion are derivable. *)

  (** Is a given closure rule arising from a total judgement presuppositive in the sense
      that its presuppositions are derivable, using just structural rules? 

  In fact, we ask for derivations not over just the structural rules but over the closure system associated to the empty flat type theory, so that infrastructure for derivations over general flat type theories can be used. *)
  Local Definition is_presuppositive : Closure.rule (judgement Σ) -> Type
    := Closure.weakly_presuppositive_rule
         presupposition (FlatTypeTheory.closure_system [<>]).

  (** Rules for variable-renaming are presuppositive *)
  Local Definition rename_is_presuppositive
      (r : rename_instance Σ)
    : is_presuppositive (rename_instance _ r).
  Proof.
    destruct r as [Γ [Γ' [f J]]]; cbn.
    set (J_orig := Build_judgement Γ J).
    intros p.
    set (p_orig := p : presupposition J_orig).
    (* We just need to rename along [f] in the corresponding original
    presupposition. *)
    simple refine (derive_rename' _ _ _ _ _).
    { exact (presupposition J_orig p_orig). }
    { exact f. }
    { apply (ap (Build_hypothetical_judgement _)), path_forall; intros i.
      destruct J as [jf j]. 
      recursive_destruct jf; recursive_destruct p; recursive_destruct i;
        apply idpath.
    }
      simple refine (Closure.hypothesis' _ _).
      + apply inr. (* go for a presup *)
        exact (tt; p_orig). (* select corresponding original presup *)
      + apply idpath.
  Defined.

  (** Substitution-application rules are presuppositive *)
  Local Definition subst_apply_is_presuppositive
        (r : subst_apply_instance Σ)
    : is_presuppositive (subst_apply_instance _ r).
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

  (** Substitution-equality rules are presuppositive *)
  Local Definition subst_equal_is_presuppositive
        (r : subst_equal_instance Σ)
    : is_presuppositive (subst_equal_instance _ r).
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
    - set (A := J (the_object_boundary_slot class_term the_type_slot)).
      set (a := J (the_head_slot class_term)).
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
             ** apply inr. exists None. exact (the_type_slot).
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
        apply (derive_term_convert _ (substitute g A)).
        * (* [ Γ' |- g^*A type ] *)
          simple refine (Closure.deduce' _ _ _).
          { apply inl, subst_apply.
            exists Γ, Γ', g, (form_object class_type).
            intros [ [] | ]. exact A.
          }
          { apply Judgement.eq_by_eta, idpath. }
          intros [ x | ].
          -- (* premise: [g] is a context map *)
            simple refine (Closure.hypothesis' _ _).
            ++ cbn. apply inl, Some, inl, inr, x.
            ++ apply idpath.
          -- (* premise: [Γ |- A type ]  *)
            simple refine (Closure.hypothesis' _ _).
            ++ apply inr. (* use a presupposition… *)
               exists None. (* …of the original target judgement… *)
               apply the_type_slot.
            ++ apply Judgement.eq_by_eta, idpath.
        * (* [ Γ' |- f^*A type ] *)
          simple refine (Closure.deduce' _ _ _).
          { apply inl, subst_apply.
            exists Γ, Γ', f, (form_object class_type).
            intros [ [] | ]. exact A.
          }
          { apply Judgement.eq_by_eta, idpath. }
          intros [ x | ].
          -- (* premise: [f] is a context map *)
            simple refine (Closure.hypothesis' _ _).
            ++ cbn. apply inl, Some, inl, inl, x.
            ++ apply idpath.
          -- (* premise: [Γ |- A type ]  *)
            simple refine (Closure.hypothesis' _ _).
            ++ apply inr. (* use a presupposition… *)
               exists None. (* …of the original target judgement… *)
               apply the_type_slot.
            ++ apply Judgement.eq_by_eta, idpath.
        * (* [ Γ' |- g^*A = f^*A ] *)
          apply derive_tyeq_sym.
          simple refine (Closure.deduce' _ _ _).
          -- apply inl, subst_equal.
             exists Γ, Γ', f, g, class_type.
             intros i; recursive_destruct i. exact A.
          -- apply Judgement.eq_by_eta, idpath.
          -- intros [ h | ].
            ++ (* for premises about f, g:
                  use corresponding premise of original rule *)
              simple refine (Closure.hypothesis' _ _).
              ** apply inl, Some, h.
              ** apply idpath.
            ++ (* premise [ Γ |- A type ]*)
              simple refine (Closure.hypothesis' _ _).
              ** apply inr. (* use a presupposition… *)
               exists None. (* …of the original target judgement… *)
               apply the_type_slot.
              ** apply Judgement.eq_by_eta, idpath.
        * (* Γ' |- g^*a : g^*A *)   
          simple refine (Closure.deduce' _ _ _).
          -- apply inl, subst_apply. (* substitute g into Γ |- a : A *)
             exists Γ, Γ', g, (form_object class_term). exact J.
          -- apply Judgement.eq_by_eta, idpath.
          -- intros [ x | ].
            ++ (* premise: [g] is a context map *)
              simple refine (Closure.hypothesis' _ _).
              ** cbn. apply inl, Some, inl, inr, x.
              ** apply idpath.
            ++ (* premise: [Γ |- a : A type ]  *)
              simple refine (Closure.hypothesis' _ _).
              ** exact (inl None).
              ** apply idpath.
Defined.

  (** Variable rules are presuppositive *)
  Local Definition variable_is_presuppositive (r : variable_instance Σ)
    : is_presuppositive (variable_instance _ r).
  Proof.
    destruct r as [Γ x].
    intros i; recursive_destruct i.
    (* type presupposition *)
    simple refine (Closure.hypothesis' _ _).
    - apply inl, tt.
    - apply Judgement.eq_by_eta; apply idpath.
  Defined.

  Section Equality_Flat_Rules.
  (** For the equality rules, we first show that they are presuppositive as _flat_
  rules; it follows that their instantiations are as closure conditions.

  We give most together in [equality_flat_rule_is_presuppositive], but break out
  the particularly long cases beforehand individually. *)

  Local Definition tmeq_convert_is_presuppositive
    : weakly_presuppositive_flat_rule [<>] (@tmeq_convert_rule σ). 
  Proof.
    (* tmeq_convert: 
       ⊢ A, B type
       ⊢ A ≡ B type
       ⊢ u, u' : A
       ⊢ u = u' : A
       -------------
       ⊢ u = u' : B
       *)
    pose (A := Some (Some (Some tt))
               : flat_rule_metas (@tmeq_convert_rule σ)).
    intros [ [] | | ].
    - (* type presup :  |- B type *)
      simple refine (Closure.hypothesis' _ _).
      + apply inl. refine (Some (Some (Some (Some None)))).
      + apply Judgement.eq_by_eta, idpath.
    - (* LHS presup :   |- u : B *)
      apply Judgement.canonicalise.
      apply (derive_term_convert _ [M/ A /]).
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some (Some (Some tt))))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some (Some None)))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some None))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some None)).
        * apply idpath.
    - (* RHS presup :   |- u' : B *)
      apply Judgement.canonicalise.
      apply (derive_term_convert _ [M/ A /]).
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some (Some (Some tt))))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some (Some None)))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some (Some (Some None))).
        * apply idpath.
      + simple refine (Closure.hypothesis' _ _).
        * apply inl. refine (Some None).
        * apply idpath.
  Defined.

  Local Definition equality_flat_rule_is_presuppositive
      (r : @equality_flat_rule σ)
    : weakly_presuppositive_flat_rule [<>] (equality_flat_rule r).
  Proof.
    recursive_destruct r; cbn.
    - (* tyeq_refl: Γ |- A  // Γ |- A = A *)
      intros p; recursive_destruct p.
      + (* left-hand side presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
      + (* right-hand side presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
    - (* tyeq_sym *)
      intros p; recursive_destruct p.
      + (* LHS presup: Γ |- B *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_rhs_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_lhs_slot.
        * apply Judgement.eq_by_eta, idpath.
    - (* tyeq_trans *)
      intros p; recursive_destruct p.
      + (* LHS presup: Γ |- A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists (Some tt). apply the_lhs_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup: Γ |- C *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists None. apply the_rhs_slot.
        * apply Judgement.eq_by_eta, idpath.
    - (* tmeq_refl *)
      intros p; recursive_destruct p.
      + (* type presup: Γ |- A type *)        
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_type_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* LHS presup: Γ |- a:A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup: Γ |- a:A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inl. exact tt.
        * apply Judgement.eq_by_eta, idpath.
    - (* tmeq_sym :  |- a = b : A //  |- b = a : A *)
      intros p; recursive_destruct p.
      + (* type presup :  |- A type *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_equality_boundary_slot, the_type_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* LHS presup :   |- a : A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_rhs_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup :   |- b : A*)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists tt. apply the_lhs_slot.
        * apply Judgement.eq_by_eta, idpath.
    - (* tmeq_trans *)
      intros p; recursive_destruct p.
      + (* type presup: Γ |- A type *)        
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists None. apply the_equality_boundary_slot, the_type_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* LHS presup: Γ |- a:A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists (Some tt). apply the_lhs_slot.
        * apply Judgement.eq_by_eta, idpath.
      + (* RHS presup: Γ |- a:A *)
        simple refine (Closure.hypothesis' _ _).
        * apply inr. exists None. apply the_rhs_slot.
        * apply Judgement.eq_by_eta, idpath.
    - (* term_convert *)
      intros p; recursive_destruct p.
      + (* type presup: Γ |- A type *)        
        simple refine (Closure.hypothesis' _ _).
        * apply inl. apply Some, Some, None.
        * apply Judgement.eq_by_eta, idpath.
    - (* tmeq_convert *)
      apply tmeq_convert_is_presuppositive.
  Defined.
  (* TODO: some thoughts from this proof:
  - rename [the_equality_boundary_slot], to eg [the_equality_boundary]? 
  - make presuppositions and hypothesis selection less option-blind (but how)? 
  - maybe make structural rule accessors take value in closure systems of type theories, not in [structural_rules] itself?  (More convenient for giving derivations; but then recursion over structural rules is less clear.) 
*)
  
  End Equality_Flat_Rules.

  (** Equality rules are presuppositive (as closure rules) *)
  Local Definition equality_is_presuppositive (r : equality_instance Σ)
    : is_presuppositive (equality_instance _ r).
  Proof.
    destruct r as [r [Γ I]].
    set (r_flat_rule := equality_flat_rule r).
    intros c_presup.
    refine (flat_rule_closure_system_weakly_presuppositive _ _ _ _ _).
    eapply fmap_weakly_presuppositive_flat_rule.
    2: apply equality_flat_rule_is_presuppositive.
    intros [].
  Defined.

  (** Putting the above components together, we obtain the main result:
      all structural rules are presuppositive. *)
  Definition is_presuppositive_structural_rule
    : forall r : structural_rule Σ, is_presuppositive (structural_rule Σ r).
  Proof.
    apply structural_rule_rect.
    - apply rename_is_presuppositive.
    - apply subst_apply_is_presuppositive.
    - apply subst_equal_is_presuppositive.
    - apply variable_is_presuppositive.
    - apply equality_is_presuppositive.
  Defined.

End TypedStructuralRule.
