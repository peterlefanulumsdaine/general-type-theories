Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ScopeSystem.
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

Section StructuralRulePresups.

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

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
    { apply eq_by_expressions_hypothetical_judgement; intros i.
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
    destruct r as [Γ [ Γ' [J [f f_triv]]]].
    set (J_orig := Build_judgement Γ J); destruct J as [jf J].
    intros p.
    transparent assert (p' : (presupposition J_orig)). { exact p. }
    (* [p] a hypothetical presupposition *)
    simple refine (derive_subst_apply' _ _ _ _ _ _).
    - exact (presupposition _ p').
    - exact f.
    - recursive_destruct jf; recursive_destruct p;
        apply Judgement.eq_by_eta_hypothetical_judgement, idpath.
    - (* premises: show the substitution OK. *)
      intros i.
      destruct (some_or_is_none (f_triv i)) as [[j [e_fi e_Γ'j]]| fi_nontriv].
      + apply inl. exists j. split; assumption.
      + apply inr.
        simple refine (Closure.hypothesis' _ _).
        * apply inl, Some; exists i. apply fi_nontriv.
        * apply idpath.
    - (* premises: new presupposition *)
      simple refine (Closure.hypothesis' _ _).
      + exact (inr (None; p')).
      + apply idpath.
  Defined.

  (** Substitution-equality rules are presuppositive *)
  Local Definition subst_equal_is_presuppositive
        (r : subst_equal_instance Σ)
    : is_presuppositive (subst_equal_instance _ r).
  Proof.
    destruct r as [Γ [ Γ' [ [f g] [ fg_triv [cl J_expr]]]]].
    intros p.
    (* Several subderivations are used multiple times, so we predefine those
    in advance before case-splitting*)
    transparent assert (J : (judgement Σ)).
    { exists Γ, (form_object cl). exact J_expr. }
    match goal with
      [|- Closure.derivation ?TT ?HH _ ]
      => set (T := (TT)); set (Hs := (HH))
    end.
    assert (d_f : forall i : Γ,
      {j : Γ'.(raw_context_carrier)
        & (f i = raw_variable j) * (Γ' j = substitute f (Γ i))}
      + Closure.derivation T Hs [!Γ' |- f i; substitute f (Γ i) !]).
    { intros i.
      destruct (some_or_is_none (fg_triv i)) as [ fgi_triv | fgi_nontriv].
      - apply inl. destruct fgi_triv as [ j [[? _] [? _]]].
        exists j; split; assumption.
      - apply inr. simple refine (Closure.hypothesis' _ _).
        { apply inl, Some. exists (i;fgi_nontriv). apply Some, Some, tt. }
        apply idpath.
    }
    assert (d_g : forall i : Γ,
      {j : Γ'.(raw_context_carrier)
        & (g i = raw_variable j) * (Γ' j = substitute g (Γ i))}
      + Closure.derivation T Hs [!Γ' |- g i; substitute g (Γ i) !]).
    { intros i.
      destruct (some_or_is_none (fg_triv i)) as [ fgi_triv | fgi_nontriv].
      - apply inl. destruct fgi_triv as [ j [[_ ?] [_ ?]]].
        exists j; split; assumption.
      - apply inr. simple refine (Closure.hypothesis' _ _).
        { apply inl, Some. exists (i;fgi_nontriv). apply Some, None. }
        apply idpath.
    }
    set (p_keep := p). simpl Closure.conclusion in p_keep.
    (* The main case-split: which presupposition are we doing? *)
    destruct p as [ p_bdry | | ].
    - (* Presup: part of boundary of conclusion. *)
      destruct cl; recursive_destruct p_bdry.
      (* Only one case: original conclusion was [! Γ' |- f^*a = g^*a : f^*A !],
       presup is [! Γ' |- f^* A !]. *)
      apply Judgement.canonicalise; simpl.
      refine (derive_subst_apply' [! Γ |- _ !] [! _ |- _ !] _ _ d_f _).
      { apply eq_by_eta_hypothetical_judgement, idpath. }
      simple refine (Closure.hypothesis' _ _).
      + apply inr. exists None. exact the_type_slot.
      + apply Judgement.eq_by_eta, idpath.
    - (* Presup: LHS of original equality conclusion. *)
      refine (derive_subst_apply' J _ _ _ _ _).
      2: { apply d_f. }
      { destruct cl; apply eq_by_eta_hypothetical_judgement; apply idpath. }
      simple refine (Closure.hypothesis' _ _). { apply inl, None. }
      apply idpath.
    - (* Presup: RHS of original equality conclusion.
      This case looks different depending on the form of the conclusion,
      due to non-triviality of the boundary for term judgements. *)
(* NOTE: could unify these cases by generalising the [_convert] rule, to give
conversion over equal boundaries for any judgement. *)
      set (gJ := Build_judgement Γ' (substitute_hypothetical_judgement g J)).
      assert (Closure.derivation T Hs gJ) as d_gJ.
      { simple refine (derive_subst_apply' J gJ _ (idpath _) d_g _).
        simple refine (Closure.hypothesis' _ _). { apply inl, None. }
        apply idpath.
      }
      destruct cl as [ | ].
      { (* type judgement: [g^* J] is [! Γ' |- g^*A !] exactly as required  *)
        refine (transport _ _ d_gJ).
        apply Judgement.eq_by_eta; apply idpath.
      }
      (* term judgement: presupposition is [! Γ' |- g^* A : f^* A !],
         while [g^*J] is [! Γ' |- g^* A : g^* A !],
         so need to apply [term_convert] rule. *)
      set (A := J (the_object_boundary_slot class_term the_type_slot)).
      set (a := J (the_head_slot class_term)).
      assert (Closure.derivation T Hs [! Γ |- A !]) as d_A.
      { simple refine (Closure.hypothesis' _ _).
        - apply inr. exists None. exact the_type_slot.
        - apply Judgement.eq_by_eta, idpath. }
      apply Judgement.canonicalise; simpl.
      simple refine (derive_term_convert _ _ _ _ _ _ _ _).
        (* TODO: improve the equality rule interfaces to work off the bat for arbitrary judgements of correct type, without canonicalising? *)
      { exact (substitute g A). }
      + (* [! Γ' |- g^* A !] *)
        refine (derive_subst_apply' [! Γ |- A !] [! _ |- _ !] g _ d_g d_A).
        apply eq_by_eta_hypothetical_judgement, idpath.
      + (* [! Γ' |- f^* A !] *)
        refine (derive_subst_apply' [! Γ |- A !] [! _ |- _ !] f _ d_f d_A).
        apply eq_by_eta_hypothetical_judgement, idpath.
      + (* [! Γ' |- g^* A = f^* A !] *)
        apply derive_tyeq_sym.
        simple refine
          (derive_subst_equal' [! _ |- _ !] [! _ |- _ ≡ _ !] f g _ _ _ d_A).
        * constructor.
        * apply eq_by_eta_hypothetical_judgement, idpath.
        * intros i.
          destruct (some_or_is_none (fg_triv i)) as [ fgi_triv | fgi_nontriv].
          { apply inl. exact fgi_triv. }
          apply inr.
          repeat split;
            simple refine (Closure.hypothesis' _ _);
            try apply inl, Some;
            try exists (i;fgi_nontriv);
            [ apply Some, Some, tt | | apply Some, None | | apply None | ];
            apply idpath.
      + refine (transport _ _ d_gJ).
        apply Judgement.eq_by_eta; apply idpath.
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

End StructuralRulePresups.
