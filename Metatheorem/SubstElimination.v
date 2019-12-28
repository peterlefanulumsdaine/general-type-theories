Require Import HoTT.
Require Import Syntax.ShapeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.StructuralRule.
Require Import Typing.FlatTypeTheory.

(** The main goal of this file is the theorem [subst_elimination], showing
that for suitable theories [T], any derivation over [T] using the full 
structural rules can be translated into a derivation not using the rules
[subst_apply], [subst_equal].

The main subsidiary lemmas are [subst_apply_admissible] and
[subst_equal_admissible], showing that (generalisations of) these rules are
admissible over the closure system given by [T] together with the other
structural rules. 

Note: at the moment, our “susbt-free” structural rules still include the
general renaming rule.  In fact the subst-free derivations we produce will
only require renaming along _equivalences_ of shapes. *)

(* TODO: perhaps restrict the renaming rule (either in general, or just
in [structural_rule_without_subst]) to just the case of equivalences,
so that the results of this file really do show that general renaming is
admissible. *)

Section Auxiliary.

  Context `{Funext} {σ : shape_system}.

  (* TODO: upstream *)
  Lemma instantiation_fmap2
      {Σ : signature σ}
      {a a' : arity σ} (f : Family.map a a')
      {γ} (I : Metavariable.instantiation a' Σ γ)
    : Metavariable.instantiation a Σ γ.
  Proof.
    intros i.
    unfold argument_class, argument_shape.
    refine (transport _ _ _). 
    { apply ap, ap, (Family.map_commutes f). }
    eapply (transport (fun cl => _ _ cl _)).
    { apply ap, (Family.map_commutes f). }
    apply I.
  Defined.

  (* TODO: upstream *)
  Lemma transport_class_instantiate
      {Σ : signature σ} {a}
      {γ} (I : Metavariable.instantiation a Σ γ)
      {cl cl'} (e_cl : cl = cl')
      {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
    : transport (fun cl => raw_expression _ cl _) e_cl
                (instantiate_expression I e)
      = instantiate_expression I
          (transport (fun cl => raw_expression _ cl _) e_cl e).
  Proof.
    destruct e_cl; apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma transport_shape_instantiate
      {Σ : signature σ} {a}
      {γ} (I : Metavariable.instantiation a Σ γ)
      {cl} {δ δ'} (e_δ : δ = δ')
      (e : raw_expression (Metavariable.extend Σ a) cl δ)
    : transport _ (ap _ e_δ) (instantiate_expression I e)
      = instantiate_expression I (transport _ e_δ e).
  Proof.
    destruct e_δ; apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma substitute_transport_shape
      {Σ : signature σ}
      {γ γ'} (e_γ : γ = γ') {δ}
      (f : raw_context_map Σ δ γ')
      {cl} (e : raw_expression Σ cl γ)
    : substitute f (transport (raw_expression _ _) e_γ e)
      = substitute (transport (raw_context_map _ _) e_γ^ f) e.
  Proof.
    destruct e_γ; apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma instantiate_fmap2
      {a a' : arity σ} (f : Family.map a a')
      {Σ} {γ} (I : Metavariable.instantiation a' Σ γ)
      {cl} {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
    : instantiate_expression I (Expression.fmap (Metavariable.fmap2 _ f) e)
    = instantiate_expression (instantiation_fmap2 f I) e.
  Proof.
    induction e as [δ i | δ [S | M] e_args IH_e_args ].
    - apply idpath. (* [raw_variable]: easy! *)
    - (* symbol of signature *)
      simpl. apply ap.
      apply path_forall; intros i.
      apply ap, IH_e_args.
    - (* metavariable symbol *)
      simpl.
      (* first, apply IH *)
      eapply concat.
      2: { eapply (ap_2back substitute).
        apply ap, path_forall; intros i.
        eapply (ap (rename _)), IH_e_args.
      }
      clear IH_e_args.
      (* from here, just transport lemmas *)
      eapply concat. { apply inverse, transport_class_instantiate. }
      simpl.
      eapply concat. { apply Substitution.transport_substitute. }
      unfold instantiation_fmap2.
      eapply concat. 2: { apply inverse, substitute_transport_shape. }
      refine (ap_2back substitute _ _ _ @ ap (substitute _) _).
      2: { refine (ap_1back _ _^ _).
           eapply concat. 2: { refine (ap_compose _ _ _). }
           apply idpath.
      }
      set (e_M := Family.map_commutes f M); clearbody e_M.
      unfold argument_shape, argument_class, symbol_arity in *; simpl in e_args.
      set (a_M := a M) in *.
      set (a_fM := a' (f M)) in *.
      simpl; fold a_fM a_M; clearbody a_M a_fM.
      destruct e_M.
      cbn; apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma instantiate_fmap2_hypothetical_judgement
      {a a' : arity σ} (f : Family.map a a')
      {Σ} {γ} (I : Metavariable.instantiation a' Σ γ)
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ a) δ)
    : instantiate_hypothetical_judgement I
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ f) J)
    = instantiate_hypothetical_judgement (instantiation_fmap2 f I) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply instantiate_fmap2.
  Defined.

  (* TODO: upstream; consider naming! *)
  Local Definition copair_instantiation
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ) 
    : Metavariable.instantiation (a+b) Σ γ.
  Proof.
    intros [i | j].
    - apply Ia.
    - apply Ib.
  Defined.

  (* TODO: upstream; consider naming! *)
  Local Definition copair_instantiation_inl
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ)
      {cl} {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
    : instantiate_expression
        (copair_instantiation Ia Ib)
        (Expression.fmap (Metavariable.fmap2 _ Family.inl) e)
      = instantiate_expression Ia e.
  Proof.
    apply instantiate_fmap2.
  Defined.

  (* TODO: upstream; consider naming! *)
  Local Definition copair_instantiation_inr
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ)
      {cl} {δ} (e : raw_expression (Metavariable.extend Σ b) cl δ)
    : instantiate_expression
        (copair_instantiation Ia Ib)
        (Expression.fmap (Metavariable.fmap2 _ Family.inr) e)
      = instantiate_expression Ib e.
  Proof.
    apply instantiate_fmap2.
  Defined.

  (* TODO: upstream; consider naming! *)
  Local Definition copair_instantiation_inl_hypothetical_judgement
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ) 
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ a) δ)
    : instantiate_hypothetical_judgement
        (copair_instantiation Ia Ib)
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ Family.inl) J)
      = instantiate_hypothetical_judgement Ia J.
  Proof.
    apply instantiate_fmap2_hypothetical_judgement.
  Defined.

  (* TODO: upstream; consider naming! *)
  Local Definition copair_instantiation_inr_hypothetical_judgement
      {Σ} {a b : arity σ} {γ}
      (Ia : Metavariable.instantiation a Σ γ) 
      (Ib : Metavariable.instantiation b Σ γ) 
      {δ} (J : hypothetical_judgement (Metavariable.extend Σ b) δ)
    : instantiate_hypothetical_judgement
        (copair_instantiation Ia Ib)
        (fmap_hypothetical_judgement (Metavariable.fmap2 _ Family.inr) J)
      = instantiate_hypothetical_judgement Ib J.
  Proof.
    apply instantiate_fmap2_hypothetical_judgement.
  Defined.

  (* TODO: upstream *)
  Lemma instantiate_combine_hypothetical_judgement
    {Σ : signature σ} {a} {γ} (Ia : Metavariable.instantiation a Σ γ)
    {δ} (K K' : hypothetical_judgement _ δ)
    (e : form_of_judgement K = form_of_judgement K')
    (K_obj : Judgement.is_object (form_of_judgement K))
    : instantiate_hypothetical_judgement Ia
                         (combine_hypothetical_judgement K K' e K_obj)
    = combine_hypothetical_judgement
        (instantiate_hypothetical_judgement Ia K)
        (instantiate_hypothetical_judgement Ia K')
        e K_obj.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros [s | | ];
      destruct K as [jf K], K' as [jf' K']; cbn in e, K_obj;
      destruct e, jf; destruct K_obj;
    (* we destruct enough that all the equalities appearing under transports in the goal become idpaths, and the transports compute. *)
      apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma rename_combine_hypothetical_judgement
    {Σ} {γ γ' : σ} (f : γ -> γ')
    (K K' : hypothetical_judgement Σ γ)
    (e : form_of_judgement K = form_of_judgement K')
    (K_obj : Judgement.is_object (form_of_judgement K))
    : rename_hypothetical_judgement f
                         (combine_hypothetical_judgement K K' e K_obj)
    = combine_hypothetical_judgement
        (rename_hypothetical_judgement f K)
        (rename_hypothetical_judgement f K')
        e K_obj.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros [s | | ];
      destruct K as [jf K], K' as [jf' K']; cbn in e, K_obj;
      destruct e, jf; destruct K_obj;
    (* we destruct enough that all the equalities appearing under transports in the goal become idpaths, and the transports compute. *)
      apply idpath.
  Defined.

End Auxiliary.

Section Subst_Free_Derivations.

  Context {σ : shape_system}.

  Definition closure_system_without_subst
      {Σ : signature σ} (T : flat_type_theory Σ)
  := structural_rule_without_subst Σ + Family.bind T FlatRule.closure_system.

  Definition subst_free_derivation
      {Σ : signature σ} (T : flat_type_theory Σ)
  := derivation (closure_system_without_subst T).

  Definition subst_free_rule_derivation {Σ : signature σ}
    (T : flat_type_theory Σ) (R : flat_rule Σ)
  := subst_free_derivation
      (FlatTypeTheory.fmap Metavariable.include_symbol T)
      (flat_rule_premise R)
      (flat_rule_conclusion R).

  (* TODO: we will probably need to generalise various lemmas from ordinary to
  subst-free derivations.  Hopefully this can be done, as far as possible, by
  proving the original lemmas in type-class based ways, which will then apply
  automatically to subst-free derivations. *)

End Subst_Free_Derivations.

Section Flat_Conditions.
(** Conditions on flat rules/type theories sufficient for admissibility of
substitution to hold over them.

  The main such condition is: every rule should have empty conclusion context.
To use one established terminology, all rules should be in _universal form_,
as opposed to _hypothetical form_. 

  For substitution to (admissibly) respect equality, we additionally need to
know that the theory is _congruous_, in that for each flat rule of object form,
the associated congruence rule should be derivable (?admissible). *)

  Context {σ} {Σ : signature σ}.

  Definition in_universal_form (R : flat_rule Σ)
    := is_empty (shape_of_judgement (flat_rule_conclusion R)).

  Definition substitutive (T : flat_type_theory Σ)
    := forall r : T, in_universal_form (T r).

  (* TODO: upstream to [FlatRule]? *)
  Definition flat_congruence_rule
      (R : flat_rule Σ)
      (R_obj : Judgement.is_object (form_of_judgement (flat_rule_conclusion R)))
    : flat_rule Σ.
  Proof.
    assert (inl : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inl. }
    assert (inr : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inr. }
    exists (flat_rule_metas R + flat_rule_metas R).
    - (* premises *)
      refine (_ + _ + _).
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inl.
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inr.
      + exists {p : flat_rule_premise R
                    & Judgement.is_object
                        (form_of_judgement (flat_rule_premise R p))}.
        intros [p p_obj].
        set (J := flat_rule_premise R p).
        fold J in p_obj.
        exists (Context.fmap inl (context_of_judgement J)).
        simple refine (combine_hypothetical_judgement _ _ _ _).
        * exact (fmap_hypothetical_judgement inl J).
        * exact (fmap_hypothetical_judgement inr J).
        * apply idpath.
        * apply p_obj.
    - (* conclusion *)
      set (J := flat_rule_conclusion R).
      exists (Context.fmap inl (context_of_judgement J)).
        simple refine (combine_hypothetical_judgement _ _ _ _).
        * exact (fmap_hypothetical_judgement inl J).
        * exact (fmap_hypothetical_judgement inr J).
        * apply idpath.
        * apply R_obj.
  Defined.

  Local Definition congruous (T : flat_type_theory Σ)
    : Type
  := Family.map
    (Family.bind T
       (fun R => {| family_element R_obj := flat_congruence_rule R R_obj |}))
    T.
  (** More readably: [T] is congruous if for each of its object rules, it also contains the associated congruence rule.

  This is not as general as would ideally be nice: ideally we would say something like “for each object rule, the associated congruence rule is _derivable_ over T”. Unfortunately, the obvious concise ways of saying that all seem to be wrong.  

  For isntance, our main sense of derivable says that the rule itself is derivable over the translation of T to the metavariable extension; this is bad for two reasons.  First, applying this notion relies on being able to instantiate derivations, which requires either the subst-apply rule or a subst-elimination principle, which will not yet be available at the point we need this.  Secondly, in examples, giving derivations with non-trivial hypotheses (as one does for a congruence rule with binders) may genuinely require use of the subst-apply and subst-eq structural rules. 

  An alternative would be to just say that the congruence rule should be _admissible_ over T, or that each instance of it should be derivable.  These would work for the present theorems, but are a bit unnatural; e.g. they’re not preserved under translation or extension of theories.

  The best notion is perhaps obtained by re-defining “derivable rule” to fit the subst-free setting.  For this, we say “the rule’s conclusion should be derivable in the metavariable extension” as before, but instead of saying “…over T, from the rule’s premises”, we convert the premises into extra rules; a premise like [ x:A |- B(x) type ] becomes a pair of rules
[ |- a:A // |- B(a) type ] and [ |- a = a' : A // |- B(a) = B(a') type ].

  With “derivable rule” thus re-defined, taking “congruous” to be “each associated congruence rule is derivable over T” should now work well: it should suffice for the theorems of this file, and be applicable to natural examples (i.e. theories set up using alternative resonable formulations of congruence rules). More generally, this seems to be the right notion of “derivable rule” in the subst-free setting, so would be good to have in general.

  However, it would take a lot of work to state this and set up the infrastructure to work with it.  So for now we stick with this simpler and cruder notion of congruousness: T should literally contain all its associated congruence rules. *)

  Local Definition derive_contained_rule
      {T : flat_type_theory Σ}
      {R} {r:T} (e : T r = R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {H} (d_prems : forall p : flat_rule_premise R,
             subst_free_derivation T H
                        (Judgement.instantiate Γ I (flat_rule_premise R p)))
    : subst_free_derivation T H
        (Judgement.instantiate Γ I (flat_rule_conclusion R)).
  Proof.
    destruct e.
    simple refine (Closure.deduce' _ _ _).
    { apply inr. exists r, Γ. exact I. }
    { apply idpath. }
    assumption.
  Defined.

  Local Definition derive_contained_rule'
      {T : flat_type_theory Σ}
      {R} {r:T} (e_R : T r = R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J} (e_J : J = Judgement.instantiate Γ I (flat_rule_conclusion R))
      {H} (d_prems : forall p : flat_rule_premise R,
             subst_free_derivation T H
                        (Judgement.instantiate Γ I (flat_rule_premise R p)))
    : subst_free_derivation T H J.
  Proof.
    destruct e_J^; eapply derive_contained_rule; eassumption.
  Defined.

  Local Definition derive_congruence {T} (T_cong : congruous T) {H}
    {r : T} (r_obj : Judgement.is_object (form_of_judgement (flat_rule_conclusion (T r))))
    (r_cong := flat_congruence_rule (T r) r_obj)
    {Γ : raw_context Σ}
    (I0 I1 : Metavariable.instantiation (flat_rule_metas (T r)) Σ Γ)
    (I := copair_instantiation I0 I1)
    (d_prems : forall p : flat_rule_premise r_cong,
        subst_free_derivation T H
          (Judgement.instantiate Γ I (flat_rule_premise r_cong p)))
    : subst_free_derivation T H
        (Judgement.instantiate Γ I (flat_rule_conclusion r_cong)).
  Proof.
    simple refine (derive_contained_rule _ _ _).
    { apply T_cong. exists r. exact r_obj. }
    { apply (Family.map_commutes T_cong). }
    assumption.
  Defined.

End Flat_Conditions.

Section Judgement_Renamings.
(** A lot of results can be concisely formulated in terms of maps/renamings of
judgements.  A map/renaming of judgements from [Γ' |- J'] to [Γ |- J] is just
a context map/renaming [f] from [Γ'] to [J], such that [J' = f^*J].

(Categorically, these are exactly maps in the total category of judgements,
viewed as a discrete fibration over contexts.)

This section gives judgement renamings; section [Weakly_Typed_Maps] below gives
the analogue for (weakly) typed context maps. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (* TODO: perhaps upstream judgement renamings to [Judgement.v], and use them
  more widely, e.g. in the renaming structural rules?? *)

  Record judgement_renaming (J J' : judgement Σ)
  := {
    typed_renaming_of_judgement_renaming
      :> typed_renaming (context_of_judgement J) (context_of_judgement J')
  ; judgement_renaming_hypothetical_part
      : rename_hypothetical_judgement
          typed_renaming_of_judgement_renaming 
          (hypothetical_part J)
        = hypothetical_part J'
  }.

  Lemma judgement_renaming_inverse
      (J J' : judgement Σ)
      (f : judgement_renaming J J')
      (e_f : IsEquiv f)
    : judgement_renaming J' J.
  Proof.
    exists (typed_renaming_inverse _ e_f).
    eapply concat.
    { apply ap, inverse, (judgement_renaming_hypothetical_part _ _ f). }
    eapply concat. { apply rename_rename_hypothetical_judgement. }
    eapply concat. 2: { apply rename_idmap_hypothetical_judgement. }
    apply (ap_1back rename_hypothetical_judgement), path_forall; intros i.
    apply eissect.
  Defined.

  Lemma instantiate_judgement_over_typed_renaming
      {Γ Γ' : raw_context Σ} (f : typed_renaming Γ Γ')
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : judgement_renaming
        (Judgement.instantiate Γ I J)
        (Judgement.instantiate Γ' (rename_instantiation f I) J).
  Proof.
    exists (instantiate_context_over_typed_renaming f I _).
    apply inverse, instantiate_hypothetical_judgement_rename_instantiation.
  Defined.

End Judgement_Renamings.

Section Rename_Derivations.
(** The goal of this section is [rename_derivation]:
given a judgement-renaming from [J] to [J'],
and a derivation [d] of [J],
we can rename throughout [d] to get a derivation of [J']. 

The proof of [rename_derivation] is by direct structural induction on
derivations; the rest of this section is devoted to the lemmas needed in
the cases of that induction. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Section Flat_Rule_Instantiation_Renaming.
    (** The lemmas of this section build up what’s needed for renaming
     flat-rule steps in derivations: 

     given an instance of a flat rule in universal form,
     and a judgement-renaming into its conclusion,
     get a renamed instance, whose conclusion is renaming-equivalent to the
     renaming we want to derive, and each of whose premises has a
     judgement-renaming to some premise of the original rule.

     The cases for non-flat structural rules are done by analogous
     claim for their closure conditions.
    *)

    (* TODO: consider naming of the whole following lemma sequence *)

    Context {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J' : judgement Σ}
      (f : judgement_renaming
             (Judgement.instantiate Γ I (flat_rule_conclusion R))
             J')
      (Γ' := context_of_judgement J').

    Local Definition rename_flat_rule_instantiation_renaming
      : typed_renaming Γ Γ'.
    Proof.
      refine (compose_typed_renaming f _).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition rename_flat_rule_instantiation_instantiation
      : Metavariable.instantiation (flat_rule_metas R) Σ Γ'.
    Proof.
      exact (rename_instantiation
               rename_flat_rule_instantiation_renaming
               I).
    Defined.

    Local Lemma rename_flat_rule_instantiation_conclusion
      : judgement_renaming
          (Judgement.instantiate Γ'
            (rename_flat_rule_instantiation_instantiation)
            (flat_rule_conclusion R))
          J'.
    (* NOTE: and moreover this judgement_renaming is an equivalence, which may
    be needed if we restrict the renaming structural rule to equivalences. *)
    Proof.
      simple refine (judgement_renaming_inverse _ _ _ _).
      1: exists (typed_renaming_to_instantiate_context _ _ _).
      2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
      eapply concat. 2: { apply inverse,
                      instantiate_hypothetical_judgement_rename_instantiation. }
      eapply concat.
        { apply ap, inverse, (judgement_renaming_hypothetical_part _ _ f). }
      eapply concat. { apply rename_rename_hypothetical_judgement. }
      apply (ap_1back rename_hypothetical_judgement), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      2: { refine (empty_rect _ _ _). apply R_univ. }
      intros x1.
      unfold Coproduct.fmap. repeat rewrite coproduct_comp_inj1.
      apply idpath.
      (* This can be seen more conceptually as a sort of naturality calculation, 
       involving naturality of [typed_renaming_to_instantiate_context] w.r.t.
       [instantiate_context_over_typed_renaming]. *)
    Defined.

    Local Lemma rename_flat_rule_instantiation_premise
          (p : flat_rule_premise R)
      : judgement_renaming
          (Judgement.instantiate Γ I (flat_rule_premise R p))
          (Judgement.instantiate Γ' rename_flat_rule_instantiation_instantiation
                                                       (flat_rule_premise R p)).
    Proof.
      apply instantiate_judgement_over_typed_renaming.
    Defined.

  End Flat_Rule_Instantiation_Renaming.

  Lemma equality_flat_rules_in_universal_form
    : forall r : @equality_flat_rule σ,
      in_universal_form (equality_flat_rule r).
  Proof.
    intro r; recursive_destruct r; apply shape_is_empty.
  Defined.

  Definition rename_derivation
      {T : flat_type_theory Σ} (T_sub : substitutive T) 
      {J} {J'} (f : judgement_renaming J J')
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    revert J' f.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' f.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (rename_flat_rule_instantiation_conclusion _ _ f) 
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inr. exists r.
        exists (context_of_judgement J').
        refine (rename_flat_rule_instantiation_instantiation _ f). 
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ f p).
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (rename_flat_rule_instantiation_conclusion _ _ f) 
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inr. exists r.
        exists (context_of_judgement J').
        refine (rename_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ f p).
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_typed_renaming f g).
      eapply concat. 2: { apply (judgement_renaming_hypothetical_part _ _ f). }
      apply inverse, @rename_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in f.
      destruct J' as [Γ' J']. 
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inl, inr.
        exists Γ'. exact (f i). }
      { cbn. apply (ap (Build_judgement _)). 
        set (e := judgement_renaming_hypothetical_part _ _ f).
        eapply concat. 2: { apply e. }
        apply (ap (Build_hypothetical_judgement _)). 
        apply path_forall.
        intros s; recursive_destruct s; try apply idpath.
        apply typed_renaming_respects_types.        
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := typed_renaming_of_judgement_renaming _ _ f).
      cbn in f0. exists f0.
      apply (ap (Build_hypothetical_judgement _)). 
      apply path_forall.
      intros s; recursive_destruct s.
      apply inverse, typed_renaming_respects_types.
  Defined.

End Rename_Derivations.

Section Weakly_Typed_Maps.
(** For [sustitute_derivation], we introduce an auxiliary notion of _weakly
typed_ context maps: maps which at each component look either like a well-typed
context map, or like a typed renaming.

This slightly subtle definition is essentially motivated by the proof
of [substitute_derivation], and in particular, the desire to keep that proof
structurally recursive on the derivation (and also not dependent on any kind
of well-typedness conditions on the flat rules).  The point is that when
passing under binders in premises of rules, we want to extend the context map
by the type-expressions of the binders, without having to check that these are
well-formed. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Local Definition weakly_typed 
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ) (f : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j) * (Δ j = substitute f (Γ i)) }
    + subst_free_derivation T (Family.empty _)
                            [! Δ |- f i ; substitute f (Γ i) !].

  Local Record weakly_typed_context_map
    (T : flat_type_theory Σ) (Δ Γ : raw_context Σ)
  := {
    raw_of_weakly_typed_context_map :> raw_context_map Σ Δ Γ
  ; weakly_typed_context_map_is_weakly_typed
                    : weakly_typed T Δ Γ raw_of_weakly_typed_context_map
  }.

  Local Lemma compose_weakly_typed_context_map_renaming
        {T : flat_type_theory Σ} (T_sub : substitutive T)
        {Γ Γ' Γ'' : raw_context Σ}
        (g : weakly_typed_context_map T Γ' Γ)
        (f : typed_renaming Γ' Γ'')
    : weakly_typed_context_map T Γ'' Γ.
  Proof.
    simple refine (Build_weakly_typed_context_map _ _ _ _ _).
    - intros i. exact (Expression.rename f (g i)).
    - intros i.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ g i)
        as [[j [e1 e2]] | d_gi].
      + apply inl.
        exists (f j); split.
        * exact (ap (rename f) e1).
        * eapply concat. { apply typed_renaming_respects_types. }
          eapply concat. { apply ap, e2. }
          apply rename_substitute.
      + apply inr.
        refine (rename_derivation _ _ d_gi).
        { assumption. }
        exists f.
        apply (ap (Build_hypothetical_judgement _)).
        (* TODO: abstract the above as [hypothetical_judgement_eq_by_expressions?
           It’s used so often. *)
        apply path_forall.
        intros j; recursive_destruct j.
        * apply rename_substitute.
        * apply idpath.
  Defined.

  Local Lemma compose_renaming_weakly_typed_context_map
        {T : flat_type_theory Σ}
        {Γ Γ' Γ'' : raw_context Σ}
        (g : typed_renaming Γ Γ')
        (f : weakly_typed_context_map T Γ'' Γ')
    : weakly_typed_context_map T Γ'' Γ.
  Proof.
    simple refine (Build_weakly_typed_context_map _ _ _ _ _).
    - intros i. exact (f (g i)).
    - intros i.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f (g i))
        as [[j [e1 e2]] | d_gi].
      + apply inl.
        exists j; split.
        * exact e1.
        * eapply concat. { exact e2. }
          eapply concat. { apply ap, typed_renaming_respects_types. }
          apply substitute_rename.
      + apply inr.
        refine (transport _ _ d_gi).
        apply (ap (fun A => [! _ |- _ ; A !])).
        eapply concat. { apply ap, typed_renaming_respects_types. }
        apply substitute_rename.
  Defined.

  (* TODO: possible alternate names:
     [instantiate_context_substitute_instantiation],
     [extend_weakly_typed_context_map] *)
  Lemma instantiate_context_over_weakly_typed_context_map
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (f : weakly_typed_context_map T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_typed_context_map T
        (Context.instantiate Γ' (substitute_instantiation f I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    exists (Substitution.extend Γ Γ' Δ f).
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
          as [[j [e1 e2]] | d_fi].
      + apply inl.
        exists (coproduct_inj1 shape_is_sum j); split.
        * exact (ap _ e1).
        * rewrite coproduct_comp_inj1.
          eapply concat. { apply ap, e2. }
          eapply concat. { apply rename_substitute. }
          eapply concat. 2: { apply inverse, substitute_rename. }
          apply (ap_2back substitute), path_forall; intros k.
          apply inverse. refine (coproduct_comp_inj1 _).
      + apply inr.
        refine (rename_derivation _ _ d_fi).
        { assumption. }
        exists (typed_renaming_to_instantiate_context _ _ _).
        apply (ap (Build_hypothetical_judgement _)).
        apply path_forall; intros j; recursive_destruct j.
        * eapply concat. { apply rename_substitute. }
          eapply concat. 2: { apply inverse, substitute_rename. }
          apply (ap_2back substitute), path_forall; intros j.
          apply inverse. refine (coproduct_comp_inj1 _).
        * apply idpath.
    - intros i. apply inl.
      exists (coproduct_inj2 shape_is_sum i); split.
      + unfold Substitution.extend; cbn.
        refine (coproduct_comp_inj2 _).
      + cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  (** Analogous to [judgement_renaming] *)
  Local Record weakly_typed_judgement_map
    (T : flat_type_theory Σ) (J' J : judgement Σ)
  := {
    weakly_typed_context_map_of_judgement_map
      :> weakly_typed_context_map T
           (context_of_judgement J') (context_of_judgement J)
  ; weakly_typed_judgement_map_hypothetical_part
      : substitute_hypothetical_judgement
          weakly_typed_context_map_of_judgement_map
          (hypothetical_part J)
        = hypothetical_part J'
  }.

  Local Lemma instantiate_judgement_over_weakly_typed_context_map
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (f : weakly_typed_context_map T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_typed_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation f I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_typed_context_map T_sub f I _).
    apply inverse, instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

End Weakly_Typed_Maps.

Section Substitute_Derivations.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Section Flat_Rule_Substitute_Instantiation.
    (** Analogously to section [Flat_Rule_Susbtitute_Renaming],
     the lemmas of this section build up what’s needed for substituting
     flat-rule steps in derivations: 

     given an instance of a flat rule in universal form,
     and a weakly-typed judgement map into its conclusion,
     get a sustituted instance, whose conclusion is renaming-equivalent to the
     renaming we want to derive, and each of whose premises has a
     weakly-typed judgement map to some premise of the original rule.

     The cases for non-flat structural rules should be done by analogous
     claim for their closure conditions.
    *)

    (* TODO: consider naming of the whole following lemma sequence 
     (but keep consistent with renaming versions above). *)

    Context
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J' : judgement Σ}
      (f : weakly_typed_judgement_map T
             J'
             (Judgement.instantiate Γ I (flat_rule_conclusion R)))
      (Γ' := context_of_judgement J').

    Local Definition substitute_flat_rule_instantiation_map
      : weakly_typed_context_map T Γ' Γ.
    Proof.
      refine (compose_renaming_weakly_typed_context_map _ f).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition substitute_flat_rule_instantiation_instantiation
      : Metavariable.instantiation (flat_rule_metas R) Σ Γ'.
    Proof.
      exact (substitute_instantiation
               substitute_flat_rule_instantiation_map
               I).
    Defined.

    Local Lemma substitute_flat_rule_instantiation_conclusion
      : judgement_renaming
          (Judgement.instantiate Γ'
            (substitute_flat_rule_instantiation_instantiation)
            (flat_rule_conclusion R))
          J'.
    (* NOTE: and moreover this judgement_renaming is an equivalence, which may
    be needed if we restrict the renaming structural rule to equivalences. *)
    Proof.
      simple refine (judgement_renaming_inverse _ _ _ _).
      1: exists (typed_renaming_to_instantiate_context _ _ _).
      2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
      (* The following can again be seen as a naturality calculation, 
       involving naturality of [typed_renaming_to_instantiate_context] w.r.t.
       weakly typed context maps. *)
      eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
      eapply concat.
        { apply ap, inverse, (weakly_typed_judgement_map_hypothetical_part _ _ _ f). }
      eapply concat. { apply rename_substitute_hypothetical_judgement. }
      apply (ap_1back substitute_hypothetical_judgement), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      2: { refine (empty_rect _ _ _). apply R_univ. }
      intros x1.
      unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
      apply idpath.
    Defined.

    Local Lemma substitute_flat_rule_instantiation_premise
          (p : flat_rule_premise R)
      : weakly_typed_judgement_map T
          (Judgement.instantiate Γ'
                  substitute_flat_rule_instantiation_instantiation
                  (flat_rule_premise R p))
          (Judgement.instantiate Γ I (flat_rule_premise R p)).
    Proof.
      apply instantiate_judgement_over_weakly_typed_context_map.
      assumption.
    Defined.

  End Flat_Rule_Substitute_Instantiation.

  Definition substitute_derivation
      {T : flat_type_theory Σ} (T_sub : substitutive T) 
      {J} {J'} (f : weakly_typed_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    revert J' f.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' f.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substitute_flat_rule_instantiation_conclusion _ _ f) 
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
      assumption.
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substitute_flat_rule_instantiation_conclusion _ _ f) 
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
      assumption.
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_renaming_weakly_typed_context_map g f).
      eapply concat.
        2: { apply (weakly_typed_judgement_map_hypothetical_part _ _ _ f). }
      apply inverse, @substitute_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in f.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
        as [[j [e1 e2]] | d_fi].
      (* TODO: add implicit args in […is_weakly_typed]!  It’s bloody long enough already *)
      + (* case: [f i = raw_variable j], [Γ' j = f^* (Γ i) ] *)
      destruct J' as [Γ' J'].
      destruct f as [f fJ'].
      cbn in j, e1, e2 |- *.
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inl, inr. (* use the variable rule *)
        exists Γ'. exact j. }
      { cbn in fJ'; destruct fJ'.
        apply Judgement.eq_by_expressions.
        - intro; apply idpath.
        - intro s; recursive_destruct s.
          + exact e2.
          + cbn. apply inverse, e1.
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := f : weakly_typed_context_map _ _ _).
      cbn in f0. exists f0.
      apply (ap (Build_hypothetical_judgement _)). 
      apply path_forall.
      intros s; recursive_destruct s.
      apply inverse, e2.
      + (* case: [f] tells us [ Γ' |- f i : f^* (Γ i) ] *)
        refine (transport _ _ d_fi).
        destruct J' as [Γ' J'].
        destruct f as [f fJ'].
        cbn in fJ' |- *; destruct fJ'.
        apply Judgement.eq_by_eta; exact idpath.
  Defined.

  (** Note: both [rename_derivation] and [sustitute_derivation] have analogues for derivations with hypotheses.  However, these are rather less clear to state, so for now we give just the versions for closed derivations.  *)
End Substitute_Derivations.

Section Equality_Substitution.
(** Goal of this section: showing that (generalisations of) the [subst_equal] structural rules are admissible.

That is: given a derivale object judgement, e.g. [ Γ |- a : A ], and two derivably judgementally equal context morphisms [ f, g : Γ' -> Γ ], we should be able to derive [ Γ |- f^*a = g^*a : f^* A ].

That result, [subst_equal_derivation], is the main goal of this section; but to make the inductive proof go through we generalise its statement, to raw context maps [f g : Γ' -> Γ] that are what we call _weakly judgementally-equal_.

The idea of this is that it generalises judgemental equality so as to be closed under extending/weakening a pair [f, g] by types either of the form [f^*A] or [g^*A], without any derivability check for [A] (which would be required for the extensions to be still judgementally equal).  Such extensions arise when going under binders in premises of rules.

Since the resulting maps may not be weakly-typed context maps, so not automatically applicable for [substitute_derivation], we also strengthen the statement to conclude additionally that [ Γ |- f^*a : f^*A ] and [ Γ |- g^*a : g^*A ]. *)

  Context {σ : shape_system} {Σ : signature σ} `{Funext}.

  Local Definition weakly_equal
      (T : flat_type_theory Σ)
      {Δ Γ : raw_context Σ}
      (f g : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j) 
                * ((Δ j = substitute f (Γ i))
                  + (Δ j = substitute g (Γ i))) }
    + subst_free_derivation T (Family.empty _)
          [! Δ |- f i ≡ g i ; substitute f (Γ i) !].

  Local Record weakly_equal_pair
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ)
  := {
    left : raw_context_map Σ Δ Γ
  ; right : raw_context_map Σ Δ Γ
  ; is_weakly_equal : weakly_equal T left right
  }.

  Arguments Build_weakly_equal_pair {_ _ _} _ _ _.
  Arguments left {_ _ _} _.
  Arguments right {_ _ _} _.
  Arguments is_weakly_equal {_ _ _} _.

  Local Definition compose_renaming_weakly_equal_pair
        {T : flat_type_theory Σ}
        {Γ Γ' Γ'' : raw_context Σ}
        (r : typed_renaming Γ Γ')
        (fg : weakly_equal_pair T Γ'' Γ')
    : weakly_equal_pair T Γ'' Γ.
  Proof.
    set (f := left fg); set (g := right fg).
    simple refine (Build_weakly_equal_pair _ _ _).
    - intros i. exact (f (r i)).
    - intros i. exact (g (r i)).
    - intros i.
      destruct (is_weakly_equal fg (r i))
        as [[j [e1 e2]] | d_fri_gri ].
      + apply inl.
        exists j; split.
        * exact e1.
        * destruct e2 as [e2|e2] ; [apply inl | apply inr];
            refine (e2 @ _);
            refine (ap _ _ @ _);
            try apply typed_renaming_respects_types;
            apply substitute_rename.
      + apply inr.
        refine (transport _ _ d_fri_gri).
        apply (ap (fun A => [! _ |- _ ≡ _ ; A !])).
        eapply concat. { apply ap, typed_renaming_respects_types. }
        apply substitute_rename.
  Defined.

  (** Given a judgement [ Γ |- J ], and a weakly equal pair [ f, g : Γ' -> Γ ],
   a derivation of [ Γ |- J ] yields derivations of two or possibly three
   judgements over [Γ']:
   - [f^* J];
   - [g^* J];
   - if [J] is an object judgement, the associated equality judgement [f^* J = g^* J]

   The proof of this has to treat all three together, since they are each
   defined mutually with the others.

   We thus wrap them up together in the notion of “weakly equal judgement map”:
   a weakly equal map [ [Γ'|-J'] -> [Γ|-J] ] is a weakly equal pair [f,g] from
   [Γ'] to [Γ], such that [J'] is one of the judgements listed above as induced
   from [J] by the [f, g].

   This then allows the theorem [substitute_equal_derivation] to be stated as:
   given a derivation of [ Γ |- J ] and a weakly equal judgement map
   [ [Γ'|-J'] -> [Γ|-J] ], get a derivation of [ Γ' |- J' ].
*)
  Local Record weakly_equal_judgement_map
    (T : flat_type_theory Σ) (J' J : judgement Σ)
   := { 
     weakly_equal_pair_of_judgement_map
       :> weakly_equal_pair T (context_of_judgement J') (context_of_judgement J)
   ; weakly_equal_judgement_map_hypothetical_part
     : (hypothetical_part J'
         = substitute_hypothetical_judgement
           (left weakly_equal_pair_of_judgement_map)
           (hypothetical_part J))
     + (hypothetical_part J'
         = substitute_hypothetical_judgement
           (right weakly_equal_pair_of_judgement_map)
           (hypothetical_part J))
     + { J_obj : Judgement.is_object (form_of_judgement J)
       & hypothetical_part J'
         = substitute_equal_hypothetical_judgement
           (left weakly_equal_pair_of_judgement_map)
           (right weakly_equal_pair_of_judgement_map)
           (hypothetical_part J)
           J_obj }
     }.

  (** The following two lemmas are definitions are key for the application of weakly equal pairs:
  given a weakly equal pair [(f,g) : Γ' —> Γ], and a context extension [Δ] of [Γ],
  we can extend (f,g) to weakly equal pairs [Γ'.f^*Δ —> Γ.Δ] and [Γ'.g^*Δ —> Γ.Δ]. *)
  Lemma instantiate_context_over_weakly_equal_pair_left
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_equal_pair T
        (Context.instantiate Γ' (substitute_instantiation (left fg) I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    simple refine
      (Build_weakly_equal_pair _ _ _).
    { exact (Substitution.extend Γ Γ' Δ (left fg)). }
    { exact (Substitution.extend Γ Γ' Δ (right fg)). }
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (is_weakly_equal fg i)
          as [[j [e_ij e_fg]] | d_fi].
      + apply inl.
        exists (coproduct_inj1 shape_is_sum j); split.
        * exact (ap _ e_ij).
        * repeat rewrite coproduct_comp_inj1.
          repeat rewrite substitute_rename.
          destruct e_fg as [e | e];
            [ apply inl | apply inr ]; rewrite e;
            repeat rewrite rename_substitute;
            apply (ap_2back substitute), path_forall; intros x;
            cbn; repeat rewrite coproduct_comp_inj1;
            apply idpath.
      + apply inr.
        refine (rename_derivation _ _ d_fi).
        { assumption. }
        exists (typed_renaming_to_instantiate_context _ _ _).
        apply (ap (Build_hypothetical_judgement _)).
        apply path_forall; intros j; recursive_destruct j;
          try apply idpath.
        eapply concat. { apply rename_substitute. }
        eapply concat. 2: { apply inverse, substitute_rename. }
        apply (ap_2back substitute), path_forall; intros j.
        apply inverse. refine (coproduct_comp_inj1 _).
    - intros i. apply inl.
      exists (coproduct_inj2 shape_is_sum i); split.
      + unfold Substitution.extend; cbn.
        refine (coproduct_comp_inj2 _).
      + apply inl; cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  Lemma instantiate_context_over_weakly_equal_pair_right
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_equal_pair T
        (Context.instantiate Γ' (substitute_instantiation (right fg) I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    simple refine
      (Build_weakly_equal_pair _ _ _).
    { exact (Substitution.extend Γ Γ' Δ (left fg)). }
    { exact (Substitution.extend Γ Γ' Δ (right fg)). }
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (is_weakly_equal fg i)
          as [[j [e_ij e_fg]] | d_fi].
      + apply inl.
        exists (coproduct_inj1 shape_is_sum j); split.
        * exact (ap _ e_ij).
        * repeat rewrite coproduct_comp_inj1.
          repeat rewrite substitute_rename.
          destruct e_fg as [e | e];
            [ apply inl | apply inr ]; rewrite e;
            repeat rewrite rename_substitute;
            apply (ap_2back substitute), path_forall; intros x;
            cbn; repeat rewrite coproduct_comp_inj1;
            apply idpath.
      + apply inr.
        refine (rename_derivation _ _ d_fi).
        { assumption. }
        exists (typed_renaming_to_instantiate_context _ _ _).
        apply (ap (Build_hypothetical_judgement _)).
        apply path_forall; intros j; recursive_destruct j;
          try apply idpath.
        eapply concat. { apply rename_substitute. }
        eapply concat. 2: { apply inverse, substitute_rename. }
        apply (ap_2back substitute), path_forall; intros j.
        apply inverse. refine (coproduct_comp_inj1 _).
    - intros i. apply inl.
      exists (coproduct_inj2 shape_is_sum i); split.
      + unfold Substitution.extend; cbn.
        refine (coproduct_comp_inj2 _).
      + apply inr; cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  Local Lemma instantiate_judgement_over_weakly_equal_pair_left
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_equal_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation (left fg) I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_equal_pair_left T_sub fg I _).
    apply inl, inl,
      instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

  Local Lemma instantiate_judgement_over_weakly_equal_pair_right
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_equal_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation (right fg) I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_equal_pair_right T_sub fg I _).
    apply inl, inr,
      instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

  Section Flat_Rule_Substitute_Equal_Instantiation.
    (** Analogously to section [Flat_Rule_Susbtitute_Instantiation],
     the lemmas of this section build up what’s needed for substituting
     flat-rule steps in derivations along weakly equal pairs:

    - given a weakly equal judgement map (f,g) from J' into the conclusion of a flat rule instance I_* R, we get two or three new instantiations: two pulled back instantiations f^*I, g^*I for R, and if R was an object rule, an instantiation (f,g)^*I of the congruence rule of R;

    - the three possible things that J can be are precisely, up to equiv-renaming, the conclusions of these three new rule instances;

    - all of the premises of these new rule instances have weakly equal judgement maps to the premises of the original instance of R.

     The cases for non-flat structural rules amount to showing analogous things for their closure conditions. *)

    Context
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      (J := Judgement.instantiate Γ I (flat_rule_conclusion R))
      {J' : judgement Σ}
      (Γ' := context_of_judgement J')
      (is_obj_R
        := Judgement.is_object (form_of_judgement (flat_rule_conclusion R))).
  (* We can’t include [fg : weakly_equal_judgement_map T J' J] as a section variable here, since the lemmas below need to be able to destruct it and act on the result. *)

  (* Since these lemmas are for internal use only, and their names are getting
  very long, we for once relax our prohibition on abbreviations *)
    Local Definition substeq_flat_rule_pair
        (fg : weakly_equal_judgement_map T J' J)
      : weakly_equal_pair T Γ' Γ.
    Proof.
      simple refine (compose_renaming_weakly_equal_pair _ fg).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition substeq_flat_rule_rule
        (fg : weakly_equal_judgement_map T J' J)
      : flat_rule Σ.
    Proof.
      destruct fg as [_ [ _ | [ R_obj _]]].
      - exact R.
      - eapply flat_congruence_rule, R_obj.
    Defined.

    Local Definition substeq_flat_rule_instantiation
        (fg : weakly_equal_judgement_map T J' J)
      : Metavariable.instantiation
          (flat_rule_metas (substeq_flat_rule_rule fg)) Σ Γ'.
    Proof.
      set (f' := left (substeq_flat_rule_pair fg)).
      set (g' := right (substeq_flat_rule_pair fg)).
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj ?]]].
      - exact (substitute_instantiation f' I).
      - exact (substitute_instantiation g' I).
      - apply copair_instantiation.
        + exact (substitute_instantiation f' I).
        + exact (substitute_instantiation g' I).
    Defined.

    Local Lemma substeq_flat_rule_conclusion
        (fg : weakly_equal_judgement_map T J' J)
      : judgement_renaming
          (Judgement.instantiate Γ'
            (substeq_flat_rule_instantiation fg)
            (flat_rule_conclusion (substeq_flat_rule_rule fg)))
          J'.
    (* NOTE: and the renaming is in each case an equivalence, though we don’t
       currently need that. *)
    Proof.
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj e_J'_fgJ]]].
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_fJ. }
        eapply concat. { apply rename_substitute_hypothetical_judgement. }
        eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
        apply (ap_1back substitute_hypothetical_judgement), path_forall.
        refine (coproduct_rect shape_is_sum _ _ _).
        2: { refine (empty_rect _ _ _). apply R_univ. }
        intros x1.
        unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
        apply idpath.
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_gJ. }
        eapply concat. { apply rename_substitute_hypothetical_judgement. }
        eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
        apply (ap_1back substitute_hypothetical_judgement), path_forall.
        refine (coproduct_rect shape_is_sum _ _ _).
        2: { refine (empty_rect _ _ _). apply R_univ. }
        intros x1.
        unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
        apply idpath.
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_fgJ. }
        simpl substeq_flat_rule_instantiation.
        simpl substeq_flat_rule_rule.
        simpl hypothetical_part.
        rewrite instantiate_combine_hypothetical_judgement.
        rewrite rename_combine_hypothetical_judgement.
        refine (ap2 (fun J K
                       => combine_hypothetical_judgement
                            (Build_hypothetical_judgement _ J)
                            (Build_hypothetical_judgement _ K)
                            _ _)
                  _ _).
        + cbn. apply path_forall; intros i.
          eapply concat. 2: { apply inverse, copair_instantiation_inl. }
          eapply concat.
          2: { apply inverse, instantiate_substitute_instantiation. }
          eapply concat. { apply rename_substitute. }
          apply (ap_2back substitute); clear i.
          apply path_forall.
          refine (coproduct_rect shape_is_sum _ _ _).
          2: { apply (empty_rect _ R_univ). }
          intros i. unfold Substitution.extend.
          apply inverse. refine (coproduct_comp_inj1 _).
        + cbn. apply path_forall; intros i.
          eapply concat. 2: { apply inverse, copair_instantiation_inr. }
          eapply concat.
          2: { apply inverse, instantiate_substitute_instantiation. }
          eapply concat. { apply rename_substitute. }
          apply (ap_2back substitute); clear i.
          apply path_forall.
          refine (coproduct_rect shape_is_sum _ _ _).
          2: { apply (empty_rect _ R_univ). }
          intros i. unfold Substitution.extend.
          apply inverse. refine (coproduct_comp_inj1 _).
    Defined.

    Local Lemma substeq_flat_rule_premise
        (fg : weakly_equal_judgement_map T J' J)
        (p : flat_rule_premise (substeq_flat_rule_rule fg))
      : flat_rule_premise R.
    (* for each premise of the new rule used,
       select a premise of the original rule
       to which the new premise will admit a weakly-equal judgement map *) 
    Proof.
      destruct fg as [fg [ [ ? | ? ] | [ ? ?]]];
        try (exact p).
      destruct p as [ [ p | p ] | [p _] ];
        exact p.
    Defined.

    Local Lemma substeq_flat_rule_premise_map
        (fg : weakly_equal_judgement_map T J' J)
        (p : flat_rule_premise (substeq_flat_rule_rule fg))
      : weakly_equal_judgement_map T
          (Judgement.instantiate Γ'
                  (substeq_flat_rule_instantiation fg)
                  (flat_rule_premise _ p))
          (Judgement.instantiate Γ I
            (flat_rule_premise _ (substeq_flat_rule_premise _ p))).
    Proof.
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj e_jf]]].
      - (* case: f^* of original rule *)
        apply instantiate_judgement_over_weakly_equal_pair_left.
        assumption.
      - (* case: g^* of original rule *)
        apply instantiate_judgement_over_weakly_equal_pair_right.
        assumption.
      - (* case: congruence rule *)
        simpl in p|- *. clear e_jf.
        admit.
    (* TODO: [instantiate_judgement_over_weakly_equal_pair_combined], 
     giving this case analogously to the cases above. *)
    Admitted. (* TODO: [substeq_flat_rule_premise_pair], hopefully reasonably straightforward. *) 

  End Flat_Rule_Substitute_Equal_Instantiation.

  
  Theorem substitute_equal_derivation
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} {J'} (fg : weakly_equal_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    (* Sketch proof: should be roughly analogous in organisation to proofs of [rename_derivation], [substitute_derivation] above. 

  The sequence of lemmas to handle the flat rule cases should show:

  - given a weakly equal judgement map (f,g) from J' into the conclusion of a flat rule instance I_* R, we get two or three new instantiations: two pulled back instantiations f^*I, g^*I for R, and if R was an object rule, an instantiation (f,g)^*I of the congruence rule of R;

  - the three possible things that J can be are precisely, up to equiv-renaming, the conclusions of these three new rule instances;

  - all of the premises of these new rule instances have weakly equal judgement maps to the premises of the original instance of R.
   *)
    revert J' fg.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' fg.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substeq_flat_rule_conclusion _ _ fg) 
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (derive_contained_rule _ _ _).
      { destruct fg as [_ [_ | [r_obj _]]].
        - exact r.
        - apply T_cong. exists r. assumption.
      }
      { destruct fg as [fg [? | [r_obj ?]]]; simpl.
        - apply idpath.
        - apply (Family.map_commutes T_cong).
      }
      intros p. apply (IH (substeq_flat_rule_premise _ _ p)).
      refine (substeq_flat_rule_premise_map _ _ _ _ _ p); try assumption.
      apply T_sub.
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substeq_flat_rule_conclusion _ _ fg) 
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      rename fg into fg_temp; set (fg := fg_temp).
      destruct fg_temp as [fg_map [J'_fg | [r_obj J'_fg]]].
      - simple refine (Closure.deduce' _ _ _).
        { apply inl, inr. exists r.
          exists (context_of_judgement J').
          refine (substeq_flat_rule_instantiation _ fg).
        }
        { apply idpath. }
        intros p. apply (IH (substeq_flat_rule_premise _ fg p)).
        refine (substeq_flat_rule_premise_map _ _ _ _ fg p); try assumption.
        apply equality_flat_rules_in_universal_form.
      - admit. (* TODO: lemma that for each equality flat rule, if in object form, each instance of its congruence rule is subst-free derivable. (There’s only one case.) With that done, repeat the bullet above using [Closure.graft']. *)
    }
    - (* case: renaming rule *)
      admit.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in fg.
      admit.
(* From proof of [substitute_derivation], for cannibalising:
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_renaming_weakly_typed_context_map g f).
      eapply concat.
        2: { apply (weakly_typed_judgement_map_hypothetical_part _ _ _ f). }
      apply inverse, @substitute_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in f.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
        as [[j [e1 e2]] | d_fi].
      (* TODO: add implicit args in […is_weakly_typed]!  It’s bloody long enough already *)
      + (* case: [f i = raw_variable j], [Γ' j = f^* (Γ i) ] *)
      destruct J' as [Γ' J'].
      destruct f as [f fJ'].
      cbn in j, e1, e2 |- *.
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inl, inr. (* use the variable rule *)
        exists Γ'. exact j. }
      { cbn in fJ'; destruct fJ'.
        apply Judgement.eq_by_expressions.
        - intro; apply idpath.
        - intro s; recursive_destruct s.
          + exact e2.
          + cbn. apply inverse, e1.
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := f : weakly_typed_context_map _ _ _).
      cbn in f0. exists f0.
      apply (ap (Build_hypothetical_judgement _)). 
      apply path_forall.
      intros s; recursive_destruct s.
      apply inverse, e2.
      + (* case: [f] tells us [ Γ' |- f i : f^* (Γ i) ] *)
        refine (transport _ _ d_fi).
        destruct J' as [Γ' J'].
        destruct f as [f fJ'].
        cbn in fJ' |- *; destruct fJ'.
        apply Judgement.eq_by_eta; exact idpath.
*)
  Admitted. (* [substitute_equal_derivation]: substantial amount of work to do. *)

End Equality_Substitution.

Section Subst_Elimination.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Theorem subst_elimination
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} (d : FlatTypeTheory.derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J.
  Proof.
    induction d as [ [] | r _ d_prems ].
    (* no hypothesis; derivation must conclude with a rule *)
    destruct r as [ [ r_substfree | [ r_subst | r_substeq ] ] | r_from_t ].
    - simple refine (Closure.deduce' _ _ _).
      + exact (inl r_substfree).
      + apply idpath.
      + apply d_prems.
    - destruct r_subst as [Γ [Γ' [f J]]].
      simpl in d_prems |- *.
      simple refine (substitute_derivation _ _ (d_prems None)); try assumption.
      simple refine (Build_weakly_typed_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_typed_context_map _ _ _ f _) | ].
      + intros i. apply inr.
        exact (d_prems (Some i)).          
      + apply idpath.
    - destruct r_substeq as [Γ [Γ' [f [g [cl J]]]]].
      simpl in d_prems.
      simple refine (substitute_equal_derivation _ _ _ (d_prems None));
        try assumption.
      simple refine (Build_weakly_equal_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_equal_pair _ _ _ f g _) | ].
        * intros i. apply inr.
          exact (d_prems (Some (inr i))).
        * apply inr.
          exists tt; apply idpath.
    - simple refine (Closure.deduce' _ _ _).
      + exact (inr (r_from_t)).
      + apply idpath.
      + apply d_prems.
  Defined.

End Subst_Elimination.

(* TODO: it could be nice to give (here or elsewhere) a _counterexample_, showing how over a theory that’s not suitably substitutive/congruous, these results may fail. *)