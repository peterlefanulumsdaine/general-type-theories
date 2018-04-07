Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.
Require Import Typed.TypedClosure.
Require Import Raw.FlatTypeTheoryMap.
Require Import Typed.TypedStructuralRule.
Require Import Typed.TypeTheory.

(** Presuppositions of a derivable judgement are derivable, over any type theory. *)
Local Definition derive_presupposition {σ} {T : raw_type_theory σ}
     {j : judgement_total (RawTypeTheory.signature T)}
     (dj : RawTypeTheory.derivation T [<>] j)
     {p : presupposition j }
  : RawTypeTheory.derivation T [<>] (presupposition j p).
Abort.

(** In order to establish this, we require a few bits of background machinery:
  - for the high level structure of the proof, abstractions of the notions of “closed under presuppositions” to flat type theories and closure systems;
  - for the lower level details, some lemmas on the interaction of derivations/presuppositions with translation under metavariable instantiations. *)

(** General background: establish some properties of how the syntactic translation given by metavariable instantiation preserves typing derivations.

  TODO: probably factor this out into a separate file. *)
Section DerivabilityUnderInstantiation.

  Context {σ : shape_system}.

  (* TODO: Perhaps upstream to [Metavariable]. *)
  Arguments Metavariable.instantiate_judgement : simpl nomatch.
  Arguments Metavariable.instantiate_expression : simpl nomatch.
  Arguments Metavariable.instantiate_context : simpl nomatch.

  (** The presuppositions of a judgement [j] instantiated by the instantiation [I]
      are equal to mapping the instantiation [I] over all presuppositions of [j]. *)
  (* TODO: upstream, but to where? *)
  (* TODO maybe attempt to refactor [presupposition] to make this easier.
   (Note: that refactoring has already been tried at least once, and seems difficult.) *)
  Local Definition presupposition_instantiate `{Funext}
      {Σ : signature σ}
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement_total _)
    : presupposition (Metavariable.instantiate_judgement I j)
      = Family.fmap (Metavariable.instantiate_judgement I) (presupposition j).
  Proof.
    destruct j as [[ | hjf] j].
    - simple refine (Family.eq _ _); try apply idpath.
      intros [].
    - simple refine (Family.eq _ _); try apply idpath.
      intros i. cbn in i. destruct i as [ i | ].
      + (* slots *)
        (* Do some computation by hand: *)
        simpl (equiv_path _ _ 1).
        eapply concat.
        Focus 2. { apply ap. exact (idpath (Some i)). } Unfocus.
        (* The judgement and context parts are judgementally equal: *)
        simple refine (path_sigma _ _ _ _ _); try apply idpath.
        simple refine (path_sigma _ _ _ _ _); try apply idpath.
        apply path_forall; intros k.
        recursive_destruct hjf;
        recursive_destruct i;
        recursive_destruct k;
        try apply idpath.
      + (* raw context *)
        apply idpath.
  Defined.

End DerivabilityUnderInstantiation.

Section PresuppositionsDerivable.
  (** Main theorem: [presupposition_derivable]: the presuppositions of any derivable judgement are again derivable. *)

  Context {σ : shape_system} `{Funext}.

  (* TODO: make Σ implicit in fields of [flat_rule] *)
  (** A flat rule is presupposition-closed, over an ambient flat theory [R],
     if all presuppositions of its conclusion are derivable from
     the premises together with their presuppositions,
     over [T] (translated up to the metavariable-extension signature) *)
  Definition presupposition_closed_flat_rule {Σ : signature σ}
      (T : flat_type_theory Σ) (r : flat_rule Σ)
    : Type
  := forall i : presupposition (flat_rule_conclusion _ r), 
      FlatTypeTheory.derivation
        (FlatTypeTheory.fmap include_symbol T)
        (flat_rule_premises _ r + (Family.bind (flat_rule_premises _ r) presupposition))
        (presupposition _ i).

  (** A flat type theory is presupposition-closed if all its rules are. *)
  Definition presupposition_closed_flat_type_theory
      {Σ : signature σ} (T : flat_type_theory Σ)
    : Type
  := forall r : T, presupposition_closed_flat_rule T (T r).

  (** If a flat type theory T is presup-closed, then so is its associated closure system. *)
  Theorem closure_system_of_presupposition_closed_flat_type_theory
      {Σ : signature σ} {T : flat_type_theory Σ}
      (T_presup_closed : presupposition_closed_flat_type_theory T)
    : TypedClosure.weakly_well_typed_system presupposition (FlatTypeTheory.closure_system T).
  Proof.
    intros [r_str | r_log ].
    - intros p.
      refine (Closure.map_derivation _ _).
      Focus 2. { apply TypedStructuralRule.well_typed. } Unfocus.
      apply Closure.map_from_family_map, Family.inl.
    - destruct r_log as [r r_inst]. cbn in r_inst.
      destruct r_inst as [Γ r_args].
      unfold TypedClosure.weakly_well_typed_rule.
      cbn.
      set (Pr := presupposition (Metavariable.instantiate_judgement r_args
                                             (flat_rule_conclusion _ (T r)))).
      assert (H_presup_inst : Pr =
          Family.fmap (Metavariable.instantiate_judgement r_args)
                      (presupposition (flat_rule_conclusion _ (T r)))).
      { apply presupposition_instantiate. }
      clearbody Pr. destruct H_presup_inst^.
      intros p.
      refine (Closure.graft _ _ _).
      + refine (FlatTypeTheory.instantiate_derivation _ _ _ _).
        apply T_presup_closed.
      + intros [ i | [ i i_presup]]. 
        * eapply (flip (transport _)).
          { refine (Closure.hypothesis _ _ _). exact (inl i). }
          apply idpath.
        * assert (ip'_e :
            { ip' : presupposition
                      (Metavariable.instantiate_judgement r_args
                        (flat_rule_premises _ (T r) i))
            & presupposition _ ip'
              = Metavariable.instantiate_judgement r_args
                  (presupposition _ i_presup)}).
          { 
            set (Pr := presupposition (Metavariable.instantiate_judgement r_args
                                             (flat_rule_premises _ (T r) i))).
            assert (H' : Pr =
                                    Family.fmap (Metavariable.instantiate_judgement r_args)
                      (presupposition (flat_rule_premises _ (T r) i))).
            { apply presupposition_instantiate. }
            clearbody Pr. destruct H'^. 
            exists i_presup. apply idpath.
          }
          destruct ip'_e as [i_presup' e].
          eapply (flip (transport _)).
          { refine (Closure.hypothesis _ _ _). refine (inr (i;_)).
            exact i_presup'. }
          apply e.
  (* TODO: this whole proof is quite painful.  Can it be cleaned up somehow?
     E.g. would it be easier if [presupposition_instantiate] were given as a
     family map instead of an equality? *)
  Defined.

  (* TODO: perhaps change def of flat rules to allow only _hypothetical_ judgements? *)
  Theorem presupposition_derivation_from_flat
      {Σ : signature σ}
      {T : flat_type_theory Σ} (H_T : presupposition_closed_flat_type_theory T)
      {j : judgement_total Σ} {hyps : family _}
      (d_j : FlatTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : FlatTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    simple refine
      (TypedClosure.presupposition_derivation presupposition _ d_j _).
    apply closure_system_of_presupposition_closed_flat_type_theory.
    apply H_T.
  Defined.

  (** For any raw type theory [T] and a rule [r] of the flattened [T], every
      presupposition in the boundary of the conclusion of [r] can be derived. *)
  Lemma presupposition_closed_flatten {T : raw_type_theory σ}
    : presupposition_closed_flat_type_theory (RawTypeTheory.flatten T).
  Proof.
    (* The flattened [T] has logical and congruence rules, two cases to consider. *)
    intros [r|r].
    - {
        (* [r] is a logical rule, we consider one of the presuppositions [p] of the conclusion. *)
        intros p.
        (* We must show that [p] has a derivation. *)
        destruct (flat_rule_conclusion _ ((RawTypeTheory.flatten T) (inl r))) as [[|hjf] j].
        - (* [p] is in the boundary of the presupposition that the context of the conclusion
            is well -formed, whose boundary is empty. There is no such [p]. *)
            elim p.
        - { destruct hjf as [[|]|eq].
            + (* p is a position in the boundary of "is a type" judgement.
                There is one position, namely the context. *)
              destruct p as [[]|].
              (* We need to show that the context of the conclusion is well-formed. *)
              destruct j as [j_ctx j_jdg].
              admit.
            + admit.
            + admit.
          }
      }
  Admitted.

  (* TODO: at least make access function between [judgment] and [judgement_total]; perhaps make it a coercion? *)
  (** Working in a type theory [T], given a judgement [j] which is derivable
      from hypotheses [hyps], suppose every presupposition [q] of every hypothesis [h : hyps]
      is derivable from [hyps], then every presuppsition [p] of [j] is derivable from
      [hyps]. *)
  Theorem presupposition_derivation {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      {hyps : family _}
      (dj : RawTypeTheory.derivation T hyps j)
      {p : presupposition j }
    : RawTypeTheory.derivation T
        (hyps + Family.bind hyps presupposition)
        (presupposition _ p).
  Proof.
    apply presupposition_derivation_from_flat; try assumption.
    apply presupposition_closed_flatten.
  Defined.

  (** Working in a type theory [T], given a judgment [j] which is derivable
      without hypotheses, ever presupposition of [j] is derivable. *)
  Corollary closed_presupposition_derivation {T : raw_type_theory σ}
      {j : judgement_total (RawTypeTheory.signature T)}
      (dj : RawTypeTheory.derivation T [<>] j)
      {p : presupposition j }
    : RawTypeTheory.derivation T [<>] (presupposition j p).
  Proof.
    refine (Closure.graft _ _ _).
    - refine (presupposition_derivation dj).
    - intros i. recursive_destruct i.
  Defined.

End PresuppositionsDerivable.
