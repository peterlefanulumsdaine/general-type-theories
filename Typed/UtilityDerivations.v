
Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.All.
Require Import Raw.SyntaxLemmas.
Require Import Raw.RawStructuralRule.

(** Some “utility derivations”: small bits of infrastructure frequently used for all sorts of derivations. *)

Section Sum_Shape_Empty.
(** This section provides infrastructure to deal with a problem
arising with instantiations of flat rules: their conclusion is typically
over a context whose shape is [ shape_sum Γ (shape_empty σ) ], not just [ Γ ]
as one would expect. 

  So we give here derivations going between a general judgement [ Γ |- J ] and
its reindexing to [ shape_sum Γ (shape_empty σ) ]. 

  It would be good to have some infrastructure (tactics or lemmas?) making
applications of this less intrusive: i.e. to allow one to use instantiations
of flat rules as the closure conditions one expects them to be, with just [Γ]
instead of [ shape_sum Γ (shape_empty σ) ]. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  (** From any judgement [ Γ |- J ],
      one can derive [ Γ+0 |- r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derivation_of_reindexing_to_empty_sum {T}
      {hjf : Judgement.hypothetical_form}
      (J : judgement Σ (form_hypothetical hjf))
      (J_tot := Build_judgement_total _ J)
    : Closure.derivation (structural_rule Σ + T)
        [< J_tot >] 
        (Judgement.rename J_tot (equiv_inverse (shape_sum_empty_inl _))).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, RawStructuralRule.rename. 
      exists J_tot.
      exact (_ ; equiv_inverse (shape_sum_empty_inl _)).
    - apply idpath.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  Definition derive_reindexing_to_empty_sum {T} {h}
      {hjf : Judgement.hypothetical_form}
      (J : judgement Σ (form_hypothetical hjf))
      (J_tot := Build_judgement_total _ J)
    : Closure.derivation (structural_rule Σ + T) h J_tot
    -> Closure.derivation (structural_rule Σ + T) h
         (Judgement.rename J_tot (equiv_inverse (shape_sum_empty_inl _))).
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_of_reindexing_to_empty_sum J) _).
    intros i. exact D.
  Defined.

  (* TODO: generalise this to arbitrary judgements, and add function
   [rename_judgement] (both to make this more general, and to make
   the statement cleaner). *)
  (* NOTE: test whether this or [derivation_of_reindexing_to_empty_sum]
   is easier to use in practice; maybe get rid of whichever is less
   useful. *)
  Definition derivation_of_judgement_over_empty_sum {T}
      {γ : σ} (γ0 := (shape_sum γ (shape_empty _)))
      {Γ_types : γ0 -> raw_type Σ γ0} (Γ := Build_raw_context γ0 Γ_types)
      {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
      (J_tot := Build_judgement_total _ (@Build_judgement _ _ 
                  (form_hypothetical _) Γ J))
      (J'_tot := Judgement.rename J_tot (shape_sum_empty_inl _))
    : Closure.derivation (structural_rule Σ + T)
        [< J'_tot >]
        J_tot.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, RawStructuralRule.rename.
      exists J'_tot. cbn.
      exact (_ ; equiv_inverse (shape_sum_empty_inl _)).
    - apply Judgement.eq_by_expressions. 
      + intros i.
        eapply concat.
        { apply inverse, rename_comp. }
        refine (_ @ ap _ _).
        * eapply concat. 2: { apply rename_idmap. }
          apply ap10. refine (apD10 _ _). apply ap.
          apply path_forall. refine (eissect _).
        * apply eisretr.
      + intros i. 
        eapply concat.
        { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply ap10. refine (apD10 _ _). apply ap.
        apply path_forall. refine (eissect _).
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  Definition derive_judgement_over_empty_sum {T} {h}
      {γ : σ} (γ0 := (shape_sum γ (shape_empty _)))
      {Γ_types : γ0 -> raw_type Σ γ0} (Γ := Build_raw_context γ0 Γ_types)
      {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
      (J_tot := Build_judgement_total _ (@Build_judgement _ _ 
                  (form_hypothetical _) Γ J))
      (J'_tot := Judgement.rename J_tot (shape_sum_empty_inl _))
    : Closure.derivation (structural_rule Σ + T) h J'_tot
    -> Closure.derivation (structural_rule Σ + T) h J_tot.
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_of_judgement_over_empty_sum J) _).
    intros i. exact D.
  Defined.

  (** Derivation of an arbitrary hypotherical judgement [ Γ |- J ],
   from its reindexing to the sum-with-empty, [ Γ+0 |- r^* J ].

   Can be used cleanly via [derive_from_reindexing_to_empty_sum] below. *)
  Definition derivation_from_reindexing_to_empty_sum {T}
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
      (J_tot := Build_judgement_total _ (@Build_judgement _ _ 
                  (form_hypothetical _) Γ J))
    : Closure.derivation (structural_rule Σ + T)
        [< Judgement.rename J_tot (equiv_inverse (shape_sum_empty_inl _)) >]
        J_tot.
  Proof.
    (* Outline: renaming rule, along [shape_sum_empty_inl], plus
    functoriality lemma for renaming to show that the conclusion
    of that is the original judgement. *)
    simple refine (Closure.deduce' _ _ _).
    - apply inl, RawStructuralRule.rename.
      exists (Judgement.rename J_tot (equiv_inverse (shape_sum_empty_inl _))).
      exists Γ. apply shape_sum_empty_inl. 
    - apply Judgement.eq_by_expressions; intros i.
      + eapply concat. { apply inverse, rename_comp. }
        eapply concat.
        { eapply (ap (fun f => rename f _)).
          apply path_forall; intros j; apply eissect. }
        eapply concat. { apply rename_idmap. }
        apply ap, eissect.
      + eapply concat. { apply inverse, rename_comp. }
        eapply concat.
        { eapply (ap (fun f => rename f _)).
          apply path_forall; intros j; apply eissect. }
        apply rename_idmap.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  (** To derive a judgement [ Γ |- J ],
      it’s sufficient to derive [ Γ+0 | - r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derive_from_reindexing_to_empty_sum {T} {h}
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
      (J_tot := Build_judgement_total _ (@Build_judgement _ _ 
                  (form_hypothetical _) Γ J))
    : Closure.derivation (structural_rule Σ + T) h
           (Judgement.rename J_tot (equiv_inverse (shape_sum_empty_inl _)))
    -> Closure.derivation (structural_rule Σ + T) h J_tot.
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_from_reindexing_to_empty_sum J) _).
    intros i. exact D.
  Defined.

End Sum_Shape_Empty.
