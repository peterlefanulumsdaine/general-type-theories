
Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.RawSubstitution.
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

  Definition shape_sum_empty (γ : σ) : σ
  := shape_sum γ (shape_empty σ).

  Definition shape_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 shape_is_sum : γ -> shape_sum_empty γ).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + intros i; exact i.
      + apply (empty_rect _ shape_is_empty).
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + intros i. apply ap.
        refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
    - intros i. refine (coproduct_comp_inj1 _).
  Defined.

  Definition shape_sum_empty_inl (γ : σ)
    : γ <~> shape_sum_empty γ
  := BuildEquiv _ _ _ (shape_sum_empty_inl_is_equiv γ).

  Definition raw_context_sum_empty (Γ : raw_context Σ)
    : raw_context Σ
  := rename_raw_context _ Γ (equiv_inverse (shape_sum_empty_inl _)).

  Definition reindexing_to_empty_sum
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical hjf).
    exists (raw_context_sum_empty Γ).
    intros i. exact (rename (shape_sum_empty_inl _) (J i)).
  Defined.

  (* TODO: upstream, at least to [RawStructuralRules] with [rename_raw_context]
     ; and use wherever possible, eg in renaming rules. *)
  Definition rename_hypothetical_judgment
      {Γ : raw_context Σ} {γ' : σ.(shape_carrier)} (f : γ' <~> Γ)
      {hjf} (J : hypothetical_judgement Σ hjf Γ)
    : hypothetical_judgement Σ hjf (rename_raw_context _ Γ f).
  Proof.
    intros i; exact (rename f^-1 (J i)).
  Defined.

  (** From any judgement [ Γ |- J ],
      one can derive [ Γ+0 |- r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derivation_of_reindexing_to_empty_sum {T}
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ + T)
        [< (form_hypothetical hjf ; (Γ ; J)) >] 
        (reindexing_to_empty_sum J).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, rename_hypothetical.
      exists Γ.
      refine (_ ; (equiv_inverse (shape_sum_empty_inl _) ; _)).
      exists hjf. exact J.
    - apply idpath.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  Definition derive_reindexing_to_empty_sum {T} {h}
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ + T) h
                             (form_hypothetical hjf ; (Γ ; J))
    -> Closure.derivation (structural_rule Σ + T) h
                             (reindexing_to_empty_sum J).
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
      (Γ' := rename_raw_context _ Γ (shape_sum_empty_inl _))
      (J' := (form_hypothetical hjf ; (Γ' ;
               (fun i => rename (shape_sum_empty_inl _)^-1 (J i))
      : hypothetical_judgement _ _ _)))
    : Closure.derivation (structural_rule Σ + T)
        [< J' >]
        (form_hypothetical hjf ; (Γ ; J)).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, rename_hypothetical.
      exists Γ'.
      refine (_ ; (equiv_inverse (shape_sum_empty_inl _) ; _)).
      exists hjf. exact J'.2.2.
    - apply Judgement.eq_by_expressions. 
      + intros i. subst Γ'.
        eapply concat.
        { apply inverse, rename_comp. }
        refine (_ @ ap _ _).
        * eapply concat. 2: { apply rename_idmap. }
          apply ap10. refine (apD10 _ _). apply ap.
          apply path_forall. refine (eissect _).
        * apply eisretr.
      + intros i; subst J'. 
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
      (Γ' := rename_raw_context _ Γ (shape_sum_empty_inl _))
      (J' := (form_hypothetical hjf ; (Γ' ;
               (fun i => rename (shape_sum_empty_inl _)^-1 (J i))
      : hypothetical_judgement _ _ _)))
    : Closure.derivation (structural_rule Σ + T) h J'
    -> Closure.derivation (structural_rule Σ + T) h
                            (form_hypothetical hjf ; (Γ ; J)).
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
    : Closure.derivation (structural_rule Σ + T)
        [< reindexing_to_empty_sum J >]
        (form_hypothetical hjf ; (Γ ; J)).
  Proof.
    (* Outline: renaming rule, along [shape_sum_empty_inl], plus
    functoriality lemma for renaming to show that the conclusion
    of that is the original judgement. *)
    simple refine (Closure.deduce' _ _ _).
    - apply inl, rename_hypothetical.
      exists (raw_context_sum_empty Γ),
        Γ, (shape_sum_empty_inl _), hjf.
      exact (fun i => rename (shape_sum_empty_inl _) (J i)).
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
  (* TODO: rename everything involving [Raw_Weaken], [Raw_Subst]! *)

  (** To derive a judgement [ Γ |- J ],
      it’s sufficient to derive [ Γ+0 | - r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derive_from_reindexing_to_empty_sum {T} {h}
      {Γ : raw_context Σ} {hjf : Judgement.hypothetical_form}
      (J : hypothetical_judgement Σ hjf Γ)
    : Closure.derivation (structural_rule Σ + T) h
                         (reindexing_to_empty_sum J)
    -> Closure.derivation (structural_rule Σ + T) h
                         (form_hypothetical hjf ; (Γ ; J)).
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_from_reindexing_to_empty_sum J) _).
    intros i. exact D.
  Defined.

End Sum_Shape_Empty.
