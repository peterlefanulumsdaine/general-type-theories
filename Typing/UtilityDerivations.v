
Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.StructuralRule.

(** Some “utility derivations”: small bits of infrastructure frequently used for all sorts of derivations. *)

Section Renaming.

  Context `{H_Funext : Funext} {σ : shape_system}.

  (** Interface to the renaming structural rule *)
  (* TODO: see if this is more convenient to use in places where older
   lemmas (eg [deduce_modulo_rename]) are currently used *)
  Lemma derive_rename {Σ : signature σ}
      {T : Closure.system (judgement Σ)} {H : family _}
      (cl_sys_T := structural_rule Σ + T)
      (Γ Γ' : raw_context Σ)
      (f : typed_renaming Γ Γ')
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation cl_sys_T H (Build_judgement Γ J)
    -> Closure.derivation cl_sys_T H
      (Build_judgement Γ' (rename_hypothetical_judgement f J)).
  Proof.
    intros D.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, StructuralRule.rename. exists Γ, Γ', f; exact J. }
    { apply idpath. }
    { intros; apply D. }
  Defined.

  Lemma derive_rename' {Σ : signature σ}
      {T : Closure.system (judgement Σ)} {H : family _}
      (cl_sys_T := structural_rule Σ + T)
      (J J' : judgement Σ)
      (f : typed_renaming
             (context_of_judgement J') (context_of_judgement J))
      (e : hypothetical_part J
           = rename_hypothetical_judgement f (hypothetical_part J'))
    : Closure.derivation cl_sys_T H J'
    -> Closure.derivation cl_sys_T H J.
  Proof.
    intros D.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, StructuralRule.rename.
      refine (_;(_;(f;_))). exact J'. }
    { apply (ap (Build_judgement _)), inverse, e. }
    { intros; apply D. }
  Defined.

  (** Commonly-required analogue of [Closure.deduce']. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma deduce_modulo_rename {Σ : signature σ}
      {T : Closure.system (judgement Σ)}
      (cl_sys_T := structural_rule Σ + T)
      {H : family _} {J : judgement _}
      (r : cl_sys_T)
      (e : shape_of_judgement J
          <~> shape_of_judgement (Closure.conclusion (cl_sys_T r)))
      (e_J : Judgement.rename (Closure.conclusion (cl_sys_T r)) e
             = J)
      (D : forall p : Closure.premises (cl_sys_T r),
          Closure.derivation cl_sys_T H (Closure.premises _ p))
    : Closure.derivation cl_sys_T H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (context_of_judgement (Closure.conclusion (cl_sys_T r))).
      exists (context_of_judgement J).
      refine (_; hypothetical_part (Closure.conclusion (cl_sys_T r))).
      exists (equiv_inverse e).
      admit.
    - admit.
    - intros [].
      exact (Closure.deduce _ _ r D).
  Admitted.

  (** Commonly-required analogue of [Closure.deduce'], similar to [deduce_modulo_rename] above. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma hypothesis_modulo_rename {Σ : signature σ}
      {T : Closure.system (judgement Σ)}
      {H : family (judgement _)}
      {J : judgement _}
      (h : H)
      (e : shape_of_judgement J <~> shape_of_judgement (H h))
      (e_J : Judgement.rename (H h) e = J)
    : Closure.derivation (structural_rule Σ + T) H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (context_of_judgement (H h)).
      exists (context_of_judgement J).
      refine (_; hypothetical_part (H h)).
      exists (equiv_inverse e).
      admit.
    - admit.
    - intros [].
      exact (Closure.hypothesis _ _ h).
  Admitted.

End Renaming.

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
      (J : judgement Σ)
    : Closure.derivation (structural_rule Σ + T)
        [< J >] 
        (Judgement.rename J (equiv_inverse (shape_sum_empty_inl _))).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (context_of_judgement J).
      exists (Context.rename (context_of_judgement J)
                (equiv_inverse (shape_sum_empty_inl _))).
      exists (Context.typed_renaming_to_rename_context _ _).
      exact (hypothetical_part J).
    - apply idpath.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  Definition derive_reindexing_to_empty_sum {T} {h}
      (J : judgement Σ)
    : Closure.derivation (structural_rule Σ + T) h J
    -> Closure.derivation (structural_rule Σ + T) h
         (Judgement.rename J (equiv_inverse (shape_sum_empty_inl _))).
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_of_reindexing_to_empty_sum J) _).
    intros i. exact D.
  Defined.

  (* TODO: generalise this to arbitrary judgements, and add function
   [Judgement.rename] (both to make this more general, and to make
   the statement cleaner). *)
  (* NOTE: test whether this or [derivation_of_reindexing_to_empty_sum]
   is easier to use in practice; maybe get rid of whichever is less
   useful. *)
  Definition derivation_of_judgement_over_empty_sum {T}
      {γ : σ} (γ0 := (shape_sum γ (shape_empty _)))
      {Γ_types : γ0 -> raw_type Σ γ0} (Γ := Build_raw_context γ0 Γ_types)
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation (structural_rule Σ + T)
        [< Judgement.rename (Build_judgement Γ J) (shape_sum_empty_inl _) >]
        (Build_judgement Γ J).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (Context.rename Γ (shape_sum_empty_inl _)).
      exists Γ.
      exists (Context.typed_renaming_from_rename_context _ _).
      refine (rename_hypothetical_judgement _ J).
      exact (equiv_inverse (shape_sum_empty_inl _)).
    - apply Judgement.eq_by_expressions.
      + intros; apply idpath.
      + intros.
        eapply concat. { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply (ap (fun f => Expression.rename f _)).
        apply path_forall; intros j; apply eisretr.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  Definition derive_judgement_over_empty_sum {T} {h}
      {γ : σ} (γ0 := (shape_sum γ (shape_empty _)))
      {Γ_types : γ0 -> raw_type Σ γ0} (Γ := Build_raw_context γ0 Γ_types)
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation (structural_rule Σ + T) h
        (Judgement.rename (Build_judgement Γ J) (shape_sum_empty_inl _) )
    -> Closure.derivation (structural_rule Σ + T) h (Build_judgement Γ J).
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_of_judgement_over_empty_sum J) _).
    intros i. exact D.
  Defined.

  (** Derivation of an arbitrary hypotherical judgement [ Γ |- J ],
   from its reindexing to the sum-with-empty, [ Γ+0 |- r^* J ].

   Can be used cleanly via [derive_from_reindexing_to_empty_sum] below. *)
  Definition derivation_from_reindexing_to_empty_sum {T}
      {Γ : raw_context Σ}
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation (structural_rule Σ + T)
        [< Judgement.rename
             (Build_judgement Γ J) (equiv_inverse (shape_sum_empty_inl _)) >]
        (Build_judgement Γ J).
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (Context.rename Γ (equiv_inverse (shape_sum_empty_inl _))).
      exists Γ.
      exists (Context.typed_renaming_from_rename_context _ _).
      exact (rename_hypothetical_judgement (shape_sum_empty_inl _) J).
    - apply Judgement.eq_by_expressions; intros i.
      + apply idpath.
      + eapply concat. { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply (ap (fun f => Expression.rename f _)).
        apply path_forall; intros j; apply eissect.
    - intros [].
      refine (Closure.hypothesis _ [<_>] tt).
  Defined.

  (** To derive a judgement [ Γ |- J ],
      it’s sufficient to derive [ Γ+0 | - r^* J ],
   where [Γ+0] is the sum of Γ with the empty shape,
   and r^*J is the reindexing of [J] to [Γ+0]. *)
  Definition derive_from_reindexing_to_empty_sum {T} {h}
      {Γ : raw_context Σ}
      (J : hypothetical_judgement Σ Γ)
    : Closure.derivation (structural_rule Σ + T) h
          (Judgement.rename
             (Build_judgement Γ J) (equiv_inverse (shape_sum_empty_inl _)))
    -> Closure.derivation (structural_rule Σ + T) h (Build_judgement Γ J).
  Proof.
    intros D.
    refine (Closure.graft _ (derivation_from_reindexing_to_empty_sum J) _).
    intros i. exact D.
  Defined.

End Sum_Shape_Empty.
