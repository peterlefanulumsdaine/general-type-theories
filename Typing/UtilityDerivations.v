
Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.StructuralRule.

(** Some “utility derivations”: small bits of infrastructure frequently used for all sorts of derivations. *)

Section Renaming.

  Context `{H_Funext : Funext} {σ : shape_system}.

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
        eapply concat. { apply rename_rename. }
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
      + eapply concat. { apply rename_rename. }
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

Section Usable_Structural_Rules.
(** Here we give more directly usable forms of the structural rules. *)

Context `{H_Funext : Funext}
        {σ : shape_system} {Σ : signature σ}
        {C : Closure.system (judgement Σ)} (T := (structural_rule Σ + C))
        {H : family (judgement Σ) }.

(* TODO: perhaps improve modularity and usability of these lemmas by making type-classes for closure systems admitting each structural rule? *)

(* TODO: at the moment, these only work for “canonical” judgements,
so usage of these often needs to be preceded by [apply Judgement.canonicalise.]
We could easily generalise the statements here to apply directly to aritrary
judgements, but the statements would become less readable. But probably we should do this! *)

(* TODO: complete this section [Usable_Structural_Rules], giving usable forms of all structural rules. *)

Definition derive_variable
    { Γ : raw_context Σ } { i : Γ }
    ( d_Γi : derivation T H [! Γ |- Γ i !] )
  : derivation T H [! Γ |- raw_variable i ; Γ i !].
Proof.
  simple refine (Closure.deduce' _ _ _).
  { apply inl, variable_rule.
    exists Γ; exact i.
  }
  { apply idpath. }
  intros p; recursive_destruct p.
  apply d_Γi.
Defined.


(** A slightly technical lemma, useful under
[Judgement.eq_by_expressions] for the types of a context
reindexed under [shape_sum_empty_inl]. *)
(* TODO: perhaps upstream to e.g. [Context]? *)
Lemma instantiate_empty_ptwise
    (Γ : raw_context Σ)
    (f : shape_empty σ -> raw_type Σ _)
    (i : shape_sum Γ (shape_empty σ))
  : coproduct_rect (shape_is_sum) _
      (fun j:Γ => rename (shape_sum_empty_inl _) (Γ j))
      f i
  = Context.rename Γ (shape_sum_empty_inl _)^-1 i.
Proof.
  revert i. cbn.
  apply (coproduct_rect shape_is_sum).
  + intros ?.
    eapply concat. { refine (coproduct_comp_inj1 _). }
    cbn. apply ap, ap.
    apply inverse. refine (coproduct_comp_inj1 _).
  + exact (empty_rect _ shape_is_empty _).
Defined.

(** A slightly technical lemma, useful under
[Judgement.eq_by_expressions] for the expressions coming from
instantiating a metavariable with empty binder. *)
(* TODO: perhaps upstream to e.g. [Metavariable]? *)
Lemma instantiate_binderless_metavariable
  {γ : σ} {cl}
  (E : raw_expression Σ cl (shape_sum γ (shape_empty _)))
  {f}
  : substitute
      (coproduct_rect shape_is_sum _
        (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
        f)
      E
    = E.
Proof.
  eapply concat. 2: { apply rename_idmap. }
  eapply concat. 2: { apply substitute_raw_variable. }
  apply (ap (fun g => substitute g _)).
  apply path_forall.
  refine (coproduct_rect shape_is_sum _ _ _).
  - intros i; refine (coproduct_comp_inj1 _).
  - apply (empty_rect _ shape_is_empty).
Defined.

Definition derive_tyeq_refl
    (Γ : raw_context Σ) (A : raw_expression Σ class_type Γ)
    (d_A : derivation T H [! Γ |- A !])
  : derivation T H [! Γ |- A ≡ A !].
Proof.
  apply derive_from_reindexing_to_empty_sum.
  simple refine (Closure.deduce' _ _ _).
  { apply inl, tyeq_refl. 
    exists Γ.
    intros i; recursive_destruct i. cbn.
    refine (rename _ A). 
    apply shape_sum_empty_inl. }
  { refine (Judgement.eq_by_expressions _ _).
    - intros i. apply instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
      apply instantiate_binderless_metavariable.
  }
  intros [].
  refine (transport _ _
            (derive_reindexing_to_empty_sum _ d_A)).
  apply Judgement.eq_by_expressions.
  - intros i. apply inverse, instantiate_empty_ptwise.
  - intros i; recursive_destruct i;
      apply inverse, instantiate_binderless_metavariable.
Defined.

Definition derive_tyeq_sym
    (Γ : raw_context Σ) (A B : raw_expression Σ class_type Γ)
    (d_AB : derivation T H [! Γ |- A ≡ B !])
  : derivation T H [! Γ |- B ≡ A !].
Proof.
Admitted. (* [derive_tyeq_sym]: straightforward, similar to others in section *)

(* rule term_convert

 ⊢ A, B type
 ⊢ A ≡ B type
 ⊢ u : A
-------------
 ⊢ u : B
*)
Definition derive_term_convert
    ( Γ : raw_context Σ )
    ( A B : raw_expression Σ class_type Γ )
    ( u : raw_expression Σ class_term Γ )
    ( d_A : derivation T H [! Γ |- A !] )
    ( d_B : derivation T H [! Γ |- B !] )
    ( d_AB : derivation T H [! Γ |- A ≡ B !] )
    ( d_u : derivation T H [! Γ |- u ; A !] )
  : derivation T H [! Γ |- u ; B !].
Proof.
  apply derive_from_reindexing_to_empty_sum.
  simple refine (Closure.deduce' _ _ _).
  { apply inl, term_convert.
    exists Γ.
    intros i; recursive_destruct i;
      refine (rename (shape_sum_empty_inl _) _).
    + exact A.
    + exact B.
    + exact u.
  }
  { refine (Judgement.eq_by_expressions _ _).
    - apply instantiate_empty_ptwise.
    - intros i; recursive_destruct i;
        apply instantiate_binderless_metavariable.
  }
  intros p. set (p_keep := p).
  recursive_destruct p;
    [ set (d := d_A) | set (d := d_B) | set (d := d_AB) | set (d := d_u) ];
    refine (transport _ _ (derive_reindexing_to_empty_sum _ d));
    (apply Judgement.eq_by_expressions;
    [ intros; apply inverse, instantiate_empty_ptwise
    | intros i; recursive_destruct i;
        apply inverse, instantiate_binderless_metavariable]).
Defined.

(* TODO: once this section done, rewrite the derivations in [TypedStructuralRules] using these. *)

End Usable_Structural_Rules.