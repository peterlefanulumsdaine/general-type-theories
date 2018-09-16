Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.All.

Section Instantiations.
(** Double instantiations. *)

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  (* NOTE: it feels like there should be a more systematic way to present the following lemmas — some kind of monadic structure on extensions/instantiations. Contemplate this, and try to figure it out? *)

  (* TODO: upstream to [RawSyntax.Metavariable]? *)
  Definition unit_instantiation (a : arity σ)
    : Metavariable.instantiation a (Metavariable.extend Σ a) (shape_empty σ).
  Proof.
    intros A.
    refine (raw_symbol (include_metavariable A) _).
    intros i. apply raw_variable.
    refine (coproduct_inj1 shape_is_sum _).
    refine (coproduct_inj2 shape_is_sum _).
    exact i.
  Defined.

  Lemma unit_instantiate_expression {a}
      {cl} {γ} (e : raw_expression (Metavariable.extend Σ a) cl γ)
    : instantiate_expression (unit_instantiation a)
        (Expression.fmap (Metavariable.fmap1 include_symbol _) e)
      = rename (coproduct_inj2 shape_is_sum) e.
  Proof.
    induction e as [ γ i | γ [S | M] args IH ].
    - apply idpath.
    - simpl. 
      apply ap, path_forall; intros i.
      eapply concat. { apply ap, IH. }
      eapply concat. { apply inverse, rename_comp. }
      apply (ap (fun f => rename f _)), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse. refine (coproduct_comp_inj1 _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse. refine (coproduct_comp_inj2 _).
    - simpl.
      apply ap, path_forall; intros i.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { apply ap, ap, IH. }
      apply inverse.
      eapply concat. 2: { apply rename_comp. }
      eapply concat. 2: { apply rename_comp. } 
      apply (ap (fun f => rename f _)), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse. 
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply ap, ap. refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
  Defined.

  Lemma unit_instantiate_context
      {a} (Γ : raw_context (Metavariable.extend Σ a))
    : Context.instantiate [::] (unit_instantiation a)
        (Context.fmap (Metavariable.fmap1 include_symbol _) Γ)
      = Context.rename Γ (shape_sum_empty_inr _)^-1.
  Proof.
    apply (ap (Build_raw_context _)), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - apply (empty_rect _ shape_is_empty).
    - intros x.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      eapply concat. { apply unit_instantiate_expression. }
      apply ap, ap, inverse. cbn.
      refine (coproduct_comp_inj2 _).
  Defined.

  Lemma unit_instantiate_judgement
      {a} (J : judgement_total (Metavariable.extend Σ a))
    : Judgement.instantiate [::] (unit_instantiation a)
        (fmap_judgement_total (Metavariable.fmap1 include_symbol _) J)
      = Judgement.rename J (shape_sum_empty_inr _)^-1.
  Proof.
    destruct J as [ [ | hjf ] J ].
    - (* context judgement *)
      destruct J as [J []].
      simpl. unfold Judgement.instantiate, Judgement.rename. 
      apply ap, ap10, ap.
      apply unit_instantiate_context.
    - (* hypothetical judgement *)
      apply Judgement.eq_by_expressions.
      + refine (coproduct_rect shape_is_sum _ _ _).
        * apply (empty_rect _ shape_is_empty).
        * intros x.
          eapply concat. { refine (coproduct_comp_inj2 _). }
          eapply concat. { apply unit_instantiate_expression. }
          apply ap, ap, inverse. cbn.
          refine (coproduct_comp_inj2 _).
      + intros i; apply unit_instantiate_expression.
  Defined.


  (* TODO: upstream to [RawSyntax.Metavariable]? *)
  Definition instantiate_instantiation
      {γ} {a} (I : Metavariable.instantiation a Σ γ)
      {δ} {b} (J : Metavariable.instantiation b (Metavariable.extend Σ a) δ)
    : Metavariable.instantiation b Σ (shape_sum γ δ).
  Proof.
    intros i.
    refine (rename _ (Metavariable.instantiate_expression I (J i))).
    apply shape_assoc.
  Defined.

  Lemma instantiate_instantiate_expression 
      {γ} {a} (I : Metavariable.instantiation a Σ γ)
      {δ} {b} (J : Metavariable.instantiation b (Metavariable.extend Σ a) δ)
      {cl} {θ} (e : raw_expression (Metavariable.extend Σ b) cl θ)
    : Metavariable.instantiate_expression
        (instantiate_instantiation I J) e
    = rename (shape_assoc _ _ _)
        (Metavariable.instantiate_expression I
          (Metavariable.instantiate_expression J
            (Expression.fmap (Metavariable.fmap1 include_symbol _) e))).
  Proof.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ].
    - (* [e] is a variable *)
      cbn. apply inverse, ap.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine (coproduct_comp_inj2 _).
    - (* [e] is a symbol of [Σ] *)
      simpl Expression.fmap.
      simpl Metavariable.instantiate_expression.
      simpl rename.
      apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply inverse, rename_comp. }
      apply inverse.
      eapply concat. { apply ap, ap. apply instantiate_rename. }
      eapply concat. { apply inverse, rename_comp. }
      eapply concat. { apply inverse, rename_comp. }
      apply (ap (fun f => rename f _)).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      (* NOTE: would be better to reduce all the following to a tactic.
       (Or, better still, to have it compute!) *)
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - (* [e] is a metavariable of [b] *)
      simpl Expression.fmap.
      simpl Metavariable.instantiate_expression.
      simpl rename.
      eapply concat.
      { refine (ap (fun f => substitute f _) _).
        refine (ap (fun f => coproduct_rect _ _ _ f) _).
        refine (@path_arrow _ _ _ _ (fun i => rename _ _) _); intros i.
        apply ap, IH_e_args.   
      } clear IH_e_args.
      unfold instantiate_instantiation.
      eapply concat. { apply substitute_rename. }
      eapply inverse.
      eapply concat. { apply ap, instantiate_substitute. }
      eapply concat. { apply rename_substitute. }
      refine (ap (fun f => substitute f _) _).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        simpl rename. eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        cbn. eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, instantiate_rename. }
        eapply concat. { apply inverse, rename_comp. }
        apply inverse. 
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply inverse, rename_comp. }
        apply (ap (fun f => rename f _)). clear e_args.
        apply path_forall.
        repeat refine (coproduct_rect shape_is_sum _ _ _); intros k.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). } cbn.
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          refine (coproduct_comp_inj2 _).
        * revert k. apply empty_rect, shape_is_empty.
  Defined.

  (* TODO: If we refactored judgements to put the shape as separate component throughout (i.e. so that [shape_of_judgement] computes without destructing the judgement form), then this would be cleaner (i.e. could just be [shape_assoc] in general, so could be inlined). *)
  Lemma instantiate_instantiate_shape_of_judgement
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement_total (Metavariable.extend Σ b))
  : shape_of_judgement
      (Judgement.instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) j)
  <~>
    shape_of_judgement
      (Judgement.instantiate Γ I
        (Judgement.instantiate Δ J
          (fmap_judgement_total (Metavariable.fmap1 include_symbol _) j))).
  Proof.
    apply equiv_inverse,shape_assoc.
  Defined.

  Lemma instantiate_instantiate_context_pointwise
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (K : raw_context (Metavariable.extend Σ b))
    : forall i,
      Context.instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) K i
    = Context.rename
        (Context.instantiate Γ I
          (Context.instantiate Δ J
            (Context.fmap (Metavariable.fmap1 include_symbol _) K)))
        (shape_assoc _ _ _)^-1
        i.
  Proof.
  repeat refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; cbn.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply inverse, rename_comp. }
      apply inverse.
      eapply concat.
      { apply ap.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      }
      eapply concat. { apply inverse, rename_comp. }
      refine (ap (fun f => rename f _) _).
      clear i. apply path_forall; intros x.
      refine (coproduct_comp_inj1 _).
    - intros i; cbn.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      apply inverse.
      eapply concat.
      { apply ap.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
      }
      eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap, instantiate_rename. }
      eapply concat. { apply inverse, rename_comp. }
      refine (ap (fun f => rename f _) _).
      clear i. apply path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
    - intros i.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      eapply concat. { apply instantiate_instantiate_expression. }
      refine ((ap (fun f => rename f _) _) @ ap _ _).
      + apply ap, inverse, einv_V. 
      + apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply ap. refine (coproduct_comp_inj2 _).
  Defined.

  Lemma instantiate_instantiate_judgement
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement_total (Metavariable.extend Σ b))
    : Judgement.instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) j
    = Judgement.rename
        (Judgement.instantiate Γ I
          (Judgement.instantiate Δ J
            (fmap_judgement_total (Metavariable.fmap1 include_symbol _) j)))
         (shape_assoc _ _ _)^-1.
  Proof.
    destruct j as [[ | jf ] j].
    - apply (ap (Build_judgement_total _)),
            (ap (fun Γ => Build_judgement Γ _)),
            (ap (fun A => Build_raw_context _ A)).
      apply path_forall.
      intros i; apply instantiate_instantiate_context_pointwise.
    - apply Judgement.eq_by_expressions.
      + apply instantiate_instantiate_context_pointwise.
      + intros i. refine (instantiate_instantiate_expression _ _ _).
  Defined.

End Instantiations.