Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.
Require Import Syntax.Metavariable.

(** Note: our treatment of contexts is slightly unorthodox in one respect.

In a context such as [ x1 : A1, x2 : A2, x3 : A3 ], we do not record the ordering of the variables and types; and, as such, we do not say “A1 is a closed type expression, A2 is a type expression over {x1}, …”, but instead take A1, A2, A3 all as type expressions over the full set of variables {x1, x2, x3}.

This reflects how contexts are *used* in derivations.  When working in a context, one doesn’t know (and doesn’t need to know) what order or earlier context the types were inserted in; one just extracts the variables and their types, as types over the current context itself.  The ordering/stratification is only needed for meta-theoretic constructions, and it can then be reconstructed from the typing derivation for the context. *)

Section RawContext.

  Context {σ : shape_system}.

  (** A raw context consists of a shape, and a raw syntactic type expression
     for each position of the shape. *)
  Record raw_context {Σ : signature σ}
  := { raw_context_carrier :> shape_carrier σ
     ; raw_context_type
         :> raw_context_carrier -> raw_type Σ raw_context_carrier
     }.

  Arguments raw_context _ : clear implicits.

  (** Functoriality in signature maps *)
  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : raw_context Σ -> raw_context Σ'.
  Proof.
    intros Γ.
    exists (raw_context_carrier Γ).
    intros i. refine (_ (raw_context_type Γ i)).
    apply (Expression.fmap f).
  Defined.

  (** The empty context. *)
  Local Definition empty {Σ : signature σ} : raw_context Σ.
  Proof.
    exists (shape_empty _).
    apply (empty_rect _ shape_is_empty).
  Defined.

  (** Extend a context by one slot of a given raw type. *)
  Local Definition extend {Σ} (Γ : raw_context Σ) (A : raw_type Σ Γ)
    : raw_context Σ.
  Proof.
    exists (shape_extend _ Γ).
    apply (plusone_rect _ _ (shape_is_extend _ _)).
    - refine (Expression.rename _ A).
      (* As we put the type into the context, we weaken it to live over the extended context. *)
    apply (plusone_inj _ _ (shape_is_extend _ _)).
    - intros i.
      refine (Expression.rename _ (Γ i)).
      apply (plusone_inj _ _ (shape_is_extend _ _)).
  Defined.

End RawContext.

Notation " [: :] " := (empty) (format "[: :]") : context_scope.
Notation " [: x ; .. ; z :] " :=
  (extend .. (extend (empty) x) .. z) : context_scope.
Open Scope context_scope.

Arguments raw_context {_} _.
Arguments Build_raw_context {_ _} _ _.

Section Typed_Renamings.
(** A _typed renaming_ between contexts is a function on their variables, respecting their types (up to literal syntactic equality). *)

  Context {σ : shape_system}.

  Definition respects_types {Σ : signature σ} (Γ Δ : raw_context Σ)
    (f : Γ -> Δ)
  := forall i:Γ, Δ (f i) = rename f (Γ i).

  Record typed_renaming {Σ : signature σ} (Γ Δ : raw_context Σ)
  := {
    map_of_typed_renaming :> Γ -> Δ
  ; typed_renaming_respects_types
    : respects_types Γ Δ map_of_typed_renaming
  }.

  Definition fmap_typed_renaming `{Funext}
      {Σ Σ' : signature σ}
      (f : Signature.map Σ Σ')
      {Γ Γ'} (α : typed_renaming Γ Γ')
    : typed_renaming (fmap f Γ) (fmap f Γ').
  Proof.
    exists (fun i : fmap f Γ => α i).
    intros i. cbn.
    eapply concat. { apply ap, typed_renaming_respects_types. }
    apply fmap_rename.
  Defined.

  Context `{Funext} {Σ : signature σ}.

  Lemma compose_respects_types
     {Γ Γ' Γ'': raw_context Σ}
     {f : Γ' -> Γ''} {g : Γ -> Γ'}
     (H_f : respects_types Γ' Γ'' f)
     (H_g : respects_types Γ Γ' g)
    : respects_types Γ Γ'' (f o g).
  Proof.
    intros i.
    eapply concat. { apply H_f. }
    eapply concat. { apply ap, H_g. }
    apply rename_rename.
  Defined.

  Definition compose_typed_renaming
     {Γ Γ' Γ'': raw_context Σ}
     (f : typed_renaming Γ' Γ'') (g : typed_renaming Γ Γ')
    : typed_renaming Γ Γ''.
  Proof.
    exists (f o g).
    apply compose_respects_types; apply typed_renaming_respects_types.
  Defined.

  Lemma respects_types_equiv_inverse
      (Γ Δ : raw_context Σ)
      (e : Γ <~> Δ)
    : respects_types Γ Δ e
    -> respects_types Δ Γ e^-1.
  Proof.
    intros H_e i.
    eapply concat. 2: { apply ap, ap, (eisretr e). }
    eapply concat. 2: { apply inverse, ap, H_e. }
    eapply concat. 2: { apply inverse, rename_rename. }
    eapply concat. { apply inverse, rename_idmap. }
    apply (ap (fun f => Expression.rename f _)).
    apply inverse, path_forall, (eissect e).
  Defined.

  Lemma typed_renaming_inverse
      {Γ Δ : raw_context Σ}
      (f : typed_renaming Γ Δ)
      (e_f : IsEquiv f)
    : typed_renaming Δ Γ.
  Proof.
    exists (@equiv_inv _ _ _ e_f).
    refine (respects_types_equiv_inverse _ _ (BuildEquiv _ _ _ _) _).
    apply typed_renaming_respects_types.
  Defined.

End Typed_Renamings.

Section Rename_Variables.
(** The action of variable-renaming on contexts (and, later, judgements) is a bit subtler than on expressions: one can only rename along an _isomorphism_ of shapes, not an arbitrary map of shapes.

  Precisely, given a raw context [Γ] and an _isomorphic_ shape [f : γ' <~> Γ], one can rename the variables of [Γ] according to [f], to get a raw context with shape [γ']; and similarly for judgements; and this will in each case preserve derivability/well-typedness.

  (NOTE: in fact this all works more generally for _retractions_ [f : γ' <~> Γ] of shapes, not just isomorphisms. However. we have no use-case for the more general version, so we give these for now just for the case of isomorphisms.) *)

  Context {σ : shape_system} {Σ : signature σ}.

  (** NOTE: arguments of [Context.rename] are in the opposite order from in renaming of expressions; this seems inevitable, unless we split up the context argument into shape and types separately, which would make this cumbersome to apply. *)
  Local Definition rename
      (Γ : raw_context Σ) {γ' : shape_carrier σ} (e : γ' <~> Γ)
    : raw_context Σ.
  Proof.
    exists γ'. 
    exact (fun j => Expression.rename (equiv_inverse e) (Γ (e j))).
  Defined.

  Definition typed_renaming_to_rename_context
      (Γ : raw_context Σ) {γ' : shape_carrier σ} (e : γ' <~> Γ)
    : typed_renaming Γ (rename Γ e).
  Proof.
    exists (equiv_inverse e : _ -> _).
    intros i; cbn.
    apply ap, ap, eisretr.
  Defined.

  Definition typed_renaming_from_rename_context `{Funext}
      (Γ : raw_context Σ) {γ' : shape_carrier σ} (e : γ' <~> Γ)
    : typed_renaming (rename Γ e) Γ.
  Proof.
    exists (e : _ -> _).
    intros i; cbn.
    eapply concat. { apply inverse, rename_idmap. }
    eapply concat. 2: { apply inverse, rename_rename. }
    refine (ap (fun f => Expression.rename f _) _).
    apply path_forall; intros ?; apply inverse, eisretr.
  Defined.

End Rename_Variables.

Section Instantiation.
(** Interaction with instantiation of metavariables. *)

  Context {σ : shape_system} `{Funext}.

  Local Definition instantiate
      {a : arity σ} {Σ : signature σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context (Metavariable.extend Σ a))
    : raw_context Σ.
  Proof.
     exists (shape_sum Γ Δ).
        apply (coproduct_rect shape_is_sum).
        + intros i.
          refine (Expression.rename _ (Γ i)).
          exact (coproduct_inj1 shape_is_sum).
        + intros i.
          exact (Metavariable.instantiate_expression I (Δ i)).
  Defined.

  Lemma respects_types_shape_sum_inl
    {Σ : signature σ} {a : arity σ}
    (Γ : raw_context Σ) (Δ : raw_context (Metavariable.extend Σ a))
    (I : Metavariable.instantiation a Σ Γ)
  : respects_types Γ (instantiate Γ I Δ)
                   (coproduct_inj1 shape_is_sum).
  Proof.
    intros i. refine (coproduct_comp_inj1 _).
  Defined.

  (* TODO: consider/consistentise naming of [repects_types_shape_sum_inl], [typed_renaming_to_instantiate_context]. *)
  Lemma typed_renaming_to_instantiate_context
      {Σ : signature σ} (Γ : raw_context Σ)
      {a : arity σ} 
      (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context (Metavariable.extend Σ a))
    : typed_renaming Γ (instantiate Γ I Δ).
  Proof.
    exists (coproduct_inj1 shape_is_sum).
    apply respects_types_shape_sum_inl.
  Defined.

  Local Definition fmap_instantiate
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {Γ : raw_context Σ} (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context (Metavariable.extend Σ a))
    : fmap f (instantiate Γ I Δ)
    = instantiate
        (fmap f Γ)
        (instantiation_fmap f I)
        (fmap (Metavariable.fmap1 f a) Δ).
  Proof.
    apply (ap (Build_raw_context _)), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _); intros i;
      unfold instantiate.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
      apply Expression.fmap_rename.
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
      apply fmap_instantiate_expression.
  Defined.

  Context {Σ : signature σ}.

  Lemma instantiate_typed_renaming
      (Γ : raw_context Σ) {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ Δ' : raw_context _} (f : typed_renaming Δ Δ')
    : typed_renaming (instantiate Γ I Δ) (instantiate Γ I Δ').
  Proof.
    exists (fmap2_shape_sum f).
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; cbn.
      unfold fmap2_shape_sum, fmap_shape_sum.
      repeat rewrite coproduct_comp_inj1.
      eapply concat. 2: { apply inverse, rename_rename. }
      apply (ap (fun f => Expression.rename f _)), path_forall.
      intros j. apply inverse; refine (coproduct_comp_inj1 _).
    - intros i; cbn.
      unfold fmap2_shape_sum, fmap_shape_sum.
      repeat rewrite coproduct_comp_inj2.
      eapply concat. { apply ap, typed_renaming_respects_types. }
      apply instantiate_rename. 
  Defined.

(* TODO: [unit_instantiate] should probably be deprecated in favour of the typed
renamings [shape_sum_empty_inl] and its inverse. *)
  Local Lemma unit_instantiate
      {a} (Γ : raw_context (Metavariable.extend Σ a))
    : instantiate [::] (unit_instantiation a)
        (fmap (Metavariable.fmap1 include_symbol _) Γ)
      = rename Γ (shape_sum_empty_inr _)^-1.
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

  Lemma respects_types_shape_sum_empty_inl_inverse
    {a} (Γ : raw_context Σ) (Δ : _)
    (I : Metavariable.instantiation a Σ Γ)
  : respects_types
      (instantiate Γ I (Build_raw_context _ Δ)) Γ
      (shape_sum_empty_inl Γ)^-1.
  Proof.
    apply respects_types_equiv_inverse, respects_types_shape_sum_inl.
  Defined.

  (** A slightly technical lemma, useful under [Judgement.eq_by_expressions]
    for the types of a context reindexed under [shape_sum_empty_inl]. *)
  Lemma instantiate_empty_ptwise
      (Γ : raw_context Σ)
      (f : shape_empty σ -> raw_type Σ _)
      (i : shape_sum Γ (shape_empty σ))
    : coproduct_rect (shape_is_sum) _
        (fun j:Γ => Expression.rename (shape_sum_empty_inl _) (Γ j))
        f i
    = rename Γ (shape_sum_empty_inl _)^-1 i.
  Proof.
    revert i. cbn.
    apply (coproduct_rect shape_is_sum).
    + intros ?.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      cbn. apply ap, ap.
      apply inverse. refine (coproduct_comp_inj1 _).
    + exact (empty_rect _ shape_is_empty _).
  Defined.

  Local Lemma instantiate_instantiate_pointwise
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (K : raw_context (Metavariable.extend Σ b))
    : forall i,
      instantiate
        (instantiate _ I Δ)
        (instantiate_instantiation I J) K i
    = rename
        (instantiate Γ I
          (instantiate Δ J
            (fmap (Metavariable.fmap1 include_symbol _) K)))
        (shape_assoc _ _ _)^-1
        i.
  Proof.
    repeat refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; cbn.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply rename_rename. }
      apply inverse.
      eapply concat.
      { apply ap.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      }
      eapply concat. { apply rename_rename. }
      refine (ap (fun f => Expression.rename f _) _).
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
      eapply concat. { apply rename_rename. }
      refine (ap (fun f => Expression.rename f _) _).
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
      refine ((ap (fun f => Expression.rename f _) _) @ ap _ _).
      + apply ap, inverse, einv_V. 
      + apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply ap. refine (coproduct_comp_inj2 _).
  Qed.

  Local Lemma instantiate_instantiate_rtol
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (Θ : raw_context (Metavariable.extend Σ b))
    : typed_renaming 
        (instantiate Γ I
          (instantiate Δ J
            (fmap (Metavariable.fmap1 include_symbol _) Θ)))
        (instantiate
          (instantiate _ I Δ)
          (instantiate_instantiation I J)
          Θ).
  Proof.
    exists shape_assoc_rtol; intros i.
    eapply concat. { apply (instantiate_instantiate_pointwise I J Θ). }
    apply (ap (Expression.rename _)), ap.
    apply eissect.
  Defined.

  Local Lemma instantiate_instantiate_ltor
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (Θ : raw_context (Metavariable.extend Σ b))
    : typed_renaming 
        (instantiate
          (instantiate _ I Δ)
          (instantiate_instantiation I J)
          Θ)
        (instantiate Γ I
          (instantiate Δ J
            (fmap (Metavariable.fmap1 include_symbol _) Θ))).
  Proof.
    exists shape_assoc_ltor.
    refine (respects_types_equiv_inverse
             (instantiate _ _ (instantiate _ _ (fmap _ _)))
             (instantiate (instantiate _ _ _) _ Θ)
             (shape_assoc _ _ _)
             _).
    exact
      (typed_renaming_respects_types _ _ (instantiate_instantiate_rtol _ _ _)).
  Defined.

  (* TODO: possible alternate name [Context.instantiate_rename_instantiation]. *)
  Lemma instantiate_context_over_typed_renaming
        {Γ Γ' : raw_context Σ} (f : typed_renaming Γ Γ')
        {a : arity σ} 
        (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
        (Δ : raw_context (Metavariable.extend Σ a))
    : typed_renaming
        (instantiate Γ I Δ)
        (instantiate Γ' (rename_instantiation f I) Δ).
  Proof.
    exists (Coproduct.fmap shape_is_sum shape_is_sum f idmap).
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros x.
      cbn; unfold Coproduct.fmap.
      repeat rewrite coproduct_comp_inj1.
      eapply concat. { apply ap, typed_renaming_respects_types. }
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply inverse, rename_rename. }
      apply (ap (fun r => Expression.rename r _)).
      apply path_forall; intros i; cbn.
      apply inverse. refine (coproduct_comp_inj1 _).
    - intros x. unfold Coproduct.fmap; cbn.
      repeat rewrite coproduct_comp_inj2.
      apply instantiate_rename_instantiation.
  Defined.

End Instantiation.

Arguments instantiate : simpl nomatch.
