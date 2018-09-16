Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.Arity.
Require Import RawSyntax.Signature.
Require Import RawSyntax.Expression.
Require Import RawSyntax.Substitution.
Require Import RawSyntax.Metavariable.

Section RawContext.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* A raw context is a shape and a raw syntactic type expression for each position in
     the shape. *)
  Record raw_context
    := { raw_context_carrier :> shape_carrier σ
       ; raw_context_type :> raw_context_carrier -> raw_type Σ raw_context_carrier
       }.

  (** The empty context. *)
  Local Definition empty : raw_context.
  Proof.
    exists (shape_empty _).
    apply (empty_rect _ shape_is_empty).
  Defined.

  (** Extend a context by one slot of a given raw type. *)
  Local Definition extend (Γ : raw_context) (A : raw_type Σ Γ)
    : raw_context.
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

Global Arguments raw_context {_} _.

Section Signature_Maps.

  Context {σ : shape_system}.

  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : raw_context Σ -> raw_context Σ'.
  Proof.
    intros Γ.
    exists (raw_context_carrier Γ).
    intros i. refine (_ (raw_context_type Γ i)).
    apply (Expression.fmap f).
  Defined.


End Signature_Maps.

Section Rename_Variables.
(** The action of variable-renaming on contexts (and, later, judgements) is a bit subtler than on expressions: one can only rename an _isomorphism_ of shapes, not an arbitrary map.

  Precisely, given a raw context [Γ] and an _isomorphic_ shape [f : γ' <~> Γ], one can rename the variables of [Γ] according to [f], to get a raw context with shape [γ']; and similarly for judgements; and this will in each case preserve derivability/well-typedness.

  (NOTE: in fact this all seems to make sense more generally for _retractions_ [f : γ' <~> Γ] of shapes, not just isomorphisms. However. we have no use-case for the more general version, so we give these for now just for the case of isomorphisms.) *)

  Context {σ : shape_system} {Σ : signature σ}.

  (** NOTE: arguments of this are in the opposite order from in renaming of expressions; this is inevitable, unless we split up the context argument into shape and types separately, which would make this cumbersome to apply. *)
  Local Definition rename
      (Γ : raw_context Σ) {γ' : shape_carrier σ} (f : γ' <~> Γ)
    : raw_context Σ.
  Proof.
    exists γ'. 
    exact (fun j => rename (equiv_inverse f) (Γ (f j))).
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

  Local Definition fmap_instantiate
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {Γ : raw_context Σ} (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context (Metavariable.extend Σ a))
    : fmap f (instantiate Γ I Δ)
    = instantiate
        (fmap f Γ)
        (fmap_instantiation f I)
        (fmap (Metavariable.fmap1 f a) Δ).
  Proof.
    apply (ap (Build_raw_context _)), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _); intros i;
      unfold instantiate.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
      apply fmap_rename.
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
      apply fmap_instantiate_expression.
  Defined.

End Instantiation.

Arguments instantiate : simpl nomatch.
