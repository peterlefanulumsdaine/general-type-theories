Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Raw.Signature.
Require Import Raw.Expression.
Require Import Raw.Substitution.

Section RawContext.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* A raw context is a shape and a raw syntactic type expression for each position in
     the shape. *)
  Record raw_context
    := { raw_context_carrier :> shape_carrier σ
       ; raw_context_type :> raw_context_carrier -> raw_type Σ raw_context_carrier
       }.

  Local Definition map Σ (γ δ : σ)
    := δ -> raw_term Σ γ.

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
    - refine (Substitution.rename _ A).
      (* As we put the type into the context, we weaken it to live over the extended context. *)
    apply (plusone_inj _ _ (shape_is_extend _ _)).
    - intros i.
      refine (Substitution.rename _ (Γ i)).
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

  (* TODO: consider naming of this.  Perhaps put this and similar things into a module [Map] in this file, so it can be e.g. [Context.Map.fmap] ?  *)
  Definition fmap_raw_context_map
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {γ γ'} (g : map Σ γ' γ)
    : map Σ' γ' γ
  := fun i => (Expression.fmap f (g i)).

End Signature_Maps.