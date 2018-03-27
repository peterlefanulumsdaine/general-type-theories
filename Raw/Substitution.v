Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Raw.Presyntax.
Require Import Raw.Expression.

Section RawSubstitution.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* A raw substitution takes positions in one shape to raw terms over another shape. *)
  Definition raw_substitution (γ δ : σ)
    := δ -> raw_term Σ γ.

  (* We first define a substitution which just replaces variables for variables.
     This notion simultaneously subsumest weakening, contraction, and exchange. *)
  Local Fixpoint rename {γ γ' : σ} (f : γ -> γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : raw_expression Σ cl γ'.
  Proof.
    destruct e as [ γ i | γ S args ].
  - exact (raw_variable (f i)).
  - refine (raw_symbol S _). intros i.
    refine (rename _ _ _ _ (args i)).
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn.
    + intros x. apply (coproduct_inj1 (shape_is_sum)). exact (f x).
    + intros x. apply (coproduct_inj2 (shape_is_sum)). exact x.
  Defined.

  (* A substitution from [γ] to [γ'] may be extended to one from [γ + δ] to [γ' + δ]. *)
  Local Definition extend (γ γ' δ : σ)
    : raw_substitution γ' γ -> raw_substitution (shape_sum γ' δ) (shape_sum γ δ).
  Proof.
    intros f.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn.
    - intros i.
      refine (rename _ (f i)).
      apply (coproduct_inj1 (shape_is_sum)).
    - intros i.
      apply raw_variable.
      apply (coproduct_inj2 (shape_is_sum)), i.
  Defined.

  (* Apply a raw substitution to a raw expression. *)
  Fixpoint substitute
      {γ δ : σ} (f : raw_substitution δ γ)
      {cl : syntactic_class}
      (e : raw_expression Σ cl γ)
    : raw_expression Σ cl δ.
  Proof.
    destruct e as [ γ i | γ S args ].
    - exact (f i).
    - refine (raw_symbol S _). intros i.
      refine (substitute _ _ _ _ (args i)).
      apply extend. exact f.
  Defined.

End RawSubstitution.

Arguments rename {_ _ _ _} _ {_} _.
