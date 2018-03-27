Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Raw.Presyntax.
Require Import Raw.Expression.
Require Import Raw.Context.
Require Import Raw.Substitution.
Require Import Raw.Judgement.

Section AlgebraicExtension.

  (* The extension of a signature by symbols representing metavariables, as used to write
     each rule.

     The *arity* here would be the overall argument of the constructor that the rule
     introduces: the metavariable symbols introduced correspond to the arguments of the
     arity.

     E.g. lambda-abstraction has arity < (Ty,•), (Ty,{x}), (Tm,{x}) >. So in the
     metavariable extension by this arity, we add three symbols — call them A, B, and b —
     with arities as follows:

     Symbol Class Arity A Ty < > B Ty <(Tm,•)> b Tm <(Tm,•)>

     allowing us to write expressions like x:A |– b(x) : B(x).
   *)

  Context {σ : shape_system}.

  Local Definition extend (Σ : signature σ) (a : @arity σ) : signature σ.
  Proof.
    refine (Family.sum Σ _).
    refine (Family.fmap _ a).
    intros cl_γ.
    exact (fst cl_γ, simple_arity (snd cl_γ)).
  Defined.

  Definition include_metavariable {Σ : signature σ} {a : @arity σ}
    : a -> extend Σ a
  := inr.

  Definition include_symbol {Σ : signature σ} {a : @arity σ}
    : Σ -> extend Σ a
  := inl.

  (* To use rules, one *instantiates* their metavariables, as raw syntax of the ambient
     signature, over some context. *)
  Local Definition instantiation (a : @arity σ) (Σ : signature σ) (γ : σ)
    : Type
    := forall i : a,
         raw_expression Σ (argument_class i) (shape_sum γ (argument_shape i)).

  (* Given such an instantiation, one can translate syntax over the extended signature
     into syntax over the base signature. *)
  Local Definition instantiate_expression
      {cl} {a : @arity σ} {Σ : signature σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
    : raw_expression Σ cl (shape_sum γ δ).
  Proof.
    induction e as [ δ i | δ [S | M] args inst_arg ].
  - refine (raw_variable _).
    exact (coproduct_inj2 (shape_is_sum) i).
  - refine (raw_symbol S _). intros i.
    refine (Substitution.rename _ (inst_arg i)).
    apply (Coproduct.assoc
             shape_is_sum shape_is_sum
             shape_is_sum shape_is_sum).
  - simpl in M. (* Substitute [args] into the expression [I M]. *)
    refine (substitute _ (I M)).
    refine (coproduct_rect shape_is_sum _ _ _).
    + intros i. apply raw_variable, (coproduct_inj1 shape_is_sum), i.
    + intros i.
      refine (Substitution.rename _ (inst_arg i)). cbn.
      refine (Coproduct.fmap shape_is_sum shape_is_sum _ _).
      exact (fun j => j).
      exact (Coproduct.empty_right shape_is_sum shape_is_empty).
  Defined.

  Local Definition instantiate_type := @instantiate_expression class_type.
  Local Definition instantiate_term := @instantiate_expression class_term.

  Global Arguments instantiate_expression {_ _ _ _} _ [_] _.
  Global Arguments instantiate_type {_ _ _} _ [_] _.
  Global Arguments instantiate_term {_ _ _} _ [_] _.

  Local Definition instantiate_context
      {a : @arity σ} {Σ : signature σ} {Γ : raw_context Σ}
      (I : instantiation a Σ Γ)
      (Δ : raw_context (extend Σ a))
    : raw_context Σ.
  Proof.
     exists (shape_sum Γ Δ).
        apply (coproduct_rect shape_is_sum).
        + intros i.
          refine (Substitution.rename _ (Γ i)).
          exact (coproduct_inj1 shape_is_sum).
        + intros i.
          exact (instantiate_type I (Δ i)).
  Defined.

  Local Definition instantiate_judgement
      {a : @arity σ} {Σ : signature σ} {Γ : raw_context Σ}
      (I : instantiation a Σ Γ)
      (e : judgement_total (extend Σ a))
    : judgement_total Σ.
  Proof.
    destruct e as [jf jfi]. exists jf ; destruct jf ; simpl in *.
    - apply (instantiate_context I). assumption.
    - destruct jfi as [Δ hjfi].
      simple refine (existT _ _ _).
      + apply (instantiate_context I).
        assumption.
      + simpl.
        intro i.
        apply (instantiate_expression I (hjfi i)).
  Defined.

End AlgebraicExtension.

Section MetavariableNotations.

(* Arities of symbols will arise in two ways:

  1. Arities we write by hand.

    These will typically use [< … >] notation.

  2. Arities of metavariables, from [Metavariable.extend].

    These will have only (Ty, shape_empty) arguments, and be indexed by the positions of some protocxt, which will itself probably be built up by [shape_extend].

  So we give functions/notations for giving arguments for each of these forms.

  Eventually, one should be able to write e.g.

  [S/ A ; e1 , e2 , e3 /]

  [M/ A ; e1 , e2 , e3 /]

  for the expression consisting of a symbol S (resp. a metavariable symbol M) applied to expressions e1, e2, e3.

  For now we provide the [M/ … /] version, but not yet the general [S/ … /] version.
*)

Context {σ : shape_system}.
Context {Σ : signature σ}.

Local Definition empty_args {γ}
  : arguments Σ (simple_arity (shape_empty _)) γ
  := empty_rect _ shape_is_empty _.

Local Definition extend_args {γ δ : σ}
  : arguments Σ (simple_arity δ) γ
    -> raw_term Σ γ
    -> arguments Σ (simple_arity (shape_extend _ δ)) γ.
Proof.
  intros ts t.
  simple refine (plusone_rect _ _ (shape_is_extend _ δ) _ _ _); cbn.
  - refine (Substitution.rename _ t).
    exact (coproduct_inj1 shape_is_sum).
  - exact ts.
Defined.

End MetavariableNotations.

Notation " '[M/' A /] " := (raw_symbol (include_metavariable A) empty_args) : syntax_scope.

Notation " '[M/' A ; x , .. , z /] "
  := (raw_symbol (include_metavariable A) (extend_args .. (extend_args (empty_args) x) .. z)) : raw_syntax_scope.

Open Scope syntax_scope.

