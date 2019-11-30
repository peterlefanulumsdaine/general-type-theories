
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