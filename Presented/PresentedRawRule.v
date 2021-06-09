(** * Well-scoped rules *)

Require Import HoTT.HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.AlgebraicExtension.
Require Import Typing.RawRule.

(** A well-scoped rule is given by the following data:

   - [rule]: the data one gives to specify a logical rule (before any typechecking)
   - [associated_congruence_rule]
   - [flatten]
*)

(** Specification of well-scoped rules *)
Section WellScopedRule.

Context {σ : scope_system}.

(** An (ordered, raw) rule consists of premises and a conclusion. For various
    reasons, we abstract the form of the premises as an _algebraic extension_.

    Such an extension can add both object premises (introducing type/term
    premises) and equality premises.

    Besides being viewed as the premises of a rule, the premises can be seen as
    particularly simple rules themselves for extending a type theory. Viewed
    this way, they are _algebraic_ in the sense that it does not introduce any
    new binders, and only take term arguments (no type arguments). This is the
    raw-syntax analogue of an arity seen as specifying the metavariable-extension
    of a signature.
*)

(** The parameters of a rule, beyond its ambient signature, may be a little
    counter-intuitive. The point is that they are just what is required to
    determine the arity of the symbol introduced by the rule (if it’s an object
    rule), and in any case the arity of its associated raw rule. *)
Record rule
  {Σ : signature σ}
  {a : arity σ}
    (* arity listing the _object_ premises of the rule *)
  {jf_conclusion : Judgement.form}
    (* judgement form of the conclusion *)
:=
  {
    rule_premise : algebraic_extension Σ a
  ; rule_conclusion_hypothetical_boundary_expressions
      : Judgement.hypothetical_boundary_expressions
          (Metavariable.extend Σ a)
          jf_conclusion
          (scope_empty σ)
  }.

(* NOTE 1. One could generalise rules by allowing the context of the conclusion to be non-empty.

 This would slightly complicate this definition, and subsequent constructions, and would (one expects) not add any real generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context (where the equivalence makes use of the “cut”/substitution rule).

  However, it could be nice (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about it being equivalent to move variables into the premises.

  On the other hand, so long as the _flattened_ rules [raw_rule] allow arbitrary conclusion judgements, one can still use those to give a lemma about the equivalence. *)

  (* NOTE 2. Perhaps the parameters of the definition of [rule] could be profitably abstracted into a “proto-rule” (probably including also the arity [ae_equality_premise]), fitting the pattern of the stratificaiton of objects into proto ≤ raw ≤ typed. *)

  Arguments rule _ _ _ : clear implicits.

  Local Definition conclusion_boundary_expressions
        {Σ} {a} {jf} (R : rule Σ a jf)
    : hypothetical_boundary_expressions
        (Metavariable.extend Σ a) jf (scope_empty σ)
  := rule_conclusion_hypothetical_boundary_expressions R.

  Local Lemma eq
      {Σ} {a} {jf_concl} (R R' : rule Σ a jf_concl)
      (e_prem : rule_premise R = rule_premise R')
      (e_concl : rule_conclusion_hypothetical_boundary_expressions R
                 = rule_conclusion_hypothetical_boundary_expressions R')
    : R = R'.
  Proof.
    destruct R'; simpl in *.
    destruct e_prem, e_concl.
    apply idpath.
  Defined.

  Local Definition fmap
      {Σ} {Σ'} (f : Signature.map Σ Σ')
      {a} {jf_concl}
      (R : rule Σ a jf_concl)
    : rule Σ' a jf_concl.
  Proof.
    simple refine (Build_rule Σ' a jf_concl _ _).
    - (* premises *)
      exact (AlgebraicExtension.fmap f (rule_premise R)).
    - (* conclusion *)
      simple refine
        (fmap_hypothetical_boundary_expressions
          _ (rule_conclusion_hypothetical_boundary_expressions R)).
      apply Metavariable.fmap1, f.
  Defined.

  Context `{Funext}.

  Local Definition fmap_idmap
      {Σ} {a} {jf_concl} (R : rule Σ a jf_concl)
    : fmap (Signature.idmap _) R = R.
  Proof.
    apply eq.
    - apply AlgebraicExtension.fmap_idmap.
    - cbn.
      eapply concat.
      { eapply (ap_3back fmap_hypothetical_boundary_expressions).
        apply Metavariable.fmap1_idmap. }
      apply fmap_hypothetical_boundary_expressions_idmap.
  Defined.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {a} {jf_concl} (R : rule Σ a jf_concl)
    : fmap (Signature.compose f' f) R = fmap f' (fmap f R).
  Proof.
    apply eq.
    - apply AlgebraicExtension.fmap_compose.
    - cbn.
      eapply concat.
      { eapply (ap_3back fmap_hypothetical_boundary_expressions).
        apply Metavariable.fmap1_compose. }
      apply fmap_hypothetical_boundary_expressions_compose.
  Defined.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {a} {jf_concl} (R : rule Σ a jf_concl)
    : fmap f' (fmap f R) = fmap (Signature.compose f' f) R.
  Proof.
    apply inverse, fmap_compose.
  Defined.

  Local Lemma conclusion_boundary_expressions_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {jf_concl} (R : rule Σ a jf_concl)
    : conclusion_boundary_expressions (fmap f R)
      = fmap_hypothetical_boundary_expressions (Metavariable.fmap1 f a)
                                        (conclusion_boundary_expressions R).
  Proof.
    apply idpath.
  Defined.

  (** Auxiliary access functions *)
  Local Definition conclusion_hypothetical_boundary
        {Σ} {a} {jf} (R : rule Σ a jf)
    : hypothetical_boundary
        (Metavariable.extend Σ a) (scope_empty σ)
  := Build_hypothetical_boundary _
        (rule_conclusion_hypothetical_boundary_expressions R).

  Local Definition conclusion_hypothetical_boundary_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {jf_concl} (R : rule Σ a jf_concl)
    : conclusion_hypothetical_boundary (fmap f R)
      = fmap_hypothetical_boundary (Metavariable.fmap1 f a)
                                        (conclusion_hypothetical_boundary R).
  Proof.
    apply idpath.
  Defined.

  Local Definition conclusion_boundary
        {Σ} {a} {jf} (R : rule Σ a jf)
    : boundary (Metavariable.extend Σ a)
  := Build_boundary [::] (conclusion_hypothetical_boundary R).

  Local Definition conclusion_boundary_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {jf} (R : rule Σ a jf)
    : conclusion_boundary (fmap f R)
      = Judgement.fmap_boundary (Metavariable.fmap1 f a)
                                (conclusion_boundary R).
  Proof.
    apply (ap (fun Γ
                  => Build_boundary
                      (Build_raw_context _ Γ) _)).
    apply path_forall; refine (empty_rect _ scope_is_empty _).
  Defined.

End WellScopedRule.

(* globalise argument declarations *)
Arguments rule {_} _ _ _.

Module Span.
(** Some auxiliary constructions for defining the ordering of the premises in
    the associated congruence rule of a constructor. *)

  Inductive span : Type :=
    left | right | top.

  Local Definition lt_relation : Relation span
  := fun x y => match x, y with
                | left, top => True
                | right, top => True
                | _, _ => False
  end.

  Definition lt_well_founded : is_well_founded lt_relation.
  Proof.
    intros P P_hereditary.
    assert (Pl : P left). { apply P_hereditary. intros [ | | ] []. }
    assert (Pr : P right). { apply P_hereditary. intros [ | | ] []. }
    intros [ | | ]; try assumption.
    apply P_hereditary. intros [ | | ] left; try assumption; destruct left.
  Defined.

  Definition lt_transitive : Transitive lt_relation.
  Proof.
    intros [ | | ] [ | | ] [ | | ] l l'; destruct l, l'; exact tt.
  Defined.

  Definition lt : well_founded_order span.
  Proof.
    exists lt_relation.
    - apply lt_well_founded.
    - apply lt_transitive.
  Defined.

End Span.


(* Each (ordered) rule induces one or two raw rules: the logical rule itself,
   and (if it was an object rule) its associated congruence rule.*)

Section Flattening.

  Context {σ : scope_system}.
  Context {Σ : signature σ}.

  (* TODO: consider whether this can be unified with [judgement_of_premise] *)
  Local Definition judgement_of_conclusion
    {a} {jf_concl}
    (R : rule Σ a jf_concl)
    (Sr : Judgement.is_object jf_concl
          -> { S : Σ & (symbol_arity S = a)
                       * (symbol_class S = class_of jf_concl) })
      : judgement (Metavariable.extend Σ a).
  Proof.
    exists [::], jf_concl.
    apply hypothetical_judgement_expressions_from_boundary_and_head.
    - exact (conclusion_boundary_expressions R).
    - intros H_obj.
      destruct jf_concl as [ ocl | ecl ]; simpl in *.
      + (* case: R an object rule *)
        destruct (Sr tt) as [S_R [e_a e_cl]]. clear Sr H_obj.
        destruct e_cl. (* TODO: can we simplify here with [raw_symbol']? *)
        refine (raw_symbol (inl S_R : Metavariable.extend _ _) _).
        change (symbol_arity (inl S_R : Metavariable.extend _ _))
          with (symbol_arity S_R).
        set (aR := symbol_arity S_R) in *. destruct (e_a^); clear e_a.
        intros p.
        cbn in p.
        refine (raw_symbol (inr p : Metavariable.extend _ _) _).
        intros i.
        apply raw_variable.
        apply (coproduct_inj1 scope_is_sum).
        exact (coproduct_inj2 scope_is_sum i).
      + (* case: R an equality rule *)
        destruct H_obj. (* ruled out by assumption *)
  Defined.

  (* Flattening a rule requires no extra information in the case of an
  equality-rule; in the case of an object-rule, it requires a symbol of
  appropriate arity to give the object introduced. *)
  Local Definition flatten
    {a} {jf_concl}
    (R : rule Σ a jf_concl)
    (SR : Judgement.is_object jf_concl
        -> { S : Σ & (symbol_arity S = a)
                     * (symbol_class S = Judgement.class_of jf_concl) })
  : raw_rule Σ.
  (* This construction involves essentially two aspects:

     - translate the syntax of each expression in the rule from its “local”
       signatures to the overall signature;

     - reconstruct the head terms of the object premises and the conclusion *)
  Proof.
    exists a.
    - exact (AlgebraicExtension.flatten (rule_premise R)).
    - exact (judgement_of_conclusion R SR).
  Defined.

End Flattening.
