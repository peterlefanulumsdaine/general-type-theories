(** * The congruence rules associated with a given rule *)

From HoTT Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.AlgebraicExtension.
Require Import Presented.PresentedRawRule.

Section CongruenceRule.

  Context {σ : scope_system}.
  Context {Σ : signature σ}.

  Local Definition original_premise {obs eqs : arity σ}
    : (obs + obs) + (eqs + eqs + obs) -> (obs + eqs).
  Proof.
    intros p ; repeat destruct p as [p | p];
      try exact (inl p); exact (inr p).
  Defined.

  Arguments original_premise : simpl nomatch.

  (* The ordering of premises of the congruence rule associated to an object rule. *)
  Local Definition lt
      {obs eqs : Type} (lt : well_founded_order (obs + eqs))
    : well_founded_order ((obs + obs) + (eqs + eqs + obs)).
  Proof.
    refine (WellFounded.pullback _ (semi_reflexive_product lt Span.lt)).
    intros [ [ ob_l | ob_r ] | [ [ eq_l | eq_r ] | eq_new ] ].
    + exact (inl ob_l, Span.left).
    + exact (inl ob_r, Span.right).
    + exact (inr eq_l, Span.left).
    + exact (inr eq_r, Span.right).
    + exact (inl eq_new, Span.top).
  Defined.

  Local Arguments lt : simpl nomatch.

  (*  Unwinding this definition, the relation is be defined as follows:

           ob_l j   ob_r j   eq_l j   eq_r j   eq_new j

ob_l i     i < j    0        i < j    0        i ≤ j

ob_r i     0        i < j    0        i < j    i ≤ j

eq_l i     i < j    0        i < j    0        i < j

eq_r i     0        i < j    0        i < j    i < j

eq_new i   0        0        0        0        i < j

*)

  Local Definition original_constructor_translation
    {a} {jf_concl} (R : rule Σ a jf_concl)
    (p : (a + a)
         + (ae_equality_premise (rule_premise R)
            + ae_equality_premise (rule_premise R)
            + a))
    : Signature.map
        (ae_signature_of_premise (original_premise p))
        (Metavariable.extend Σ (Family.subfamily (a + a)
           (fun j => lt (ae_lt) (inl j) p))).
  Proof.
    (* In case [p] is one of the 2 copies of the original premises, there is a single canonical choice for this definition.

    In case [p] is one of the new equality premises (between the 2 copies of the old equality premises), there are in principle 2 possibilities; it should make no difference which one chooses. *)
    apply Metavariable.fmap2.
    simple refine (_;_).
    - intros q.
      destruct p as [ [ pob_l | pob_r ] | [ [ peq_l | peq_r ] | peq_new ] ].
      + (* pob_l *)
        exists (inl (pr1 q)).
        apply inr; cbn. split; try apply idpath. exact (pr2 q).
      + (* pob_r *)
        exists (inr (pr1 q)).
        apply inr; cbn. split; try apply idpath. exact (pr2 q).
      + (* peq_l *)
        exists (inl (pr1 q)).
        apply inr; cbn. split; try apply idpath. exact (pr2 q).
      + (* peq_r *)
        exists (inr (pr1 q)).
        apply inr; cbn. split; try apply idpath. exact (pr2 q).
      + (* peq_new *)
        exists (inr (pr1 q)). (* note both [inl], [inr] make this work *)
        apply inl, inl; cbn. split; try constructor. exact (pr2 q).
    - intros q.
      repeat destruct p as [ p | p ]; apply idpath.
  Defined.

  Definition congruence_rule
    {a} {jf_concl} (R : rule Σ a jf_concl)
    (H : Judgement.is_object jf_concl)
    (S : Σ)
    (e_a : symbol_arity S = a)
    (e_cl : symbol_class S = class_of jf_concl)
    : (rule Σ (Family.sum a a)
                 (form_equality (class_of jf_concl))).
  Proof.
    (* TODO: refactor the following, to unify it with def of raw congruence
       rules (once given). *)
    simple refine (Build_rule _ _ _ _ _).
    1: simple refine
           {| ae_equality_premise :=
                 ((ae_equality_premise (rule_premise R)) +
                 (ae_equality_premise (rule_premise R))) + a ;
              |}.
    - (* ae_lt *)
      exact (lt (ae_lt)).
    - (* ae_raw_context_type *)
      intros p i.
      refine (Expression.fmap
        (original_constructor_translation _ _) _).
      set (p_orig := original_premise p).
      recursive_destruct p;
      refine (ae_raw_context_type p_orig i).
      (* alternatively, instead of destructing [p], could use equality reasoning
      on the type of [i]. *)
    - (* ae_hypothetical_boundary *)
      intros p.
      set (p_orig := original_premise p).
      recursive_destruct p;
        try (refine (Judgement.fmap_hypothetical_boundary_expressions
          (original_constructor_translation _ _) _) ;
             refine (ae_hypothetical_boundary_expressions _ p_orig)).
      (* The cases where [p] is a copy of an original premise are all just translation,
      leaving just the new equality premises to give. *)
      intros i; simpl Judgement.boundary_slot in i.
      destruct i as [ i | | ]; [ idtac | simpl | simpl].
      + (* boundary of the corresponding original premise *)
        refine (Expression.fmap
          (original_constructor_translation _ _) _).
        apply (ae_hypothetical_boundary_expressions _ p_orig).
      + (* LHS of new equality premise *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_metavariable.
          refine (inl _; _).
          cbn. apply inl, inr; split; constructor.
        * apply idpath.
        * intros i.
          apply raw_variable, (coproduct_inj1 scope_is_sum), i.
      + (* RHS of new equality premise *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_metavariable.
          refine (inr _; _).
          cbn. apply inl, inr; split; constructor.
        * apply idpath.
        * intros i.
          apply raw_variable, (coproduct_inj1 scope_is_sum), i.
    - (* rule_conclusion_hypothetical_boundary *)
      intros [ i | | ]; simpl.
      + (* boundary of original conclusion *)
        refine (Expression.fmap _ _).
        * apply Metavariable.fmap2, Family.inl.
        * destruct jf_concl as [cl | ?].
          -- exact (rule_conclusion_hypothetical_boundary_expressions R i).
          -- destruct H. (* know [jf_concl] isn’t an equality judgement *)
      + (* LHS of new conclusion *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_symbol, S.
        * apply e_cl.
        * simpl symbol_arity.
          change (symbol_arity (Metavariable.include_symbol_carrier S))
            with (symbol_arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (raw_symbol' _ _ _).
          -- apply Metavariable.include_metavariable.
             exact (inl p).
          -- apply idpath.
          -- cbn. intros i.
             apply raw_variable.
             apply (coproduct_inj1 scope_is_sum).
             apply (coproduct_inj2 scope_is_sum).
             exact i.
      + (* RHS of new conclusion *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_symbol, S.
        * apply e_cl.
        * simpl symbol_arity.
          change (symbol_arity (Metavariable.include_symbol_carrier S))
            with (symbol_arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (raw_symbol' _ _ _).
          -- apply Metavariable.include_metavariable.
             exact (inr p).
          -- apply idpath.
          -- cbn. intros i.
             apply raw_variable.
             apply (coproduct_inj1 scope_is_sum).
             apply (coproduct_inj2 scope_is_sum).
             exact i.
  Defined.
  (* TODO: the above is a bit unreadable.  An alternative approach that might be clearer and more robust:
   - factor out the constructions of the head terms of conclusions and premises from [flatten], if doable.
   - here, invoke those, but (for the LHS/RHS of the new equalities), translate them under appropriate context morphisms “inl”, “inr”. *)

(* A good test proposition will be the following: whenever a rule is well-typed, then so is its associated congruence rule. *)

End CongruenceRule.
