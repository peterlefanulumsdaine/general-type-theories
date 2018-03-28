Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMap.

(** In this file:

- [rule]: the data one gives to specify a logical rule (before any typechecking)
- [associated_congruence_rule]
- [flatten]
*)

(** Specification of “well-shaped” rules *)
Section Rule.

Context {σ : shape_system}.

(* An (ordered, raw) rule consists of premises and a conclusion.  For various reasons, we abstract the form of the premises as an _algebraic extension_.

Such an extension can add both object premises (introducing type/term premises) and equality premises.

Besides being viewed as the premises of a rule, the premises can be seen as particularly simple rules themselves for extending a type theory.  Viewed this way, they are _algebraic_ in the sense that it does not introduce any new binders, and only take term arguments (no type arguments). This is the raw-syntax analogue of an arity seen as specifying the metavariable-extension of a signature. *)
Record algebraic_extension
  {Σ : signature σ}
  {a : arity σ} (* arity listing the _object_ premises of the extension *)
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    ae_equality_premise : arity σ
  (* family indexing the premises of the extension, and giving for each… *)
  ; ae_premise :> family (Judgement.hypothetical_form * σ)
    := Family.sum
         (Family.fmap (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)) a)
         (Family.fmap (fun cl_γ => (form_equality (fst cl_γ), snd cl_γ)) ae_equality_premise)
  (* - the judgement form of each premise, e.g. “term” or “type equality” *)
  ; ae_hjf_of_premise : ae_premise -> Judgement.hypothetical_form
    := fun i => fst (ae_premise i)
  (* - the proto-context of each premise *)
  ; ae_proto_cxt_of_premise : ae_premise -> σ
    := fun i => snd (ae_premise i)
  (* the ordering relation on the premises *)
  ; ae_lt : well_founded_order ae_premise
  (* for each premise, the arity specifying what metavariables are available in the syntax for this premise; i.e., the family of type/term arguments already introduced by earlier premises *)
  ; ae_arity_of_premise : ae_premise -> arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  (* syntactic part of context of premise *)
  (* NOTE: this should never be used directly, always through [ae_raw_context_of_premise] *)
  ; ae_context_expr_of_premise
    : forall (i : ae_premise) (v : ae_proto_cxt_of_premise i),
        raw_type
          (Metavariable.extend Σ (ae_arity_of_premise i))
          (ae_proto_cxt_of_premise i)
  (* raw context of each premise *)
  ; ae_raw_context_of_premise
    : forall i : ae_premise,
        raw_context (Metavariable.extend Σ (ae_arity_of_premise i))
    := fun i => Build_raw_context _ (ae_context_expr_of_premise i)
  (* hypothetical judgement boundary instance for each premise *)
  ; ae_hyp_bdry_of_premise
    : forall i : ae_premise,
        Judgement.hypothetical_boundary
          (Metavariable.extend Σ (ae_arity_of_premise i))
          (ae_hjf_of_premise i)
          (ae_proto_cxt_of_premise i)
  }.

Arguments algebraic_extension _ _ : clear implicits.

(* The parameters of a rule, beyond its ambient signature, may be a little counter-intuitive.  The point is that they are just what is required to determine the arity of the symbol introduced by the rule, if it’s an object rule. *)
Record rule
  {Σ : signature σ}
  {a : arity σ} (* arity listing the _object_ premises of the rule *)
  {hjf_conclusion : Judgement.hypothetical_form} (* judgement form of the conclusion *)
:=
  {
    premise : algebraic_extension Σ a
  (* hyp judgement boundary instance of conclusion: *)
  ; hyp_judgt_bdry_of_conclusion
      : Judgement.hypothetical_boundary
          (Metavariable.extend Σ a)
          hjf_conclusion
          (shape_empty σ)
  }.

(* NOTE 1. One could generalise rule-specs by allowing the context of the conclusion to be non-empty.

 This would slightly complicate this definition, and subsequent constructions, and would (one expects) not add any real generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context (where the equivalence makes use of the “cut”/substitution rule).

  However, it could be nice (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about it being equivalent to move variables into the premises.

  On the other hand, so long as the _flattened_ rules [flat_rule] allow arbitrary conclusion judgements, one can still use those to give a lemma about the equivalence. *)

  (* NOTE 2. Perhaps the parameters of the definition of [rule] could be profitably abstracted into a “proto-rule-spec” (probably including also the arity [ae_equality_premise]), fitting the pattern of the stratificaiton of objects into proto ≤ raw ≤ typed. *)

  Arguments rule _ _ _ : clear implicits.

  (* Template for defining rule-specs: *)
  Definition Example {Σ} {a} {hjf} : rule Σ a hjf.
  Proof.
    simple refine (Build_rule _ _ _ _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - admit. (* ae_equality_premise: arity specifying equality premises *)
    - admit. (* ae_lt *)
    - admit. (* ae_context_expr_of_premise *)
    - admit. (* ae_hyp_bdry_of_premise *)
    - admit. (* hyp_judgt_bdry_of_conclusion *)
  Abort.

  Definition judgt_bdry_of_conclusion {Σ} {a} {hjf} (R : rule Σ a hjf)
    : Judgement.boundary (Metavariable.extend Σ a) (form_hypothetical hjf)
  := ([::]; hyp_judgt_bdry_of_conclusion R).

  Definition Fmap_rule
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      {a} {hjf_concl}
      (R : rule Σ a hjf_concl)
    : rule Σ' a hjf_concl.
  Proof.
    simple refine (Build_rule Σ' a hjf_concl _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - exact (ae_equality_premise (premise R)).
    - exact (ae_lt (premise R)).
    - (* ae_context_expr_of_premise *)
      intros i v.
      refine (_ (ae_context_expr_of_premise _ i v)).
      apply Fmap_Raw_Syntax, Fmap1_Metavariable_Extension, f.
    - (* ae_hyp_bdry_of_premise *)
      intros i.
      simple refine
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (ae_hyp_bdry_of_premise _ i)).
      apply Fmap1_Metavariable_Extension, f.
    - (* hyp_judgt_bdry_of_conclusion *)
      simple refine
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (hyp_judgt_bdry_of_conclusion R)).
      apply Fmap1_Metavariable_Extension, f.
  Defined.

End Rule.

(* globalise argument declarations *)
Arguments algebraic_extension {_} _ _.
Arguments rule {_} _ _ _.


Module Span.
(* Some auxiliary constructions for defining the ordering of the premises in the associated congruence rule of a constructor. *)
  
  Local Inductive span : Type := l | r | t.
  
  Local Definition lt_relation : relation span
  := fun x y => match x, y with 
                | l, t => True
                | r, t => True
                | x, y => False
  end.
  
  Definition lt_well_founded : is_well_founded lt_relation.
  Proof.
    intros P P_hereditary.
    assert (Pl : P l). { apply P_hereditary. intros [ | | ] []. }
    assert (Pr : P r). { apply P_hereditary. intros [ | | ] []. }
    intros [ | | ]; try assumption.
    apply P_hereditary. intros [ | | ] l; try assumption; destruct l.
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

Section Associated_Congruence_Rules.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Definition associated_original_premise {obs eqs : arity σ}
    : (obs + obs) + (eqs + eqs + obs) -> (obs + eqs).
  Proof.
    intros p ; repeat destruct p as [p | p];
      try exact (inl p); exact (inr p).
  Defined.

  Arguments associated_original_premise : simpl nomatch.

  (* The ordering of premises of the congruence rule associated to an object rule. *)
  Definition associated_congruence_rule_lt
      {obs eqs : Type} (lt : well_founded_order (obs + eqs))
    : well_founded_order ((obs + obs) + (eqs + eqs + obs)).
  Proof.
    refine (WellFounded.pullback _ (semi_reflexive_product lt Span.lt)).
    intros [ [ ob_l | ob_r ] | [ [ eq_l | eq_r ] | eq_new ] ].
    + exact (inl ob_l, Span.l).
    + exact (inl ob_r, Span.r).
    + exact (inr eq_l, Span.l).
    + exact (inr eq_r, Span.r).
    + exact (inl eq_new, Span.t).
  Defined.

  Arguments associated_congruence_rule_lt : simpl nomatch.

  (*  Unwinding this definition, the relation is be defined as follows:

           ob_l j   ob_r j   eq_l j   eq_r j   eq_new j

ob_l i     i < j    0        i < j    0        i ≤ j

ob_r i     0        i < j    0        i < j    i ≤ j

eq_l i     i < j    0        i < j    0        i < j

eq_r i     0        i < j    0        i < j    i < j

eq_new i   0        0        0        0        i < j

*)

  Definition associated_congruence_rule_original_constructor_translation
    {a} {hjf_concl} (R : rule Σ a hjf_concl)
    (p : (a + a) +
         (ae_equality_premise (premise R) + ae_equality_premise (premise R) + a))
    : Signature_Map
        (Metavariable.extend Σ
          (ae_arity_of_premise (premise R) (associated_original_premise p)))
        (Metavariable.extend Σ (Family.subfamily (a + a)
           (fun j => associated_congruence_rule_lt (ae_lt _) (inl j) p))).
  Proof.
    (* In case [p] is one of the 2 copies of the original premises, there is a single canonical choice for this definition.

    In case [p] is one of the new equality premises (between the 2 copies of the old equality premises), there are in principle 2 possibilities; it should make no difference which one chooses. *)
    apply Fmap2_Metavariable_Extension.
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

  Definition associated_congruence_rule
    {a} {hjf_concl} (R : rule Σ a hjf_concl)
    (H : Judgement.is_object hjf_concl)
    (S : Σ)
    (e_a : symbol_arity S = a)
    (e_cl : symbol_class S = Judgement.class_of hjf_concl)
    : (rule Σ (Family.sum a a)
                 (form_equality (Judgement.class_of hjf_concl))).
  Proof.
    simple refine (Build_rule _ _ _ _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - (* ae_equality_premise: arity of equality premises *)
      exact (((ae_equality_premise (premise R)) + (ae_equality_premise (premise R))) + a).
    - (* ae_lt *)
      exact (associated_congruence_rule_lt (ae_lt _)).
    - (* ae_context_expr_of_premise *)
      intros p i.
      refine (Fmap_Raw_Syntax
        (associated_congruence_rule_original_constructor_translation _ _) _).
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | ? ] ];
      refine (ae_context_expr_of_premise _ p_orig i).
      (* alternatively, instead of destructing [p], could use equality reasoning on the type of [i]. *)
    - (* ae_hyp_bdry_of_premise *)
      intros p.
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | p ] ];
      try (refine (Fmap_Hyp_Judgt_Bdry_Instance
        (associated_congruence_rule_original_constructor_translation _ _) _);
           refine (ae_hyp_bdry_of_premise _ p_orig)).
      (* The cases where [p] is a copy of an original premise are all just translation,
      leaving just the new equality premises to give. *)
      intros i; simpl Judgement.boundary_slot in i.
      destruct i as [ [ i | ] | ]; [ idtac | simpl | simpl].
      + (* boundary of the corresponding original premise *)
        refine (Fmap_Raw_Syntax
          (associated_congruence_rule_original_constructor_translation _ _) _).
        apply (ae_hyp_bdry_of_premise _ p_orig).
      + (* LHS of new equality premise *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_metavariable.
          refine (inl p; _).
          cbn. apply inl, inr; split; constructor.
        * apply idpath.
        * intros i.
          apply raw_variable, (coproduct_inj1 shape_is_sum), i.
      + (* RHS of new equality premise *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_metavariable.
          refine (inr p; _).
          cbn. apply inl, inr; split; constructor.
        * apply idpath.
        * intros i.
          apply raw_variable, (coproduct_inj1 shape_is_sum), i.
    - (* ae_hyp_judgt_bdry_of_conclusion *)
      intros [ [ i | ] | ]; simpl.
      + (* boundary of original conclusion *)
        refine (Fmap_Raw_Syntax _ _).
        * apply Fmap2_Metavariable_Extension, Family.map_inl.
        * destruct hjf_concl as [cl | ?].
          -- exact (hyp_judgt_bdry_of_conclusion R i).
          -- destruct H. (* [hjf_concl] can’t be an equality judgement *)
      + (* LHS of new conclusion *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_symbol, S.
        * apply e_cl.
        * change (symbol_arity (Metavariable.include_symbol S)) with (symbol_arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (raw_symbol' _ _ _).
          -- apply Metavariable.include_metavariable.
             exact (inl p).
          -- apply idpath.
          -- cbn. intros i.
             apply raw_variable.
             apply (coproduct_inj1 shape_is_sum).
             apply (coproduct_inj2 shape_is_sum).
             exact i.
      + (* RHS of new conclusion *)
        cbn. simple refine (raw_symbol' _ _ _).
        * apply Metavariable.include_symbol, S.
        * apply e_cl.
        * change (symbol_arity (Metavariable.include_symbol S)) with (symbol_arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (raw_symbol' _ _ _).
          -- apply Metavariable.include_metavariable.
             exact (inr p).
          -- apply idpath.
          -- cbn. intros i.
             apply raw_variable.
             apply (coproduct_inj1 shape_is_sum).
             apply (coproduct_inj2 shape_is_sum).
             exact i.
  Defined.
  (* TODO: the above is a bit unreadable.  An alternative approach that might be clearer and more robust:
   - factor out the constructions of the head terms of conclusions and premises from [flatten], if doable.
   - here, invoke those, but (for the LHS/RHS of the new equalities), translate them under appropriate context morphisms “inl”, “inr”. *)

(* A good test proposition will be the following: whenever a rule is well-typed, then so is its associated congruence rule. *)

End Associated_Congruence_Rules.


(* Each (ordered) rule induces one or two flat rules: the logical rule itself, and (if it was an object rule) its associated congruence rule.*)

Section Flattening.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* In flattening a rule, and in other settings (e.g. type-checking the premises), we often want to extract premises as judgements.

   We need to do this into several different signatures, so in this lemma, we isolate exactly what is required: a map from the signature of this premise, plus (in case the premise is an object premise) a symbol to use as the head of the judgement, i.e. the metavariable introduced by the premise. *)
  (* TODO: consider whether the flattening of the conclusion can also be covered by this. *)
  Lemma judgement_of_premise 
      {a} {A : algebraic_extension Σ a} (i : A)
      {Σ'} (f : Signature_Map (Metavariable.extend Σ (ae_arity_of_premise _ i)) Σ')
      (Sr : Judgement.is_object (ae_hjf_of_premise _ i) 
           -> { S : Σ'
             & (symbol_arity S = simple_arity (ae_proto_cxt_of_premise _ i))
             * (symbol_class S = Judgement.class_of (ae_hjf_of_premise _ i))})
   : judgement_total Σ'.
  Proof.
    exists (form_hypothetical (ae_hjf_of_premise _ i)).
    exists (Fmap_Raw_Context f (ae_raw_context_of_premise _ i)).
    apply Judgement.hypothetical_instance_from_boundary_and_head.
    - refine (Fmap_Hyp_Judgt_Bdry_Instance f _).
      apply ae_hyp_bdry_of_premise.
    - intro H_obj.
      destruct i as [ i_obj | i_eq ]; simpl in *.
      + (* case: i an object rule *)
        simple refine (raw_symbol' _ _ _).
        * refine (Sr _).1. constructor.
        * refine (snd (Sr _).2).
        * set (e := (fst (Sr tt).2)^). destruct e.
           intro v. apply raw_variable.
           exact (coproduct_inj1 shape_is_sum v).
      + (* case: i an equality rule *)
        destruct H_obj. (* ruled out by assumption *)
  Defined.
  
  (* Flattening a rule requires no extra information in the case of an equality-rule; in the case of an object-rule, it requires a symbol of appropriate arity to give the object introduced. *)
  Definition flatten
    {a} {hjf_concl}
    (R : rule Σ a hjf_concl)
    (Sr : Judgement.is_object hjf_concl
        -> { S : Σ & (symbol_arity S = a) * (symbol_class S = Judgement.class_of hjf_concl) })
  : flat_rule Σ.
  (* This construction involves essentially two aspects:
  - translate the syntax of each expression in the rule-spec from its “local” signatures to the overall signature;
  - reconstruct the head terms of the object premises and the conclusion *)
  Proof.
    refine (Build_flat_rule _ a _ _).
    - (* premises *)
      exists (premise R).
      intros i.
      apply (judgement_of_premise i).
      + apply Fmap2_Metavariable_Extension.
        apply Family.inclusion.
      + intros H_i_obj.
        destruct i as [ i | i ]; simpl in i.
        * (* case: i an object premise *)
          simple refine (_;_). 
          -- apply include_metavariable. exact i.
          -- split; apply idpath.
        * (* case: i an equality premise *)
          destruct H_i_obj. (* ruled out by assumption *)
   - (* conclusion *)
     (* TODO: consider whether this can be unified with [judgement_of_premise] *)
      exists (form_hypothetical hjf_concl).
      simpl.
      exists (pr1 (judgt_bdry_of_conclusion R)).
      apply Judgement.hypothetical_instance_from_boundary_and_head.
      + exact (pr2 (judgt_bdry_of_conclusion R)).
      + intros H_obj.
        destruct hjf_concl as [ ocl | ecl ]; simpl in *.
        * (* case: R an object rule *)
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
          apply (coproduct_inj1 shape_is_sum).
          exact (coproduct_inj2 shape_is_sum i).
        * (* case: R an equality rule *)
          destruct H_obj. (* ruled out by assumption *)
  Defined.

End Flattening.