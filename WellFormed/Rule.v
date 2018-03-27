Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMap.

(** In this file:

- [rule]: the data one gives to specify a logical rule (before any typechecking)
- [associated_congruence_rule]
- [Raw_Rule_of_rule]
*)

(** Specification of “well-shaped” rules *)
Section Rule.

Context {σ : shape_system}.

(* An (ordered, raw) rule consists of premises and a conclusion.  For various reasons, we abstract the form of the premises as an _algebraic extension_.

Such an extension can add both object rules and equality rules.  When an extension is used as premises of a rule, these rules become the premises, introducing type/term metavariables and equality premises respectively.

The extension is _algebraic_ in the sense that it does not introduce any new binders; this is the raw-syntax analogue of an arity seen as specifying the metavariable-extension of a signature. *)
Record algebraic_extension
  {Σ : Signature σ}
  {a : Arity σ} (* arity listing the _object_ rules of the extension *)
:=
  {
  (* The arity [a] supplies the family of object-judgment rules. *)
  (* The family of equality-judgment rules: *)
    ae_equality_rule : Arity σ
  (* family indexing the rules of the extension, and giving for each… *)
  ; ae_rule :> family (Hyp_Judgt_Form * σ)
    := Family.sum
         (Family.fmap (fun cl_γ => (obj_HJF (fst cl_γ), snd cl_γ)) a)
         (Family.fmap (fun cl_γ => (eq_HJF (fst cl_γ), snd cl_γ)) ae_equality_rule)
  (* - the judgement form of each rule, e.g. “term” or “type equality” *)
  ; ae_hjf_of_rule : ae_rule -> Hyp_Judgt_Form
    := fun i => fst (ae_rule i)
  (* - the proto-context of each rule *)
  ; ae_proto_cxt_of_rule : ae_rule -> σ
    := fun i => snd (ae_rule i)
  (* the ordering relation on the rules *)
  (* TODO: somewhere we will want to add that this is well-founded; maybe prop_valued; mayb more *)
  ; ae_lt : ae_rule -> ae_rule -> Type
  (* for each rule, the arity specifying what metavariables are available in the syntax for this rule; i.e., the family of type/term arguments already introduced by earlier rules *)
  ; ae_arity_of_rule : ae_rule -> Arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  (* syntactic part of context of rule *)
  (* NOTE: this should never be used directly, always through [ae_raw_context_of_rule] *)
  ; ae_context_expr_of_rule 
    : forall (i : ae_rule) (v : ae_proto_cxt_of_rule i),
        Raw_Syntax
          (Metavariable_Extension Σ (ae_arity_of_rule i))
          Ty
          (ae_proto_cxt_of_rule i)
  (* raw context of each rule *)
  ; ae_raw_context_of_rule
    : forall i : ae_rule,
        Raw_Context (Metavariable_Extension Σ (ae_arity_of_rule i))
    := fun i => Build_Raw_Context _ (ae_context_expr_of_rule i)
  (* hypothetical judgement boundary instance for each rule *)
  ; ae_hyp_bdry_of_rule
    : forall i : ae_rule,
        Hyp_Judgt_Bdry_Instance
          (Metavariable_Extension Σ (ae_arity_of_rule i))
          (ae_hjf_of_rule i)
          (ae_proto_cxt_of_rule i)
  }.

  Arguments algebraic_extension _ _ : clear implicits. 

(* The parameters of a rule, beyond its ambient signature, may be a little counter-intuitive.  The point is that they are just what is required to determine the arity of the symbol introduced by the rule, if it’s an object rule. *)
Record rule
  {Σ : Signature σ}
  {a : Arity σ} (* arity listing the _object_ premises of the rule *)
  {hjf_conclusion : Hyp_Judgt_Form} (* judgement form of the conclusion *)
:=
  {
    premise :> algebraic_extension Σ a
  (* hyp judgement boundary instance of conclusion: *)
  ; hyp_judgt_bdry_of_conclusion
      : Hyp_Judgt_Bdry_Instance
          (Metavariable_Extension Σ a)
          hjf_conclusion
          (shape_empty σ)
  }.

(* NOTE 1. One could generalise rule-specs by allowing the context of the conclusion to be non-empty.

 This would slightly complicate this definition, and subsequent constructions, and would (one expects) not add any real generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context (where the equivalence makes use of the “cut”/substitution rule).

  However, it could be nice (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about it being equivalent to move variables into the premises.

  On the other hand, so long as the _flattened_ rules [Raw_Rule] allow arbitrary conclusion judgements, one can still use those to give a lemma about the equivalence. *)

  (* NOTE 2. Perhaps the parameters of the definition of [rule] could be profitably abstracted into a “proto-rule-spec” (probably including also the arity [ae_equality_rule]), fitting the pattern of the stratificaiton of objects into proto ≤ raw ≤ typed. *)

  Arguments rule _ _ _ : clear implicits.

  (* Template for defining rule-specs: *)
  Definition Example {Σ} {a} {hjf} : rule Σ a hjf.
  Proof.
    simple refine (Build_rule _ _ _ _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - admit. (* ae_equality_rule: arity specifying equality premises *)
    - admit. (* ae_lt *)
    - admit. (* ae_context_expr_of_rule *)
    - admit. (* ae_hyp_bdry_of_rule *)
    - admit. (* hyp_judgt_bdry_of_conclusion *)
  Abort.

  Definition judgt_bdry_of_conclusion {Σ} {a} {hjf} (R : rule Σ a hjf)
    : Judgt_Bdry_Instance (Metavariable_Extension Σ a) (HJF hjf)
  := ([::]; hyp_judgt_bdry_of_conclusion R). 

  Definition Fmap_rule
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      {a} {hjf_concl}
      (R : rule Σ a hjf_concl)
    : rule Σ' a hjf_concl.
  Proof.
    simple refine (Build_rule Σ' a hjf_concl _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - exact (ae_equality_rule R).
    - exact (ae_lt R).
    - (* ae_context_expr_of_rule *)
      intros i v.
      refine (_ (ae_context_expr_of_rule R i v)).
      apply Fmap_Raw_Syntax, Fmap1_Metavariable_Extension, f.
    - (* ae_hyp_bdry_of_rule *)
      intros i.
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (ae_hyp_bdry_of_rule R i)).
      apply Fmap1_Metavariable_Extension, f.
    - (* hyp_judgt_bdry_of_conclusion *)
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (hyp_judgt_bdry_of_conclusion R)).
      apply Fmap1_Metavariable_Extension, f.
  Defined.

End Rule.

Arguments rule {_} _ _ _.


Section Associated_Congruence_Rules.

  Context {σ : shape_system}.
  Context {Σ : Signature σ}.

  Definition associated_original_premise {obs eqs : Arity σ}
    : (obs + obs) + (eqs + eqs + obs) -> (obs + eqs).
  Proof.
    intros p ; repeat destruct p as [p | p];
      try exact (inl p); exact (inr p).
  Defined.
  
  Arguments associated_original_premise : simpl nomatch.

  (* The ordering of premises of the congruence rule associated to an object rule. 

  TODO: perhaps try to refactor to avoid so many special cases?  E.g. as: take the lex product of the input relation [R] with the 3-element order ({{0},{1},{0,1}}, ⊂ ) and then pull this back along the suitable map (o+o)+(e+e+o) —> (o+e)*3 ?  *)
  Definition associated_congruence_rule_lt
      {obs eqs : Type} (lt : relation (obs + eqs))
    : relation ((obs + obs) + (eqs + eqs + obs)).
  Proof.
  (*  In a more readable organisation, the cases we want are as follows:

           ob_l i   ob_r i   eq_l i   eq_r i   eq_new i

ob_l j     i < j    0        i < j    0        0

ob_r j     0        i < j    0        i < j    0
 
eq_l j     i < j    0        i < j    0        0

eq_r j     0        i < j    0        i < j    0

eq_new j   i ≤ j    i ≤ j    i < j    i < j    i < j

*)
    intros [ [ ob_l | ob_r ] | [ [ eq_l | eq_r ] | eq_new ] ];
    intros [ [ ob'_l | ob'_r ] | [ [ eq'_l | eq'_r ] | eq'_new ] ].
      (* column eq_l *)
    - exact (lt (inl ob_l) (inl ob'_l)).
    - exact False.
    - exact (lt (inl ob_l) (inr eq'_l)).
    - exact False.
    - exact ((lt (inl ob_l) (inl eq'_new)) \/ (ob_l = eq'_new)).
      (* column ob_r *)
    - exact False.
    - exact (lt (inl ob_r) (inl ob'_r)).
    - exact False.
    - exact (lt (inl ob_r) (inr eq'_r)).
    - exact ((lt (inl ob_r) (inl eq'_new)) \/ (ob_r = eq'_new)).
      (* column eq_l *)
    - exact (lt (inr eq_l) (inl ob'_l)).
    - exact False.
    - exact (lt (inr eq_l) (inr eq'_l)).
    - exact False.
    - exact (lt (inr eq_l) (inl eq'_new)).
      (* column eq_r *)
    - exact False.
    - exact (lt (inr eq_r) (inl ob'_r)).
    - exact False.
    - exact (lt (inr eq_r) (inr eq'_r)).
    - exact (lt (inr eq_r) (inl eq'_new)).
      (* column eq_new *)
    - exact False.
    - exact False.
    - exact False.
    - exact False.
    - exact (lt (inl eq_new) (inl eq'_new)).
  Defined.

  Arguments associated_congruence_rule_lt : simpl nomatch.

  Definition associated_congruence_rule_original_constructor_translation
    {a} {hjf_concl} (R : rule Σ a hjf_concl)
    (p : (a + a) + (ae_equality_rule R + ae_equality_rule R + a))
    : Signature_Map
        (Metavariable_Extension Σ
          (ae_arity_of_rule R (associated_original_premise p)))
        (Metavariable_Extension Σ (Family.subfamily (a + a)
           (fun j => associated_congruence_rule_lt (ae_lt R) (inl j) p))).
  Proof.
    (* In case [p] is one of the 2 copies of the original premises, there is a single canonical choice for this definition.

    In case [p] is one of the new equality premises (between the 2 copies of the old equality premises), there are in principle 2 possibilities; it should make no difference which one chooses. *)
    apply Fmap2_Metavariable_Extension.
    simple refine (_;_).
    - intros q.
      destruct p as [ [ pob_l | pob_r ] | [ [ peq_l | peq_r ] | peq_new ] ].
      + (* pob_l *)
        exists (inl (pr1 q)). exact (pr2 q).
      + (* pob_r *) 
        exists (inr (pr1 q)). exact (pr2 q).
      + (* peq_l *) 
        exists (inl (pr1 q)). exact (pr2 q).
      + (* peq_r *) 
        exists (inr (pr1 q)). exact (pr2 q).
      + (* peq_new *)
        exists (inr (pr1 q)). (* note both [inl], [inr] make this work *)
        exact (inl (pr2 q)).
    - intros q.
      repeat destruct p as [ p | p ]; apply idpath.
  Defined.

  Definition associated_congruence_rule
    {a} {hjf_concl} (R : rule Σ a hjf_concl)
    (H : is_obj_HJF hjf_concl)
    (S : Σ)
    (e_a : arity S = a)
    (e_cl : class S = class_of_HJF hjf_concl)
    : (rule Σ (Family.sum a a)
                 (eq_HJF (class_of_HJF hjf_concl))).
  Proof.
    simple refine (Build_rule _ _ _ _ _).
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - (* ae_equality_rule: arity of equality premises *)
      exact (((ae_equality_rule R) + (ae_equality_rule R)) + a). 
    - (* ae_lt *)
      exact (associated_congruence_rule_lt (ae_lt R)).
    - (* ae_context_expr_of_rule *)
      intros p i.
      refine (Fmap_Raw_Syntax
        (associated_congruence_rule_original_constructor_translation _ _) _).
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | ? ] ];
      refine (ae_context_expr_of_rule R p_orig i).
      (* alternatively, instead of destructing [p], could use equality reasoning on the type of [i]. *)
    - (* ae_hyp_bdry_of_rule *)
      intros p.
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | p ] ];
      try (refine (Fmap_Hyp_Judgt_Bdry_Instance
        (associated_congruence_rule_original_constructor_translation _ _) _);
           refine (ae_hyp_bdry_of_rule R p_orig)).
      (* The cases where [p] is a copy of an original premise are all just translation,
      leaving just the new equality premises to give. *)
      intros i; simpl Hyp_Judgt_Bdry_Slots in i.
      destruct i as [ [ i | ] | ]; [ idtac | simpl | simpl]. 
      + (* boundary of the corresponding original premise *)
        refine (Fmap_Raw_Syntax
          (associated_congruence_rule_original_constructor_translation _ _) _).
        apply (ae_hyp_bdry_of_rule R p_orig).
      + (* LHS of new equality premise *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inr_Metavariable.
          refine (inl p; _).
          apply inr, idpath.
        * apply idpath.
        * intros i.
          apply var_raw, (coproduct_inj1 shape_is_sum), i.
      + (* RHS of new equality premise *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inr_Metavariable.
          refine (inr p; _).
          apply inr, idpath.
        * apply idpath.
        * intros i.
          apply var_raw, (coproduct_inj1 shape_is_sum), i.
    - (* ae_hyp_judgt_bdry_of_conclusion *)
      intros [ [ i | ] | ]; simpl. 
      + (* boundary of original conclusion *)
        refine (Fmap_Raw_Syntax _ _).
        * apply Fmap2_Metavariable_Extension, Family.map_inl.
        * destruct hjf_concl as [cl | ?].
          -- exact (hyp_judgt_bdry_of_conclusion R i).
          -- destruct H. (* [hjf_concl] can’t be an equality judgement *)
      + (* LHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (symb_raw' _ _ _).
          -- apply inr_Metavariable.
             exact (inl p).
          -- apply idpath.
          -- cbn. intros i.
             apply var_raw. 
             apply (coproduct_inj1 shape_is_sum).
             apply (coproduct_inj2 shape_is_sum).
             exact i.
      + (* RHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros p.
          simple refine (symb_raw' _ _ _).
          -- apply inr_Metavariable.
             exact (inr p).
          -- apply idpath.
          -- cbn. intros i.
             apply var_raw. 
             apply (coproduct_inj1 shape_is_sum).
             apply (coproduct_inj2 shape_is_sum).
             exact i.
  Defined.
  (* TODO: the above is a bit unreadable.  An alternative approach that might be clearer and more robust:
   - factor out the constructions of the head terms of conclusions and premises from [Raw_Rule_of_rule], if doable.
   - here, invoke those, but (for the LHS/RHS of the new equalities), translate them under appropriate context morphisms “inl”, “inr”. *)

(* A good test proposition will be the following: whenever a rule is well-typed, then so is its associated congruence rule. *)

End Associated_Congruence_Rules.


(* Each rule induces one or two raw rules: the logical rule itself, and (if it was an object rule) its associated congruence rule.*)

Section Raw_Rules_of_Rules.

  Context {σ : shape_system}.
  Context {Σ : Signature σ}.

  (* Flattening a rule into a raw rule requires no extra information in the case of an equality-rule; in the case of an object-rule, it requires a symbol of appropriate arity to give the object introduced. *)
  Definition Raw_Rule_of_Rule
    {a} {hjf_concl}
    (R : rule Σ a hjf_concl)
    (Sr : is_obj_HJF hjf_concl
        -> { S : Σ & (arity S = a) * (class S = class_of_HJF hjf_concl) })
  : Raw_Rule Σ.
  (* This construction involves essentially two aspects:
  - translate the syntax of each expression in the rule-spec from its “local” signatures to the overall signature;
  - reconstruct the head terms of the object premises and the conclusion *)
  Proof.
    refine (Build_Raw_Rule _ a _ _).
    - (* premises *)
      exists (ae_rule R).
      intros P. 
      assert (f_P : Signature_Map
              (Metavariable_Extension Σ (ae_arity_of_rule R P))
              (Metavariable_Extension Σ a)).
      {
        apply Fmap2_Metavariable_Extension.
        apply Family.inclusion.
      }
      exists (HJF (ae_hjf_of_rule _ P)).
      exists (Fmap_Raw_Context f_P (ae_raw_context_of_rule _ P)).
      simpl.
      apply Hyp_Judgt_Instance_from_bdry_plus_head.
      + refine (Fmap_Hyp_Judgt_Bdry_Instance f_P _).
        apply ae_hyp_bdry_of_rule.
      + intro H_obj.
        destruct P as [ P | P ]; simpl in P.
        * (* case: P an object premise *)
          refine (symb_raw (inr P : Metavariable_Extension Σ a) _).
          intro i. apply var_raw.
          exact (coproduct_inj1 shape_is_sum i).
        * (* case: P an equality premise *)
          destruct H_obj. (* ruled out by assumption *)
   - (* conclusion *)
      exists (HJF hjf_concl).
      simpl.
      exists (pr1 (judgt_bdry_of_conclusion R)).
      apply Hyp_Judgt_Instance_from_bdry_plus_head.
      + exact (pr2 (judgt_bdry_of_conclusion R)).
      + intros H_obj.
        destruct hjf_concl as [ ocl | ecl ]; simpl in *.
        * (* case: R an object rule *)
          destruct (Sr tt) as [S_R [e_a e_cl]]. clear Sr H_obj.
          destruct e_cl. (* TODO: can we simplify here with [symb_raw']? *)
          refine (symb_raw (inl S_R : Metavariable_Extension _ _) _).
          change (arity (inl S_R : Metavariable_Extension _ _))
            with (arity S_R). 
          set (aR := arity S_R) in *. destruct (e_a^); clear e_a.
          intros p.
          cbn in p.
          refine (symb_raw (inr p : Metavariable_Extension _ _) _).
          intros i.
          apply var_raw.
          apply (coproduct_inj1 shape_is_sum).
          exact (coproduct_inj2 shape_is_sum i).
        * (* case: R an equality rule *)
          destruct H_obj. (* ruled out by assumption *)
  Defined.

End Raw_Rules_of_Rules.