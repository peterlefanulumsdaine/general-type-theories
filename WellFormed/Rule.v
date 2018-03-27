Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMap.

(** In this file:

- [Rule_Spec]: the data one gives to specify a logical rule (before any typechecking)
- [associated_congruence_rule_spec]
- [Raw_Rule_of_Rule_Spec]
*)

(** Specification of “well-shaped” rules *)
Section RuleSpecs.

Context {σ : shape_system}.

(* The parameters of a rule-spec, beyond its ambient signature, may be a little counter-intuitive.  The point is that they are just what is required to determine the arity of the symbol introduced by the rule, if it’s an object rule. *)
Record Rule_Spec
  {Σ : Signature σ}
  {a : Arity σ} (* arity listing the _object_ premises of the rule *)
  {γ_conclusion : σ} (* proto-context of the conclusion *)
  {hjf_conclusion : judgement_form} (* judgement form of the conclusion *)
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    RS_equality_premise : Arity σ
  (* family indexing the premises of the rule, and giving for each… *)
  ; RS_Premise : family (judgement_form * σ)
    := Family.sum
         (Family.fmap (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)) a)
         (Family.fmap (fun cl_γ => (form_equation (fst cl_γ), snd cl_γ)) RS_equality_premise)
  (* - the judgement form of each premise, e.g. “term” or “type equality” *)
  ; RS_hjf_of_premise : RS_Premise -> judgement_form
    := fun i => fst (RS_Premise i)
  (* - the proto-context of each premise *)
  ; RS_proto_cxt_of_premise : RS_Premise -> σ
    := fun i => snd (RS_Premise i)
  (* the ordering relation on the premises *)
  (* TODO: somewhere we will want to add that this is well-founded; maybe prop_valued; mayb more *)
  ; RS_lt : RS_Premise -> RS_Premise -> Type
  (* for each premise, the arity specifying what metavariables are available in the syntax for this premise; i.e., the family of type/term arguments already introduced by earlier premises *)
  ; RS_arity_of_premise : RS_Premise -> Arity _
    := fun i => Family.subfamily a (fun j => RS_lt (inl j) i)
  (* syntactic part of context of premise *)
  (* NOTE: this should never be used directly, always through [RS_raw_context_of_premise] *)
  ; RS_context_expr_of_premise 
    : forall (i : RS_Premise) (v : RS_proto_cxt_of_premise i),
        Raw_Syntax
          (Metavariable_Extension Σ (RS_arity_of_premise i))
          Ty
          (RS_proto_cxt_of_premise i)
  (* raw context of each premise *)
  ; RS_raw_context_of_premise
    : forall i : RS_Premise,
        Raw_Context (Metavariable_Extension Σ (RS_arity_of_premise i))
    := fun i => Build_Raw_Context _ (RS_context_expr_of_premise i)
  (* hypothetical judgement boundary instance for each premise *)
  ; RS_hyp_bdry_instance_of_premise
    : forall i : RS_Premise,
        Judgement.boundary_instance
          (Metavariable_Extension Σ (RS_arity_of_premise i))
          (RS_hjf_of_premise i)
          (RS_proto_cxt_of_premise i)
  (* context expressions of conclusion *)
  (* NOTE: this should never be used directly, always through [RS_raw_context_of_conclusion] *)
  ; RS_context_expr_of_conclusion
    : γ_conclusion -> Raw_Syntax (Metavariable_Extension Σ a) Ty γ_conclusion
  (* raw context of conclusion *)
  ; RS_raw_context_of_conclusion : Raw_Context (Metavariable_Extension Σ a)
    := Build_Raw_Context _ RS_context_expr_of_conclusion
  (* hyp judgement boundary instance of conclusion *)
  ; RS_hyp_judgt_bdry_instance_of_conclusion
      : Judgement.boundary_instance
          (Metavariable_Extension Σ a)
          hjf_conclusion
          γ_conclusion
  (* full judgement boundary instance of conclusion *) (* TODO: move out of record?? *)
  ; RS_judgt_bdry_instance_of_conclusion
      : Judgt_Bdry_Instance (Metavariable_Extension Σ a)
                            (HJF hjf_conclusion)
    := (RS_raw_context_of_conclusion; RS_hyp_judgt_bdry_instance_of_conclusion)
  }.
  (* NOTE 1. One could restrict rule-specs by only allowing the case where the context of the conclusion is empty.  This would simplify this definition, and several things below, and would (one expects) not lose any generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context.

  However, we retain (for now) the current general version, (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about it being equivalent to move variables into the premises. *)

  (* NOTE 2. Perhaps the parameters of the definition could be profitably abstracted into a “proto-rule-spec” (probably including also the arity [RS_equality_Premise]), fitting the pattern of the stratificaiton of objects into proto ≤ raw ≤ typed. *)

  Arguments Rule_Spec _ _ _ _ : clear implicits.

(* Template for defining rule-specs:

  simple refine (Build_Rule_Spec _ _ _ _ _ _ _ _ _ _).
  - admit. (* RS_equality_premise: arity of equality premises *)
  - admit. (* RS_lt *)
  - admit. (* RS_context_expr_of_premise *)
  - admit. (* RS_hyp_bdry_instance_of_premise *)
  - admit. (* RS_context_expr_of_conclusion *)
  - admit. (* RS_hyp_judgt_bdry_instance_of_conclusion *)

*)

  Definition Fmap_Rule_Spec
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      {a} {γ_concl} {hjf_concl}
      (R : Rule_Spec Σ a γ_concl hjf_concl)
    : Rule_Spec Σ' a γ_concl hjf_concl.
  Proof.
    simple refine (Build_Rule_Spec Σ' a γ_concl hjf_concl _ _ _ _ _ _).
    - exact (RS_equality_premise R).
    - exact (RS_lt R).
    - (* RS_context_expr_of_premise *)
      intros i v.
      refine (_ (RS_context_expr_of_premise R i v)).
      apply Fmap_Raw_Syntax, Fmap1_Metavariable_Extension, f.
    - (* RS_hyp_bdry_instance_of_premise *)
      intros i.
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (RS_hyp_bdry_instance_of_premise R i)).
      apply Fmap1_Metavariable_Extension, f.
    - (* RS_context_expr_of_conclusion *)
      intros v.
      refine (_ (RS_context_expr_of_conclusion R v)).
      apply Fmap_Raw_Syntax, Fmap1_Metavariable_Extension, f.
    - (* RS_hyp_judgt_bdry_instance_of_conclusion *)
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (RS_hyp_judgt_bdry_instance_of_conclusion R)).
      apply Fmap1_Metavariable_Extension, f.
  Defined.

End RuleSpecs.

Arguments Rule_Spec {_} _ _ _ _.


Section Associated_Congruence_Rule_Specs.

  Context {σ : shape_system}.
  Context {Σ : Signature σ}.

  Definition associated_original_premise {obs eqs : Arity σ}
    : (obs + obs) + (eqs + eqs + obs) -> (obs + eqs).
  Proof.
    intros p ; repeat destruct p as [p | p];
      try exact (inl p); exact (inr p).
  Defined.
  
  Arguments associated_original_premise : simpl nomatch.

  (* The ordering of premises of the congruence rule_spec associated to an object rule_spec. 

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
    {a} {γ_concl} {hjf_concl} (R : Rule_Spec Σ a γ_concl hjf_concl)
    (p : (a + a) + (RS_equality_premise R + RS_equality_premise R + a))
    : Signature_Map
        (Metavariable_Extension Σ
          (RS_arity_of_premise R (associated_original_premise p)))
        (Metavariable_Extension Σ (Family.subfamily (a + a)
           (fun j => associated_congruence_rule_lt (RS_lt R) (inl j) p))).
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

  Definition associated_congruence_rule_spec
    {a} {γ_concl} {hjf_concl} (R : Rule_Spec Σ a γ_concl hjf_concl)
    (H : is_object_form hjf_concl)
    (S : Σ)
    (e_a : arity S = a + (simple_arity γ_concl))
    (e_cl : class S = class_of_HJF hjf_concl)
    : (Rule_Spec Σ (Family.sum a a) γ_concl
                 (form_equation (class_of_HJF hjf_concl))).
  Proof.
    simple refine (Build_Rule_Spec _ _ _ _ _ _ _ _ _ _).
    - (* RS_equality_premise: arity of equality premises *)
      exact (((RS_equality_premise R) + (RS_equality_premise R)) + a). 
    - (* RS_lt *)
      exact (associated_congruence_rule_lt (RS_lt R)).
    - (* RS_context_expr_of_premise *)
      intros p i.
      refine (Fmap_Raw_Syntax
        (associated_congruence_rule_original_constructor_translation _ _) _).
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | ? ] ];
      refine (RS_context_expr_of_premise R p_orig i).
      (* alternatively, instead of destructing [p], could use equality reasoning on the type of [i]. *)
    - (* RS_hyp_bdry_instance_of_premise *)
      intros p.
      set (p_orig := associated_original_premise p).
      destruct p as [ [ ? | ? ] | [ [ ? | ? ] | p ] ];
      try (refine (Fmap_Hyp_Judgt_Bdry_Instance
        (associated_congruence_rule_original_constructor_translation _ _) _);
           refine (RS_hyp_bdry_instance_of_premise R p_orig)).
      (* The cases where [p] is a copy of an original premise are all just translation,
      leaving just the new equality premises to give. *)
      intros i; simpl Hyp_Judgt_Bdry_Slots in i.
      destruct i as [ [ i | ] | ]; [ idtac | simpl | simpl]. 
      + (* boundary of the corresponding original premise *)
        refine (Fmap_Raw_Syntax
          (associated_congruence_rule_original_constructor_translation _ _) _).
        apply (RS_hyp_bdry_instance_of_premise R p_orig).
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
    - (* RS_context_expr_of_conclusion *)
      intros i.
      refine (Fmap_Raw_Syntax _ (RS_context_expr_of_conclusion R i)).
      apply Fmap2_Metavariable_Extension, Family.map_inl.
    - (* RS_hyp_judgt_bdry_instance_of_conclusion *)
      intros [ [ i | ] | ]; simpl. 
      + (* boundary of original conclusion *)
        refine (Fmap_Raw_Syntax _ _).
        * apply Fmap2_Metavariable_Extension, Family.map_inl.
        * destruct hjf_concl as [cl | ?].
          -- exact (RS_hyp_judgt_bdry_instance_of_conclusion R i).
          -- destruct H. (* [hjf_concl] can’t be an equality judgement *)
      + (* LHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros [ p | i ].
          -- simple refine (symb_raw' _ _ _).
             ++ apply inr_Metavariable.
                exact (inl p).
             ++ apply idpath.
             ++ cbn. intros i.
                apply var_raw. 
                apply (coproduct_inj1 shape_is_sum).
                apply (coproduct_inj2 shape_is_sum).
                exact i.
          -- apply var_raw, (coproduct_inj1 shape_is_sum), i.
      + (* RHS of new conclusion *)
        cbn. simple refine (symb_raw' _ _ _).
        * apply inl_Symbol, S.
        * apply e_cl.
        * change (arity (inl_Symbol S)) with (arity S).
          destruct (e_a^); clear e_a.
          intros [ p | i ].
          -- simple refine (symb_raw' _ _ _).
             ++ apply inr_Metavariable.
                exact (inr p).
             ++ apply idpath.
             ++ cbn. intros i.
                apply var_raw. 
                apply (coproduct_inj1 shape_is_sum).
                apply (coproduct_inj2 shape_is_sum).
                exact i.
          -- apply var_raw, (coproduct_inj1 shape_is_sum), i.
  Defined.
  (* TODO: the above is a bit unreadable.  An alternative approach that might be clearer and more robust:
   - factor out the constructions of the head terms of conclusions and premises from [Raw_Rule_of_Rule_Spec], if doable.
   - here, invoke those, but (for the LHS/RHS of the new equalities), translate them under appropriate context morphisms “inl”, “inr”. *)

(* A good test proposition will be the following: whenever a rule-spec is well-typed, then so is its associated congruence rule-spec. *)

End Associated_Congruence_Rule_Specs.


(* Each rule-spec induces one or two raw rules: the logical rule itself, and (if it was an object rule) its associated congruence rule.*)

Section Raw_Rules_of_Rule_Specs.

  Context {σ : shape_system}.
  Context {Σ : Signature σ}.

  (* Translating a rule-spec into a raw rule requires no extra information in the case of an equality-rule; in the case of an object-rule, it requires a symbol of appropriate arity to give the object introduced. *)
  Definition Raw_Rule_of_Rule_Spec
    {a} {γ_concl} {hjf_concl}
    (R : Rule_Spec Σ a γ_concl hjf_concl)
    (Sr : is_object_form hjf_concl
        -> { S : Σ & (arity S = Family.sum a (simple_arity γ_concl))
                     * (class S = class_of_HJF hjf_concl) })
  : Raw_Rule Σ.
  (* This construction involves essentially two aspects:
  - translate the syntax of each expression in the rule-spec from its “local” signatures to the overall signature;
  - reconstruct the head terms of the object premises and the conclusion *)
  Proof.
    refine (Build_Raw_Rule _ a _ _).
    - (* premises *)
      exists (RS_Premise R).
      intros P. 
      assert (f_P : Signature_Map
              (Metavariable_Extension Σ (RS_arity_of_premise R P))
              (Metavariable_Extension Σ a)).
      {
        apply Fmap2_Metavariable_Extension.
        apply Family.inclusion.
      }
      exists (HJF (RS_hjf_of_premise _ P)).
      exists (Fmap_Raw_Context f_P (RS_raw_context_of_premise _ P)).
      simpl.
      apply Judgement.hypothetical_instance_from_boundary_and_head.
      + refine (Fmap_Hyp_Judgt_Bdry_Instance f_P _).
        apply RS_hyp_bdry_instance_of_premise.
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
      exists (pr1 (RS_judgt_bdry_instance_of_conclusion R)).
      apply Judgement.hypothetical_instance_from_boundary_and_head.
      + exact (pr2 (RS_judgt_bdry_instance_of_conclusion R)).
      + intros H_obj.
        destruct hjf_concl as [ ocl | ecl ]; simpl in *.
        * (* case: R an object rule *)
          destruct (Sr tt) as [S_R [e_a e_cl]]. clear Sr H_obj.
          destruct e_cl. (* TODO: can we simplify here with [symb_raw']? *)
          refine (symb_raw (inl S_R : Metavariable_Extension _ _) _).
          change (arity (inl S_R : Metavariable_Extension _ _))
            with (arity S_R). 
          set (aR := arity S_R) in *. destruct (e_a^); clear e_a.
          intros [P | i].
          -- cbn in P.
            refine (symb_raw (inr P : Metavariable_Extension _ _) _).
            intros i.
            apply var_raw.
            apply (coproduct_inj1 shape_is_sum).
            exact (coproduct_inj2 shape_is_sum i).
          -- apply var_raw.
            exact (coproduct_inj1 shape_is_sum i).
        * (* case: R an equality rule *)
          destruct H_obj. (* ruled out by assumption *)
  Defined.

End Raw_Rules_of_Rule_Specs.