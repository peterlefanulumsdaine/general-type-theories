Require Import HoTT.
Require Import Family.
Require Import ShapeSystems.
Require Import Coproduct.
Require Import DeductiveClosure.
Require Import RawSyntax.
Require Import SignatureMaps.

Section Raw_Rules.

  Context {σ : Shape_System}.
  Context (Σ : Signature σ).

  Record Raw_Rule
  :=
    { RR_metas : Arity _
    ; RR_prem : Family (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    ; RR_concln : (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    }.

  Definition CCs_of_RR (R : Raw_Rule)
    : Family (closure_condition (Judgt_Instance Σ)).
  Proof.
    exists { Γ : Raw_Context Σ & Instantiation (RR_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Fmap _ (RR_prem R)).
      apply (instantiate_ji I).
    - apply (instantiate_ji I).
      apply (RR_concln R).
  Defined.

  Definition Raw_Type_Theory := Family Raw_Rule.

End Raw_Rules.

Arguments CCs_of_RR {_ _} _.

(** Specification of “well-shaped” rules *)
Section RuleSpecs.

Context {Proto_Cxt : Shape_System}.

Record Rule_Spec
  {Σ : Signature Proto_Cxt}
  {a : Arity Proto_Cxt}
  {γ_conclusion : Shape Proto_Cxt}
  {hjf_conclusion : Hyp_Judgt_Form}
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    RS_equality_premise : Arity Proto_Cxt
  (* family indexing the premises of the rule, and giving for each… *)
  ; RS_Premise : Family (Hyp_Judgt_Form * Proto_Cxt)
    := Family.Sum
         (Family.Fmap (fun cl_γ => (obj_HJF (fst cl_γ), snd cl_γ)) a)
         (Family.Fmap (fun cl_γ => (eq_HJF (fst cl_γ), snd cl_γ)) RS_equality_premise)
  (* - the judgement form of each premise, e.g. “term” or “type equality” *)
  ; RS_hjf_of_premise : RS_Premise -> Hyp_Judgt_Form
    := fun i => fst (RS_Premise i)
  (* - the proto-context of each premise *)
  ; RS_proto_cxt_of_premise : RS_Premise -> Proto_Cxt
    := fun i => snd (RS_Premise i)
  (* the ordering relation on the premises *)
  (* TODO: somewhere we will want to add that this is well-founded; maybe more *)
  ; RS_lt : RS_Premise -> RS_Premise -> hProp
  (* for each premise, the arity specifying what metavariables are available in the syntax for this premise; i.e., the family of type/term arguments already introduced by earlier premises *)
  ; RS_arity_of_premise : RS_Premise -> Arity _
    := fun i => Fmap
        (fun jγ => (class_of_HJF (fst jγ), snd jγ))
        (Subfamily RS_Premise
          (fun j => is_obj_HJF (fst (RS_Premise j)) * RS_lt j i))
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
        Hyp_Judgt_Bdry_Instance
          (Metavariable_Extension Σ (RS_arity_of_premise i))
          (RS_hjf_of_premise i)
          (RS_proto_cxt_of_premise i)
  (* arity of the rule as a whole *)
  ; RS_arity : Arity _
    := Fmap
        (fun jγ => (class_of_HJF (fst jγ), snd jγ))
        (Subfamily RS_Premise
          (fun j => is_obj_HJF (fst (RS_Premise j))))
  (* judgement form of conclusion *)
  ; RS_hjf_of_conclusion : Hyp_Judgt_Form
    := hjf_conclusion
  (* context expressions of conclusion *)
  (* NOTE: this should never be used directly, always through [RS_raw_context_of_conclusion] *)
  ; RS_context_expr_of_conclusion
    : γ_conclusion -> Raw_Syntax (Metavariable_Extension Σ a) Ty γ_conclusion
  (* raw context of conclusion *)
  ; RS_raw_context_of_conclusion : Raw_Context (Metavariable_Extension Σ a)
    := Build_Raw_Context _ RS_context_expr_of_conclusion
  (* hyp judgement boundary instance of conclusion *)
  ; RS_hyp_judgt_bdry_instance_of_conclusion
      : Hyp_Judgt_Bdry_Instance
          (Metavariable_Extension Σ a)
          RS_hjf_of_conclusion
          γ_conclusion
  (* full judgement boundary instance of conclusion *)
  ; RS_judgt_bdry_instance_of_conclusion
      : Judgt_Bdry_Instance (Metavariable_Extension Σ a)
                            (HJF RS_hjf_of_conclusion)
    := (RS_raw_context_of_conclusion; RS_hyp_judgt_bdry_instance_of_conclusion)
  }.
  (* NOTE 1. One could restrict this by only allowing the case where the context of the conclusion is empty.  This would simplify this definition, and several things below, and would (one expects) not lose any generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context.

  However, we retain (for now) the current general version, (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about equivalent  forms of a rule . *)

  (* NOTE 2. The current parameters of the definition could perhaps be profitably abstracted into a “proto-rule-spec” (probably including also the arity [RS_equality_Premise]), fitting the pattern of the stratificaiton of objects into proto -> raw -> typed. *)

  Arguments Rule_Spec _ _ _ _ : clear implicits.

  (* TODO: upstream *)
  Definition Fmap_Metavariable_Extension
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      (a : Arity Proto_Cxt)
    : Signature_Map (Metavariable_Extension Σ a)
                    (Metavariable_Extension Σ' a).
  Proof.
    refine (Fmap_Family_Sum _ _).
    - apply f.
    - apply idmap_Family.
  Defined.

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
      apply Fmap_Raw_Syntax, Fmap_Metavariable_Extension, f.
    - (* RS_hyp_bdry_instance_of_premise *)
      intros i.
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (RS_hyp_bdry_instance_of_premise R i)).
      apply Fmap_Metavariable_Extension, f.
    - (* RS_context_expr_of_conclusion *)
      intros v.
      refine (_ (RS_context_expr_of_conclusion R v)).
      apply Fmap_Raw_Syntax, Fmap_Metavariable_Extension, f.
    - (* RS_hyp_judgt_bdry_instance_of_conclusion *)
      simple refine 
        (Fmap_Hyp_Judgt_Bdry_Instance
          _ (RS_hyp_judgt_bdry_instance_of_conclusion R)).
      apply Fmap_Metavariable_Extension, f.     
  Defined.
  
  Definition Raw_Rule_of_Rule_Spec
    {Σ} {a} {γ_concl} {hjf_concl}
    (R : Rule_Spec Σ a γ_concl hjf_concl)
    (Sr : is_obj_HJF hjf_concl
        -> { S : Σ & (arity S = Family.Sum a (simple_arity γ_concl))
                     * (class S = class_of_HJF hjf_concl) })
  : Raw_Rule Σ.
  (* This construction involves essentially two aspects:
  - translate the syntax given in R from its “local” signatures to the overall signature;
  - construct the head terms of object premises and conclusion
  *)
  Proof.
    refine (Build_Raw_Rule _ a _ _).
    - (* premises *)
      exists (RS_Premise R).
      intros P. 
      assert (f_P : Signature_Map
              (Metavariable_Extension Σ (RS_arity_of_premise R P))
              (Metavariable_Extension Σ a)).
        admit. (* signature map from sub-arity *)
      exists (HJF (RS_hjf_of_premise _ P)).
      exists (Fmap_Raw_Context f_P (RS_raw_context_of_premise _ P)).
      simpl.
      apply Hyp_Judgt_Instance_from_bdry_plus_head.
      + refine (Fmap_Hyp_Judgt_Bdry_Instance f_P _).
        apply RS_hyp_bdry_instance_of_premise.
      + intro H_obj.
        destruct P as [ P | P ]; simpl in P.
        * (* case: P an object premise *)
          refine (symb_raw (inr P : Metavariable_Extension Σ a) _).
          intro i. apply var_raw.
          exact (coproduct_inj1 shape_is_coproduct i).
        * (* case: P an equality premise *)
          destruct H_obj. (* ruled out by assumption *)
    - (* conclusion *)
      exists (HJF hjf_concl).
      simpl.
      exists (pr1 (RS_judgt_bdry_instance_of_conclusion R)).
      apply Hyp_Judgt_Instance_from_bdry_plus_head.
      + exact (pr2 (RS_judgt_bdry_instance_of_conclusion R)).
      + intros H_obj.
        destruct hjf_concl as [ ocl | ecl ]; simpl in *.
        * (* case: R an object rule *)
          destruct (Sr tt) as [S_R [e_a e_cl]]. clear Sr H_obj.
          destruct e_cl.
          refine (symb_raw (inl S_R : Metavariable_Extension _ _) _).
          change (arity (inl S_R : Metavariable_Extension _ _))
            with (arity S_R). 
          set (aR := arity S_R) in *. destruct (e_a^); clear e_a.
          intros [P | i].
          -- cbn in P.
            refine (symb_raw (inr P : Metavariable_Extension _ _) _).
            intros i.
            apply var_raw.
            apply (coproduct_inj1 shape_is_coproduct).
            exact (coproduct_inj2 shape_is_coproduct i).
          -- apply var_raw.
            exact (coproduct_inj1 shape_is_coproduct i).
        * (* case: R an equality rule *)
          destruct H_obj. (* ruled out by assumption *)
  Admitted.

End RuleSpecs.

Arguments Rule_Spec {_} _ _ _ _.

(** Specification of a type theory (but before checking that syntax in rules is well-typed. *)

Section TTSpecs.

  Context (σ : Shape_System).

  Record Type_Theory_Spec
  := {
  (* The family of _rules_, with their object-premise arities and conclusion forms specified *)
    TTS_Rule : Family (Hyp_Judgt_Form * Arity σ * Shape σ)
  (* the ordering relation on the rules *)
  (* TODO: somewhere we will want to add that this is well-founded; maybe more *)
  (* the judgement form of the conclusion of each rule *)
  ; TTS_hjf_of_rule : TTS_Rule -> Hyp_Judgt_Form
    := fun i => fst (fst (TTS_Rule i))
  (* the arity of the arguments (i.e. the *object* premises only) of each rule *)
  ; TTS_arity_of_rule : TTS_Rule -> Arity _
    := fun i => snd (fst (TTS_Rule i))
  (* the shape of the conclusion of each rule *)
  ; TTS_concl_shape_of_rule : TTS_Rule -> Shape σ
    := fun i => snd (TTS_Rule i)
  (* the ordering on rules.  TODO: will probably need to add well-foundedness *)
  ; TTS_lt : TTS_Rule -> TTS_Rule -> hProp
  (* the signature over which each rule can be written *)
  ; TTS_signature_of_rule : TTS_Rule -> Signature σ
    := fun i => Fmap
        (fun jaγ => ( class_of_HJF (fst (fst jaγ))
                   , Family.Sum (snd (fst jaγ)) (simple_arity (snd jaγ))))
        (Subfamily TTS_Rule
          (fun j => is_obj_HJF (TTS_hjf_of_rule j) * TTS_lt j i))
  (* the actual rule specification of each rule *)
  ; TTS_rule_spec
    : forall i : TTS_Rule,
        Rule_Spec
          (TTS_signature_of_rule i)
          (TTS_arity_of_rule i)
          (TTS_concl_shape_of_rule i)
          (TTS_hjf_of_rule i)
  }.

End TTSpecs.

Arguments TTS_Rule {_} _.
Arguments TTS_hjf_of_rule {_ _} _.
Arguments TTS_arity_of_rule {_ _} _.
Arguments TTS_concl_shape_of_rule {_ _} _.
Arguments TTS_lt {_ _} _ _.
Arguments TTS_signature_of_rule {_ _} _.
Arguments TTS_rule_spec {_ _} _.

