Require Import HoTT.
Require Import Family.
Require Import ShapeSystems.
Require Import Coproduct.
Require Import DeductiveClosure.
Require Import RawSyntax.

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
  (Σ : Signature Proto_Cxt)
  (a : Arity Proto_Cxt)
  (hjf_conclusion : Hyp_Judgt_Form)
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    RS_equality_premise : Arity Proto_Cxt
  (* family indexing the premises of the rule, and giving for each: *)
  ; RS_Premise : Family (Hyp_Judgt_Form * Proto_Cxt)
    := Family.Sum
         (Family.Fmap (fun cl_γ => (obj_HJF (fst cl_γ), snd cl_γ)) a)
         (Family.Fmap (fun cl_γ => (obj_HJF (fst cl_γ), snd cl_γ)) RS_equality_premise)
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
  (* syntactic part of context of premise; this should never be used directly, always through [RS_raw_context_of_premise] *)
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
  (* judgement boundary instance of conclusion *)
  ; RS_judgt_bdry_instance_of_conclusion
      : Judgt_Form_Instance
          (Metavariable_Extension Σ RS_arity)
          (HJF RS_hjf_of_conclusion)
  }.

End RuleSpecs.

(** Specification of a type theory (but before checking that syntax in rules is well-typed. *)

Section TTSpecs.

  Context (σ : Shape_System).

  Record Type_Theory_Spec
  := {
  (* The family of _rules_, with their object-premise arities and conclusion forms specified *)
    TTS_Rule : Family (Hyp_Judgt_Form * Arity σ)
  (* the ordering relation on the rules *)
  (* TODO: somewhere we will want to add that this is well-founded; maybe more *)
  (* the judgement form of the conclusion of each rule *)
  ; TTS_hjf_of_rule : TTS_Rule -> Hyp_Judgt_Form
    := fun i => fst (TTS_Rule i)
  (* the arity (of the *object* premises only) of each rule *)
  ; TTS_arity_of_rule : TTS_Rule -> Arity _
    := fun i => snd (TTS_Rule i)
  (* the ordering on rules.  TODO: will probably need to add well-foundedness *)
  ; TTS_lt : TTS_Rule -> TTS_Rule -> hProp
  (* the signature over which each rule can be written *)
  ; TTS_signature_of_rule : TTS_Rule -> Signature σ
    := fun i => Fmap
        (fun jγ => (class_of_HJF (fst jγ), snd jγ))
        (Subfamily TTS_Rule
          (fun j => is_obj_HJF (TTS_hjf_of_rule j) * TTS_lt j i))
  (* the actual rule specification of each rule *)
  ; TTS_rule_spec
    : forall i : TTS_Rule,
        Rule_Spec
          (TTS_signature_of_rule i)
          (TTS_arity_of_rule i)
          (TTS_hjf_of_rule i)
  }.

End TTSpecs.

Arguments TTS_Rule {_} _.
Arguments TTS_hjf_of_rule {_ _} _.
Arguments TTS_arity_of_rule {_ _} _.
Arguments TTS_lt {_ _} _ _.
Arguments TTS_signature_of_rule {_ _} _.
Arguments TTS_rule_spec {_ _} _.

