Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.

Record algebraic_extension
  {σ : shape_system}
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
  ; ae_form : ae_premise -> Judgement.hypothetical_form
    := fun i => fst (ae_premise i)
  (* - the proto-context of each premise *)
  ; ae_shape : ae_premise -> σ
    := fun i => snd (ae_premise i)
  (* the ordering relation on the premises *)
  ; ae_lt : well_founded_order ae_premise
  (* for each premise, the arity specifying what metavariables are available in the syntax
     for this premise; i.e., the family of type/term arguments already introduced by earlier
     premises *)
  ; ae_metas : ae_premise -> arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  ; ae_signature : ae_premise -> signature _
    := fun i => Metavariable.extend Σ (ae_metas i)
  (* syntactic part of context of premise *)
  (* NOTE: this should never be used directly, always through [ae_raw_context] *)
  ; ae_raw_context_type
    : forall (i : ae_premise) (v : ae_shape i),
        raw_type
          (ae_signature i)
          (ae_shape i)
  (* raw context of each premise *)
  ; ae_raw_context
    : forall i : ae_premise,
        raw_context (ae_signature i)
    := fun i => Build_raw_context _ (ae_raw_context_type i)
  (* hypothetical judgement boundary instance for each premise *)
  ; ae_hypothetical_boundary
    : forall i : ae_premise,
        Judgement.hypothetical_boundary
          (ae_signature i)
          (ae_form i)
          (ae_shape i)
  }.

Arguments algebraic_extension {_} _ _.
(* TODO: make the record argument implicit in most fields. *)

Local Definition judgement_boundary
    {σ : shape_system}
    {Σ : signature σ} {a}
    {A : algebraic_extension Σ a} (r : A)
  : Judgement.boundary (ae_signature _ r)
                       (form_hypothetical (ae_form _ r)).
Proof.
  exists (ae_raw_context _ r).
  apply (ae_hypothetical_boundary).
Defined.
