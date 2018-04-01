(** * Well-shaped rules *)

Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.AlgebraicExtension.

(** A well-shaped rule is given by the following data:

   - [rule]: the data one gives to specify a logical rule (before any typechecking)
   - [associated_congruence_rule]
   - [flatten]
*)

(** Specification of well-shaped rules *)
Section WellShapedRule.

Context {σ : shape_system}.

(** An (ordered, raw) rule consists of premises and a conclusion. For various reasons, we
    abstract the form of the premises as an _algebraic extension_.

    Such an extension can add both object premises (introducing type/term premises) and
    equality premises.

    Besides being viewed as the premises of a rule, the premises can be seen as
    particularly simple rules themselves for extending a type theory. Viewed this way,
    they are _algebraic_ in the sense that it does not introduce any new binders, and only
    take term arguments (no type arguments). This is the raw-syntax analogue of an arity
    seen as specifying the metavariable-extension of a signature.
*)

(** The parameters of a rule, beyond its ambient signature, may be a little
    counter-intuitive. The point is that they are just what is required to
    determine the arity of the symbol introduced by the rule (if it’s an object
    rule), and in any case the arity of its associated flat rule. *)
Record rule
  {Σ : signature σ}
  {a : arity σ} (* arity listing the _object_ premises of the rule *)
  {hjf_conclusion : Judgement.hypothetical_form} (* judgement form of the conclusion *)
:=
  {
    rule_premise : algebraic_extension Σ a
  ; rule_conclusion_hypothetical_boundary
      : Judgement.hypothetical_boundary
          (Metavariable.extend Σ a)
          hjf_conclusion
          (shape_empty σ)
  }.

(* NOTE 1. One could generalise rules by allowing the context of the conclusion to be non-empty.

 This would slightly complicate this definition, and subsequent constructions, and would (one expects) not add any real generality, since one can always move variables from that context to become extra premises, giving an equivalent rule with empty conclusion context (where the equivalence makes use of the “cut”/substitution rule).

  However, it could be nice (a) since rules are sometimes written this way in practice, and (b) to allow a precise theorem stating the claim above about it being equivalent to move variables into the premises.

  On the other hand, so long as the _flattened_ rules [flat_rule] allow arbitrary conclusion judgements, one can still use those to give a lemma about the equivalence. *)

  (* NOTE 2. Perhaps the parameters of the definition of [rule] could be profitably abstracted into a “proto-rule” (probably including also the arity [ae_equality_premise]), fitting the pattern of the stratificaiton of objects into proto ≤ raw ≤ typed. *)

  Arguments rule _ _ _ : clear implicits.

  (* This does not seem to be needed, and in any case has a silly name. *)
  (* (* Template for defining rules: *) *)
  (* Definition Example {Σ} {a} {hjf} : rule Σ a hjf. *)
  (* Proof. *)
  (*   simple refine (Build_rule _ _ _ _ _). *)
  (*   simple refine (Build_algebraic_extension _ _ _ _ _ _). *)
  (*   - admit. (* ae_equality_premise: arity specifying equality premises *) *)
  (*   - admit. (* ae_lt *) *)
  (*   - admit. (* ae_raw_context_type *) *)
  (*   - admit. (* ae_hypothetical_boundary *) *)
  (*   - admit. (* rule_conclusion_hypothetical_boundary *) *)
  (* Abort. *)

  Local Definition conclusion_boundary {Σ} {a} {hjf} (R : rule Σ a hjf)
    : Judgement.boundary (Metavariable.extend Σ a) (form_hypothetical hjf)
  := ([::]; rule_conclusion_hypothetical_boundary R).

  Local Definition fmap
      {Σ} {Σ'} (f : Signature.map Σ Σ')
      {a} {hjf_concl}
      (R : rule Σ a hjf_concl)
    : rule Σ' a hjf_concl.
  Proof.
    simple refine (Build_rule Σ' a hjf_concl _ _).
    simple refine {| ae_equality_premise := ae_equality_premise (rule_premise R) ;
                     ae_lt := ae_lt (rule_premise R) |}.
    - (* ae_raw_context_type *)
      intros i v.
      refine (_ (ae_raw_context_type _ i v)).
      apply Expression.fmap, Metavariable.fmap1, f.
    - (* ae_hypothetical_boundary *)
      intros i.
      simple refine
        (fmap_hypothetical_boundary
          _ (ae_hypothetical_boundary _ i)).
      apply Metavariable.fmap1, f.
    - (* rule_conclusion_hypothetical_boundary *)
      simple refine
        (fmap_hypothetical_boundary
          _ (rule_conclusion_hypothetical_boundary R)).
      apply Metavariable.fmap1, f.
  Defined.

End WellShapedRule.

(* globalise argument declarations *)
Arguments algebraic_extension {_} _ _.
Arguments rule {_} _ _ _.


Module Span.
(** Some auxiliary constructions for defining the ordering of the premises in the
    associated congruence rule of a constructor. *)

  Local Inductive span : Type :=
    left | right | top.

  Local Definition lt_relation : relation span
  := fun x y => match x, y with
                | left, top => True
                | right, top => True
                | x, y => False
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


(* Each (ordered) rule induces one or two flat rules: the logical rule itself,
   and (if it was an object rule) its associated congruence rule.*)

Section Flattening.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* In flattening a rule, and in other settings (e.g. type-checking the premises), we often want to extract premises as judgements.

   We need to do this into several different signatures, so in this lemma, we isolate exactly what is required: a map from the signature of this premise, plus (in case the premise is an object premise) a symbol to use as the head of the judgement, i.e. the metavariable introduced by the premise. *)
  (* TODO: consider whether the flattening of the conclusion can also be covered by this. *)
  Local Definition judgement_of_premise
      {a} {A : algebraic_extension Σ a} (i : A)
      {Σ'} (f : Signature.map (ae_signature _ i) Σ')
      (Sr : Judgement.is_object (ae_form _ i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_shape _ i))
             * (symbol_class S = Judgement.class_of (ae_form _ i))})
   : judgement_total Σ'.
  Proof.
    exists (form_hypothetical (ae_form _ i)).
    exists (Context.fmap f (ae_raw_context _ i)).
    apply Judgement.hypothetical_instance_from_boundary_and_head.
    - refine (fmap_hypothetical_boundary f _).
      apply ae_hypothetical_boundary.
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

  (* Flattening a rule requires no extra information in the case of an
  equality-rule; in the case of an object-rule, it requires a symbol of
  appropriate arity to give the object introduced. *)
  Local Definition flatten
    {a} {hjf_concl}
    (R : rule Σ a hjf_concl)
    (Sr : Judgement.is_object hjf_concl
        -> { S : Σ & (symbol_arity S = a) * (symbol_class S = Judgement.class_of hjf_concl) })
  : flat_rule Σ.
  (* This construction involves essentially two aspects:

     - translate the syntax of each expression in the rule from its “local”
       signatures to the overall signature;

     - reconstruct the head terms of the object premises and the conclusion *)
  Proof.
    refine (Build_flat_rule _ a _ _).
    - (* premises *)
      exists (rule_premise R).
      intros i.
      apply (judgement_of_premise i).
      + apply Metavariable.fmap2.
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
      exists (pr1 (conclusion_boundary R)).
      apply Judgement.hypothetical_instance_from_boundary_and_head.
      + exact (pr2 (conclusion_boundary R)).
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
