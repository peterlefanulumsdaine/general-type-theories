Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.SyntaxLemmas.

Section Algebraic_Extensions.

Context {σ : shape_system} {Σ : signature σ}.

Record algebraic_extension
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
  (* for each premise, the arity specifying what metavariables are available
  in the syntax for this premise; i.e., the type/term arguments already
  introduced by earlier premises *)
  ; ae_metas : ae_premise -> arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  ; ae_signature : ae_premise -> signature _
    := fun i => Metavariable.extend Σ (ae_metas i)
  (* syntactic part of context of premise *)
  (* NOTE: should never be used directly, always through [ae_raw_context] *)
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

Arguments algebraic_extension _ : clear implicits.

(* TODO: make the record argument implicit in most fields. *)

Local Definition premise_boundary
    {a} {A : algebraic_extension a} (r : A)
  : Judgement.boundary (ae_signature _ r)
                       (form_hypothetical (ae_form _ r)).
Proof.
  exists (ae_raw_context _ r).
  apply (ae_hypothetical_boundary).
Defined.

Local Definition eq_premise {a : arity σ}
    {A_eqp A'_eqp : arity σ} (e : A_eqp = A'_eqp)
    (f_ob : (_ -> _) := (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)))
    (f_eq : (_ -> _) := (fun cl_γ => (form_equality (fst cl_γ), snd cl_γ)))
  : Family.map (Family.fmap f_ob a + Family.fmap f_eq A_eqp)
               (Family.fmap f_ob a + Family.fmap f_eq A'_eqp).
Proof.
  destruct e. apply Family.idmap.
Defined.

Local Definition eq_metas {a : arity _}
    {A_eqp A'_eqp : arity σ} (e_eqp : A_eqp = A'_eqp) 
    {A_lt : well_founded_order (a + A_eqp)}
    {A'_lt : well_founded_order (a + A'_eqp)}
    (e_lt : transport (fun K => well_founded_order (Family.sum _ K))
                      e_eqp A_lt = A'_lt)
  : forall i : (a + A_eqp),
    Family.map (Family.subfamily a (fun j => A_lt (inl j) i))
      (Family.subfamily a (fun j => A'_lt (inl j)
        (eq_premise e_eqp i))).                  
Proof.
  destruct e_eqp, e_lt. intros; apply Family.idmap.
Defined.

(*TODO: upstream to [SyntaxLemmas] *)
Local Lemma rename_hypothetical_boundary_idmap `{Funext}
      {Σ'} {γ : σ} {hjf} (B : Judgement.hypothetical_boundary Σ' hjf γ)
    : rename_hypothetical_boundary idmap B = B.
Proof.
  apply path_forall; intros i.
  apply rename_idmap.
Defined.

Local Definition eq `{Funext} {a}
    {A A' : algebraic_extension a}
    (e_premises : ae_equality_premise A = ae_equality_premise A')
    (e_lt : transport
              (fun K => well_founded_order (_ + Family.fmap _ K))
              e_premises
              (ae_lt A)
            = ae_lt A')
    (equiv_premise : ae_premise A -> ae_premise A' := eq_premise e_premises)
    (fe_signature : forall i : ae_premise A,
      Signature.map (ae_signature A i) (ae_signature A' (equiv_premise i))
      := fun i => Metavariable.fmap2 _ (eq_metas e_premises e_lt i))
    (fe_shape : forall i : ae_premise A,
        (ae_shape A i <~> ae_shape A' (equiv_premise i))
      := fun i => equiv_path _ _ (ap _ (ap _ (Family.map_commutes _ i)^)))
    (e_raw_context : forall (i : ae_premise A) (j : _),
        Expression.fmap (fe_signature i) (ae_raw_context A i j)
        = rename (equiv_inverse (fe_shape i))
                 (ae_raw_context A' _ (fe_shape i j)))
    (e_hypothetical_boundary
       : forall i : ae_premise A,
        rename_hypothetical_boundary (fe_shape i)
        (fmap_hypothetical_boundary (fe_signature i)
        (transport (fun hjf => Judgement.hypothetical_boundary _ hjf _)
                   (ap fst (Family.map_commutes (eq_premise e_premises) i)^)
        (ae_hypothetical_boundary A i)))
        = ae_hypothetical_boundary A' (equiv_premise i))
  : A = A'.
Proof.
  destruct A, A'; cbn in e_premises, e_lt.
  destruct e_premises, e_lt; simpl in *.
  refine
    (ap (Build_algebraic_extension _ _ _ _) _
    @ ap (fun rc => Build_algebraic_extension _ _ _ rc _) _).
  - clear ae_raw_context0 ae_raw_context1 e_raw_context.
    apply path_forall; intros i.
    refine (_ @ e_hypothetical_boundary i). apply inverse.
    eapply concat.
    { unfold transport. apply rename_hypothetical_boundary_idmap. }
    unfold fe_signature.
    eapply concat.
    { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
      apply Metavariable.fmap2_idmap. }
    apply fmap_hypothetical_boundary_idmap.
  - clear e_hypothetical_boundary.
    apply path_forall; intros i.
    apply path_forall; intros j.  
    refine (_ @ e_raw_context i j @ _).
    + unfold fe_signature.
    eapply inverse, concat.
    { refine (ap (fun f => Expression.fmap f _) _).
      apply Metavariable.fmap2_idmap. }
    apply Expression.fmap_idmap.
    + unfold equiv_premise, transport.
      apply rename_idmap.
Defined.

End Algebraic_Extensions.

Arguments algebraic_extension {_} _ _.

Section Functoriality.

  Context {σ : shape_system}.

  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : algebraic_extension Σ' a.
  Proof.
    simple refine {| ae_equality_premise := ae_equality_premise A ;
                     ae_lt := ae_lt A |}.
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
  Defined.

  Context `{Funext}.

  Local Definition fmap_idmap
      {Σ} {a} (A : algebraic_extension Σ a)
    : fmap (Signature.idmap _) A = A.
  Proof.
  Admitted.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : fmap (Signature.compose f' f) A = fmap f' (fmap f A).
  Proof.
  Admitted.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : fmap f' (fmap f A) = fmap (Signature.compose f' f) A.
  Proof.
    apply inverse, fmap_compose.
  Defined.

End Functoriality.

Section Flattening.

  Context {σ : shape_system} {Σ : signature σ}.

  (* In flattening an algebraic extension (or rule), and in other settings (e.g. type-checking the premises), we often want to extract premises as judgements.

   We need to do this into several different signatures, so in this lemma, we isolate exactly what is required: a map from the signature of this premise, plus (in case the premise is an object premise) a symbol to use as the head of the judgement, i.e. the metavariable introduced by the premise. *)
  (* TODO: consider whether the flattening of the conclusion of rules can also be unified with this. *)
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
    - refine (Judgement.fmap_hypothetical_boundary f _).
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

  Local Definition flatten {a}
    (A : algebraic_extension Σ a)
  : family (judgement_total (Metavariable.extend Σ a)).
  (* This construction involves essentially two aspects:

     - translate the syntax of each expression in the rule from its “local”
       signatures to the overall signature;

     - reconstruct the head terms of the object premises *)
  Proof.
    exists (ae_premise A).
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
  Defined.

End Flattening.