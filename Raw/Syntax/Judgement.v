Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.Signature.
Require Import Raw.Syntax.SyntacticClass.
Require Import Raw.Syntax.Expression.
Require Import Raw.Syntax.Context.

Section JudgementDefinitions.
  Context {σ : shape_system}.
  Context (Σ : signature σ).

  (* The basic hypothetical judgments forms. *)
  Inductive hypothetical_form : Type :=
  | form_object (cl : syntactic_class) (* a thing is a term, a thing is a type *)
  | form_equality (cl : syntactic_class). (* terms are equal, types are equal *)

  Local Definition is_object : hypothetical_form -> Type
    := fun jf => match jf with
                     | form_object _ => Unit
                     | form_equality _ => Empty
                  end.

  Local Definition class_of : hypothetical_form -> syntactic_class
    := fun jf => match jf with
                     | form_object cl => cl
                     | form_equality cl => cl
                  end.

  (* Contexts are also a judgement form. *)
  Inductive form : Type :=
    | form_context
    | form_hypothetical (hjf : hypothetical_form).

  (* The boundary of a term or a type. *)
  Local Definition object_boundary_slot (cl : syntactic_class) : family syntactic_class
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => [< >]
       (* Boundary of a term judgement: the type of the term *)
       | class_term => [< class_type >]
     end.

  (* Syntactic classes of the slots in the boundary of a hypothetical judgement *)
  Local Definition boundary_slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* object judgement boundary is the boundary of the object *)
       | form_object cl => object_boundary_slot cl
       (* equality judgement boundary: a boundary of the corresponding object-judgement,
          together with two objects of the given class *)
       | form_equality cl  => Family.adjoin (Family.adjoin (object_boundary_slot cl) cl) cl
     end.

  (* Syntactic classes of the slots in a hypothetical judgement *)
  Local Definition slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* Equality case: boundary is everything *)
       | form_equality cl =>
           boundary_slot (form_equality cl)
       (* Object case: add the head slot *)
       | form_object cl =>
           Family.adjoin (boundary_slot (form_object cl)) cl
     end.
  (* NOTE: the order of slots for term judgements follows “dependency order” — later slots are (morally) dependent on earlier ones, so the type comes before the term.  However, the functions in section [Judgement_Notations] below follow standard written order, so the term comes before the type. *)

  Local Definition hypothetical_boundary (hjf : hypothetical_form) γ : Type
    := forall i : boundary_slot hjf, raw_expression Σ (family_element _ i) γ.

  Definition hypothetical_judgement (hjf : hypothetical_form) γ : Type
    := forall i : slot hjf, raw_expression Σ (family_element _ i) γ.

  Local Definition boundary (jf : form) : Type
    := match jf with
       | form_context => Unit
       | form_hypothetical hjf =>
          { Γ : raw_context Σ & hypothetical_boundary hjf Γ }
     end.

  Definition judgement (jf : form) : Type
    := match jf with
       | form_context => raw_context Σ
       | form_hypothetical hjf =>
         { Γ : raw_context Σ & hypothetical_judgement hjf Γ }
       end.

  (* NOTE [AB]: I know the name [judgement_total] is ugly, but I do not want to introduce "instance" all over the place.
      Will first check to see which types are most frequently mentioned in the rest of the code. *)
  (* NOTE: if [judgement_total] is renamed to [judgement] and [judgement] to [judgement_instance], then [Judgement.fmap] and [fmap_judgement_total] below should be renamed accordingly (among many other things). *)
  Definition judgement_total
    := { jf : form & judgement jf }.

  Local Definition hypothetical_instance_from_boundary_and_head
      {hjf : hypothetical_form} {γ}
      (bdry : hypothetical_boundary hjf γ)
      (head : is_object hjf -> raw_expression Σ (class_of hjf) γ)
    : hypothetical_judgement hjf γ.
  Proof.
    destruct hjf as [ ocl | ecl ].
    - (* case: object judgement *)
      intros [ i | ].
      + apply bdry.
      + apply head. constructor.
    - (* case: equality judgement *)
      apply bdry.
  Defined.

  Definition boundary_of_judgement
      {jf} (j : judgement jf)
    : boundary jf.
  Proof.
    destruct jf as [ | hjf].
    - constructor. (* context judgement: no boundary *)
    - (* hyp judgement *)
      cbn in j. exists (pr1 j). intros i.
      destruct hjf as [ ob_hjf | eq_hjf ].
      + exact (pr2 j (Some i)).
      + exact (pr2 j i).
  Defined.

End JudgementDefinitions.

Arguments hypothetical_boundary : simpl nomatch.
Arguments boundary_of_judgement {_ _ _} _ : simpl nomatch.

Section JudgementFmap.

  Context {σ : shape_system}.

  Local Definition fmap_hypothetical_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {hjf} {γ}
    : hypothetical_boundary Σ hjf γ -> hypothetical_boundary Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Expression.fmap f), hjbi.
  Defined.

  Local Definition fmap_hypothetical_judgement
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {hjf} {γ}
    : hypothetical_judgement Σ hjf γ -> hypothetical_judgement Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Expression.fmap f), hjbi.
  Defined.

  (* NOTE: if [judgement_total] is renamed to [judgement] and [judgement] to [judgement_instance], then [Judgement.fmap] and [fmap_judgement_total] below should be renamed accordingly. *)
  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf}
    : judgement Σ jf -> judgement Σ' jf.
  Proof.
    destruct jf as [ | hjf].
    - apply Context.fmap, f.
    - cbn. intros Γ_hjfi.
      exists (Context.fmap f Γ_hjfi.1).
      exact (fmap_hypothetical_judgement f Γ_hjfi.2).
  Defined.

  (* NOTE: if [judgement_total] is renamed to [judgement] and [judgement] to [judgement_instance], then [Judgement.fmap] and [fmap_judgement_total] below should be renamed accordingly. *)
  Local Definition fmap_judgement_total {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : judgement_total Σ -> judgement_total Σ'.
  Proof.
    intros jf_jfi.
    exists jf_jfi.1.
    exact (fmap f jf_jfi.2).
  Defined.

End JudgementFmap.

Section JudgementNotations.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition make_context_ji
        (Γ : raw_context Σ)
    : judgement_total Σ.
  Proof.
    exists form_context.
    exact Γ.
  Defined.

  Local Definition make_type_ji
        (Γ : raw_context Σ) (A : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_object class_type)).
    exists Γ.
    intros [ [] | ]; exact A.
  Defined.

  Local Definition make_type_equality_ji
             (Γ : raw_context Σ)
             (A A' : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equality class_type)).
    exists Γ.
    intros [ [ [] | ] | ].
    exact A.
    exact A'.
  Defined.

  Local Definition make_term_ji
             (Γ : raw_context Σ) (a : raw_term Σ Γ) (A : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_object class_term)).
    exists Γ.
    intros [ [] | ].
    exact A.
    exact a.
  Defined.

  (* TODO: consistentise order with [make_term_ji]. *)
  Local Definition make_term_equality_ji
             (Γ : raw_context Σ) (A : raw_type Σ Γ) (a a': raw_term Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equality class_term)).
    exists Γ.
    intros [ [ [] | ] | ].
    exact A.
    exact a.
    exact a'.
  Defined.

End JudgementNotations.

Notation "'[Cxt!' |- Γ !]" := (make_context_ji Γ) : judgement_scope.
Notation "'[Ty!' Γ |- A !]" := (make_type_ji Γ A) : judgement_scope.
Notation "'[TyEq!' Γ |- A ≡ A' !]" := (make_type_equality_ji Γ A A') : judgement_scope.
Notation "'[Tm!' Γ |- a ; A !]" :=  (make_term_ji Γ a A) : judgement_scope.
Notation "'[TmEq!' Γ |- a ≡ a' ; A !]" := (make_term_equality_ji Γ A a a') : judgement_scope.

Open Scope judgement_scope.

Section Presupposition.
(** TODO: the naming in this section seems a bit ugly. *)

(** Whenever an object appears in the boundary of an object judgement, then its
    boundary embeds into that boundary.

    NOTE. This is a special case of [presup_slots_from_boundary] below. It is
    abstracted out because it’s used twice: directly for object judgements, and
    as part of the case for equality judgements.

    In fact it’s almost trivial, so could easily be inlined; but conceptually it
    is the same thing both times, and in type theory with more judgements, it
    would be less trivial, so we keep it factored out. *)

  Local Definition object_boundary_from_boundary_slots
    {cl : syntactic_class} (i : object_boundary_slot cl)
    : Family.map
        (object_boundary_slot (object_boundary_slot cl i))
        (object_boundary_slot cl).
  Proof.
    apply Family.Build_map'. intros j.
    destruct cl as [ | ]; cbn in i.
    (* Ty: nothing to do, no objects in boundary *)
    - destruct i.
    (* Tm: i must be type, so again nothing left, no j in its boundary *)
    - destruct i as []; destruct j.
  Defined.

(** Wherever an judgement [I] occurs as a presupposition of a judgement [J],
there is a canonical embedding of the slots of [I] into the slots of [J]. *)
  Local Definition presupposition_from_boundary_slots
    {hjf : hypothetical_form} (i : boundary_slot hjf)
    : Family.map
        (slot (form_object (boundary_slot hjf i)))
        (boundary_slot hjf).
  Proof.
    apply Family.Build_map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct hjf as [ cl | cl ].
      + (* original hjf is object judgement *)
        exists (object_boundary_from_boundary_slots i j).
        apply (Family.map_commutes _ j).
      + (* original hjf is equality judgement *)
        destruct i as [ [i' | ] | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists (Some (Some (object_boundary_from_boundary_slots i' j))).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (Some (Some j)). apply idpath.
        * (* i is LHS *)
          exists (Some (Some j)). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.

  Context {σ : shape_system}.

  (** The presuppositions of judgment boundary [jbi] *)
  Local Definition presupposition_of_boundary
      {Σ : signature σ} {jf} (jbi : boundary Σ jf)
    : family (judgement_total Σ).
  Proof.
    destruct jf as [ | hjf].
    - (* context judgement: no boundary *)
      apply Family.empty.
    - (* hyp judgement: presups are the context,
                        plus the slots of the hyp boundary *)
      apply Family.adjoin.
      + exists (boundary_slot hjf).
        intros i.
        exists (form_hypothetical (form_object ((boundary_slot hjf) i))).
        exists (pr1 jbi).
        intros j.
        set (p := Family.map_commutes (presupposition_from_boundary_slots i) j).
        set (j' := presupposition_from_boundary_slots i j) in *.
        destruct p.
        exact (pr2 jbi j').
      + exists (form_context).
        exact (pr1 jbi).
  Defined.

  (** The presuppositions of judgement [j]. *)
  Local Definition presupposition
      {Σ : signature σ} (j : judgement_total Σ)
    : family (judgement_total Σ)
  := presupposition_of_boundary (boundary_of_judgement (pr2 j)).

End Presupposition.
