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

  Local Definition type_object_boundary : family syntactic_class := [< >].

  Local Definition term_object_boundary := [< class_type >].

  (* The boundary of a term or a type. *)
  Local Definition object_boundary_slot (cl : syntactic_class) : family syntactic_class
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => type_object_boundary
       (* Boundary of a term judgement: the type of the term *)
       | class_term => term_object_boundary
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
    destruct jf as [ | hjf ].
    - (* context judgement: no boundary *)
      constructor.
    - (* hypothetical judgement *)
      exists (pr1 j). (* the context of the boundary is the context of the
                         original judgement *)
      destruct hjf as [ ob_hjf | eq_hjf ].
      + (* object judgement *)
        intro slot ; exact (pr2 j (Some slot)).
      + (* equality judgement *)
        intro slot ; exact (pr2 j slot).
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
    intros [ [ [] | ] | ].
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
    intros [ [ [ [] | ] | ] | ].
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
    - destruct i as [[] |]; destruct j.
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

  (** The presuppositions of a judgment boundary [jb] *)
  Definition presupposition_of_boundary
      {Σ : signature σ} {jf} (jb : boundary Σ jf)
    : family (judgement_total Σ).
  Proof.
  (* Note: destructing [jf] once early makes this definition look cleaner.

   However, destructing [jf] as late as possible, and clearing [jb] when
   possible, gives stronger computational behaviour:
   it keeps the index set and judgement forms independent of [Σ], [jb]. *)
    simple refine (Build_family _ _ _).
    - clear jb. destruct jf as [ | hjf].
      + (* context judgement: no boundary *)
        exact Empty.
      + (* hyp judgement: presups are the context,
                        plus the slots of the hyp boundary *)
        exact (option (boundary_slot hjf)).
    - intros i; simple refine (_;_).
      + clear jb. destruct jf as [ | hjf].
        * destruct i as [].
        * destruct i as [ i | ].
          -- exact (form_hypothetical (form_object ((boundary_slot hjf) i))).
          -- exact form_context.
      +  destruct jf as [ | hjf].
         * destruct i as [].
         * destruct i as [ i | ].
           -- exists (pr1 jb).
              intros j.
              refine (transport (fun cl => raw_expression _ cl _) _ _).
              ++ exact (Family.map_commutes (presupposition_from_boundary_slots i) j).
              ++ exact (pr2 jb (presupposition_from_boundary_slots i j)).
           -- exact (pr1 jb).
  Defined.

  (** The presuppositions of judgement [j]. *)
  Definition presupposition
      {Σ : signature σ} (j : judgement_total Σ)
    : family (judgement_total Σ)
  := presupposition_of_boundary (boundary_of_judgement (pr2 j)).

End Presupposition.


(** A tactic that is often handy working with syntax, especially slots:
recursively destruct some object of an iterated inductive type. 

Currently only supports specific inductive types hand-coded here. *)
(* TODO: can this be generalised to work for arbitrary inductive types? *)
Ltac recursive_destruct x :=
    cbn in x;
    try match type of x with
    | hypothetical_form => destruct x as [ cl | cl ]; recursive_destruct cl
    | syntactic_class => destruct x as [ | ]
    | option _ => destruct x as [ y | ]; [recursive_destruct y | idtac ]
    | Empty => destruct x
    | Unit => destruct x as []
    | sum _ _ => destruct x as [ y | y ]; recursive_destruct y
    | sig _ => destruct x as [ x1 x2 ];
       recursive_destruct x1; recursive_destruct x2
    | _ => idtac
    end.
