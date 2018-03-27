Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Presyntax.
Require Import Raw.Expression.
Require Import Raw.Context.

Section Judgement.
  Context {σ : shape_system}.
  Context (Σ : signature σ).

  (* The basic hypothetical judgments forms. *)
  Inductive hypothetical_form : Type :=
  | form_object (cl : syntactic_class) (* a thing is a term, a thing is a type *)
  | form_equation (cl : syntactic_class). (* terms are equal, types are equal *)

  Local Definition is_object : hypothetical_form -> Type
    := fun jf => match jf with
                     | form_object _ => Unit
                     | form_equation _ => Empty
                  end.

  Local Definition class_of : hypothetical_form -> syntactic_class
    := fun jf => match jf with
                     | form_object cl => cl
                     | form_equation cl => cl
                  end.

  (* Contexts are also a judgement form. *)
  Inductive form : Type :=
    | form_context
    | form_hypothetical (hjf : hypothetical_form).

  (* The boundary of a term or a type. *)
  Local Definition object_boundary_slot (cl : syntactic_class)
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => [< >]
       (* Boundary of a term judgement: the type of the term *)
       | class_term => [< class_type >]
     end.

  (* Syntactic classes of the slots in the boundary of a hypothetical judgement *)
  Local Definition hypothetical_boundary_slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* object judgement boundary is the boundary of the object *)
       | form_object cl => object_boundary_slot cl
       (* equality judgement boundary: a boundary of the corresponding object-judgement,
          together with two objects of the given class *)
       | form_equation cl  => Family.adjoin (Family.adjoin (object_boundary_slot cl) cl) cl
     end.

  (* Syntactic classes of the slots in a hypothetical judgement *)
  Local Definition hypothetical_form_slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* Equality case: boundary is everything *)
       | form_equation cl =>
           hypothetical_boundary_slot (form_equation cl)
       (* Object case: add the head slot *)
       | form_object cl =>
           Family.adjoin (hypothetical_boundary_slot (form_object cl)) cl
     end.
  (* NOTE: the order of slots for term judgements follows “dependency order” — later slots are (morally) dependent on earlier ones, so the type comes before the term.  However, the functions in section [Judgement_Notations] below follow standard written order, so the term comes before the type. *)

  Local Definition hypothetical_boundary (hjf : hypothetical_form) γ : Type
    := forall i : hypothetical_boundary_slot hjf, raw_expression Σ (family_element _ i) γ.

  Definition hypothetical_judgement (hjf : hypothetical_form) γ : Type
    := forall i : hypothetical_form_slot hjf, raw_expression Σ (family_element _ i) γ.

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

  (** I know this is ugly, but I do not want to introduce "instance" all over the place.
      Will first check to see which types are most frequently mentioned in the rest of the
      code. *)
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

End Judgement.


Section Judgement_Notations.

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

  Local Definition make_type_equation_ji
             (Γ : raw_context Σ)
             (A A' : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equation class_type)).
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
  Local Definition make_term_equation_ji
             (Γ : raw_context Σ) (A : raw_type Σ Γ) (a a': raw_term Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equation class_term)).
    exists Γ.
    intros [ [ [ [] | ] | ] | ].
    exact A.
    exact a.
    exact a'.
  Defined.

End Judgement_Notations.

Notation "'[Cxt!' |- Γ !]" := (make_context_ji Γ) : judgement_scope.
Notation "'[Ty!' Γ |- A !]" := (make_type_ji Γ A) : judgement_scope.
Notation "'[TyEq!' Γ |- A ≡ A' !]" := (make_type_equation_ji Γ A A') : judgement_scope.
Notation "'[Tm!' Γ |- a ; A !]" :=  (make_term_ji Γ a A) : judgement_scope.
Notation "'[TmEq!' Γ |- a ≡ a' ; A !]" := (make_term_equation_ji Γ A a a') : judgement_scope.

Open Scope judgement_scope.

