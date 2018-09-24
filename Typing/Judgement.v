Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.
Require Import Syntax.Metavariable.
Require Import Typing.Context.

Section JudgementDefinitions.
  Context {σ : shape_system}.
  Context (Σ : signature σ).

  (* The basic hypothetical judgment forms. *)
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

  Local Definition type_object_boundary := Family.empty syntactic_class.

  Inductive term_boundary_slot_index := the_term_type.

  Definition term_boundary_slot :=
    {| family_index := term_boundary_slot_index ;
       family_element :=
         (fun slot =>
            match slot with
            | the_term_type => class_type
            end)
    |}.

  (* The boundary slots of a term or type judgement. *)
  Local Definition object_boundary_slot (cl : syntactic_class) : family syntactic_class
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => type_object_boundary
       (* Boundary of a term judgement: the type of the term *)
       | class_term => term_boundary_slot
     end.

  Inductive equality_boundary_slot_index cl :=
  | the_equality_sort : family_index (object_boundary_slot cl) -> equality_boundary_slot_index cl
  | the_equality_lhs
  | the_equality_rhs.

  Local Definition equality_boundary_slot (cl : syntactic_class) :=
    {| family_index := equality_boundary_slot_index cl ;
       family_element :=
         (fun slot =>
            match slot with
            | the_equality_sort slot' => object_boundary_slot cl slot'
            | the_equality_lhs => cl
            | the_equality_rhs => cl
            end)
    |}.

  (* Syntactic classes of the slots in the boundary of a hypothetical judgement *)
  Local Definition boundary_slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* object judgement boundary is the boundary of the object *)
       | form_object cl => object_boundary_slot cl
       (* equality judgement boundary: a boundary of the corresponding object-judgement,
          together with two objects of the given class *)
       | form_equality cl  => equality_boundary_slot cl
     end.

  Inductive object_slot_index cl :=
  | the_boundary : object_boundary_slot cl -> object_slot_index cl
  | the_head : object_slot_index cl.

  Local Definition object_slot cl :=
    {| family_index := object_slot_index cl ;
       family_element :=
         (fun slot =>
            match slot with
            | the_boundary slot' => object_boundary_slot cl slot'
            | the_head => cl
            end)
    |}.

  (* Syntactic classes of the slots in a hypothetical judgement *)
  Local Definition slot (hjf : hypothetical_form)
    : family syntactic_class
  := match hjf with
       (* Equality case: boundary is everything *)
       | form_equality cl =>
           boundary_slot (form_equality cl)
       (* Object case: add the head slot *)
       | form_object cl =>
           object_slot cl
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

  (** NOTE: the redundant “unit” is slightly ugly.
      However, compared to having the whole “shape” of [judgement jf] depend
      on whether [jf] is a context form or hyp form, this keeps the context
      part uniformly accessible, which gives better computational behaviour. *)
  Record judgement (jf : form) : Type
  := { context_of_judgement : raw_context Σ
     ; hypothetical_part :
         match jf with
         | form_context => (Unit : Type)
         | form_hypothetical hjf => hypothetical_judgement hjf context_of_judgement
         end
     }.
     (* NOTE: the cast [Unit : Type] above is necessary, for subtle universe-
      polymorphism reasons.  (Specifically: otherwise, Coq specialises [Unit]
      to [Set], which then forces the type of the other branch to be [Set], and
      so imposes unwanted universe constraints on the signature, shape system,
      etc., which can cause conflicts downstream.) *)

  Definition make_context_judgement (Γ : raw_context Σ) : judgement form_context
  := Build_judgement form_context Γ tt.
 
  Definition shape_of_judgement {jf} (J : judgement jf) : shape_carrier σ
  := context_of_judgement _ J.

  (* NOTE [AB]: I know the name [judgement_total] is ugly, but I do not want to introduce "instance" all over the place.
      Will first check to see which types are most frequently mentioned in the rest of the code. *)
  (* NOTE: if [judgement_total] is renamed to [judgement] and [judgement] to [judgement_instance], then [Judgement.fmap] and [fmap_judgement_total] below should be renamed accordingly (among many other things). *)
  Record judgement_total : Type
  := { form_of_judgement_total : form 
     ; judgement_of_judgement_total :> judgement form_of_judgement_total
     }.

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
      cbn in j. exists (context_of_judgement _ j). intros i.
      destruct hjf as [ ob_hjf | eq_hjf ].
      + exact (hypothetical_part _ j (the_boundary _ i)).
      + exact (hypothetical_part _ j i).
  Defined.

End JudgementDefinitions.

Arguments hypothetical_boundary : simpl nomatch.
Arguments Build_judgement {_ _ _} _ _.
Arguments context_of_judgement {_ _ _} j : simpl nomatch.
Arguments hypothetical_part {_ _ _} j : simpl nomatch.
Arguments make_context_judgement {_ _} _.
Arguments Build_judgement_total {_ _} _ _.
Arguments form_of_judgement_total {_ _} j : simpl nomatch.
Arguments boundary_of_judgement {_ _ _} _ : simpl nomatch.
Arguments shape_of_judgement {_ _ _} _ : simpl nomatch.

(** A tactic that is often handy working with syntax, especially slots:
recursively destruct some object of an iterated inductive type.

Currently only supports specific inductive types hand-coded here. *)
(* TODO: can this be generalised to work for arbitrary inductive types? *)
Ltac recursive_destruct x :=
    cbn in x;
    try match type of x with
    | form =>
      let hf := fresh "hf" in
      destruct x as [ | hf ]; [idtac | recursive_destruct hf]
    | hypothetical_form =>
      let cl := fresh "cl" in
      destruct x as [ cl | cl ]; recursive_destruct cl
    | syntactic_class => destruct x as [ | ]
    | option _ =>
      let y := fresh "y" in
      destruct x as [ y | ]; [recursive_destruct y | idtac ]
    | Empty => destruct x
    | Unit => destruct x as []
    | sum _ _ =>
      let y := fresh "y" in
      destruct x as [ y | y ]; recursive_destruct y
    | sig _ =>
      let x1 := fresh "x1" in
      let x2 := fresh "x2" in
      destruct x as [ x1 x2 ]; recursive_destruct x1; recursive_destruct x2
    | term_boundary_slot_index => destruct x as []
    | object_slot_index _ =>
      let slot := fresh "slot" in
      destruct x as [ slot | ] ; [ recursive_destruct slot | idtac ]
    | equality_boundary_slot_index _ =>
      let slot := fresh "slot" in
      destruct x as [ slot | | ] ; [ recursive_destruct slot | idtac | idtac ]
    | _ => idtac
    end.

Section Equality_Lemmas.
(** If judgements were record types, rather than function types over their finite set of slots, they would have judgemental eta, which would be very convenient.

In lieu of that, we give explicit lemmas for judgement equality:
- one [eq_by_eta] analogous to eta-expansion and the eta rule,
- one [eq_by_expressions] analogous to general function extensionality. *)

  Context {σ : shape_system} {Σ : signature σ} `{Funext}.

  Local Definition eta_expand (j : judgement_total Σ)
    : judgement_total Σ.
  Proof.
    destruct j as [jf j].
    exists jf.
    exists (context_of_judgement j).
    destruct jf as [ | hf].
    - (* note: could use [constructor] here, but this keeps this case
         literally equal to [j]. *)
      exact (hypothetical_part j).
    - intros i.
      set (i_keep := i).
      recursive_destruct hf;
        recursive_destruct i;
        exact (hypothetical_part j i_keep).
  Defined.

  Local Definition eta (j : judgement_total Σ)
    : eta_expand j = j.
  Proof.
    apply (ap (Build_judgement_total _)).
    destruct j as [jf j].
    destruct jf as [ | hf]; try apply idpath.
    destruct j as [Γ hj].
    apply (ap (Build_judgement _)).
    apply path_forall; intros i.
    recursive_destruct hf;
      recursive_destruct i;
      apply idpath.
  Defined.

  (** To give something for a judgement (e.g. to derive it), one can always eta-expand the judgement first. *)
  Local Definition canonicalise
      (P : judgement_total Σ -> Type)
      (j : judgement_total Σ)
    : P (eta_expand j) -> P j.
  Proof.
    apply transport, eta.
  Defined.

  (* TODO: consider naming *)
  (** To check two judgements are equal, it’s enough to check their eta-expansions.
   Convenient for when modulo eta expansion, judgements are literally equal:
   [apply Judgement.eq_by_eta, idpath.] 

   For other cases, [eq_by_expressions] may be clearer. *)
  Local Definition eq_by_eta
      (j j' : judgement_total Σ)
    : eta_expand j = eta_expand j' -> j = j'.
  Proof.
    intros e.
    exact ((eta j)^ @ e @ eta j').
  Defined.

  (** When two judgements have the same form and are over the same shape, 
  then they are equal if all expressions involved (in both the context and
  the hypothetical part) are equal.

  Often useful in cases where the equality of expressions is for a uniform
  reason, such as functoriality/naturality lemmas. 

  For cases where the specific form of the judgement is involved in the 
  difference, [eq_by_eta] may be cleaner. *)
  Local Definition eq_by_expressions
      {hjf : hypothetical_form}
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {J J' : hypothetical_judgement Σ hjf γ}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_J : forall i, J i = J' i)
    : Build_judgement_total _ (@Build_judgement _ _
        (form_hypothetical hjf) (Build_raw_context γ Γ) J)
    = Build_judgement_total _ (@Build_judgement _ _
        (form_hypothetical hjf) (Build_raw_context γ Γ') J').
  Proof.
    apply ap.
    refine (@ap _ _
                (fun ΓJ : (_ * hypothetical_judgement _ _ γ)
                 => @Build_judgement _ _ (form_hypothetical _)
                       (Build_raw_context γ (fst ΓJ)) (snd ΓJ))
            (_,_) (_,_) _).
    apply path_prod; apply path_forall; auto.
  Defined.

  (** When two judgements have the same form and are over the same shape, 
  then they are equal if all expressions involved (in both the context and
  the hypothetical part) are equal.

  Often useful in cases where the equality of expressions is for a uniform
  reason, such as functoriality/naturality lemmas. 

  For cases where the specific form of the judgement is involved in the 
  difference, [eq_by_eta] may be cleaner. *)
  Local Definition boundary_eq_by_expressions
      {hjf : hypothetical_form}
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {B B' : hypothetical_boundary Σ hjf γ}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_B : forall i, B i = B' i) 
    : (Build_raw_context γ Γ ; B)
      = ((Build_raw_context γ Γ' ; B')
          : boundary _ (form_hypothetical hjf)).
  Proof.
    refine (@ap _ _
              (fun ΓB : (_ * hypothetical_boundary _ _ γ)
               => (Build_raw_context γ (fst ΓB) ; (snd ΓB)))
           (_,_) (_,_) _).
    apply path_prod; apply path_forall; auto.
  Defined.

End Equality_Lemmas.

Section JudgementFmap.

  Context {σ : shape_system}.

  Definition fmap_hypothetical_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {hjf} {γ}
    : hypothetical_boundary Σ hjf γ -> hypothetical_boundary Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Expression.fmap f), hjbi.
  Defined.

  Local Definition fmap_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} (B : boundary Σ jf)
    : boundary Σ' jf.
  Proof.
    destruct jf as [ | hjf].
    - exact B.
    - exists (Context.fmap f B.1).
      exact (fmap_hypothetical_boundary f B.2).
  Defined.

  Definition fmap_hypothetical_judgement
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
    intros J.
    exists (Context.fmap f (context_of_judgement J)).
    destruct jf as [ | hjf].
    - constructor.
    - cbn. exact (fmap_hypothetical_judgement f (hypothetical_part J)).
  Defined.

  (* NOTE: if [judgement_total] is renamed to [judgement] and [judgement] to [judgement_instance], then [Judgement.fmap] and [fmap_judgement_total] below should be renamed accordingly. *)
  Definition fmap_judgement_total {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : judgement_total Σ -> judgement_total Σ'.
  Proof.
    intros J.
    exists (form_of_judgement_total J).
    exact (fmap f J).
  Defined.

  Context `{Funext}.

  Definition fmap_hypothetical_boundary_idmap
      {Σ} {hjf} {γ} (B : hypothetical_boundary Σ hjf γ)
    : fmap_hypothetical_boundary (Signature.idmap Σ) B = B.
  Proof. 
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_boundary
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {hjf} {γ} (B : hypothetical_boundary Σ hjf γ)
    : fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B)
      = fmap_hypothetical_boundary (Signature.compose f' f) B.
  Proof. 
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_hypothetical_boundary_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {hjf} {γ} (B : hypothetical_boundary Σ hjf γ)
    : fmap_hypothetical_boundary (Signature.compose f' f) B
      = fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_boundary.
  Defined.

  Definition fmap_hypothetical_judgement_idmap
      {Σ} {hjf} {γ} (J : hypothetical_judgement Σ hjf γ)
    : fmap_hypothetical_judgement  (Signature.idmap Σ) J = J.
  Proof.
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_judgement
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {hjf} {γ} (B : hypothetical_judgement Σ hjf γ)
    : fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B)
      = fmap_hypothetical_judgement (Signature.compose f' f) B.
  Proof. 
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_hypothetical_judgement_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {hjf} {γ} (B : hypothetical_judgement Σ hjf γ)
    : fmap_hypothetical_judgement (Signature.compose f' f) B
      = fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_judgement.
  Defined.

  Local Definition fmap_idmap
      {Σ} {jf} (J : judgement Σ jf)
    : fmap (Signature.idmap Σ) J = J.
  Proof.
    destruct jf as [ | hjf].
    - (* cxt judgement *)
      destruct J as [ Γ []].
      unfold fmap. apply ap10, ap, (ap (Build_raw_context _)).
      apply path_forall; intros i.
      apply Expression.fmap_idmap.
    - (* hypothetical judgement *)
      destruct J. eapply concat.
      2: { apply ap, path_forall; intros i.
           apply Expression.fmap_idmap. }
      unfold fmap. simpl.
      refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
      apply path_forall; intros i.
      apply Expression.fmap_idmap.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {jf} (J : judgement Σ jf)
    : fmap (Signature.compose f' f) J = fmap f' (fmap f J).
  Proof.
    destruct jf as [ | hjf].
    - (* cxt judgement *)
      destruct J as [ Γ []].
      unfold fmap. apply ap10, ap, (ap (Build_raw_context _)).
      apply path_forall; intros i.
      apply Expression.fmap_compose.
    - (* hypothetical judgement *)
      destruct J.
      eapply concat.
      2: { refine (ap (Build_judgement _) _). apply path_forall; intros i.
           apply Expression.fmap_compose. }
      unfold fmap. simpl.
      refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
      apply path_forall; intros i.
      apply Expression.fmap_compose.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {jf} (J : judgement Σ jf)
    : fmap f' (fmap f J) = fmap (Signature.compose f' f) J.
  Proof.
    apply inverse, fmap_compose.
  Defined.

  Definition fmap_judgement_total_idmap {Σ} (J : judgement_total Σ)
    : fmap_judgement_total (Signature.idmap Σ) J = J.
  Proof.
    apply (ap (Build_judgement_total _)), fmap_idmap.
  Defined.

  Definition fmap_judgement_total_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement_total Σ)
    : fmap_judgement_total (Signature.compose f' f) J
      = fmap_judgement_total f' (fmap_judgement_total f J).
  Proof.
    apply (ap (Build_judgement_total _)), fmap_compose.
  Defined.

  Definition fmap_fmap_judgement_total
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement_total Σ)
    : fmap_judgement_total f' (fmap_judgement_total f J)
      = fmap_judgement_total (Signature.compose f' f) J.
  Proof.
    apply inverse, fmap_judgement_total_compose.
  Defined.

  Definition fmap_hypothetical_instance_from_boundary_and_head
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {hjf} {γ : σ} (B : hypothetical_boundary Σ hjf γ)
      (e : is_object hjf -> raw_expression Σ (class_of hjf) γ)
    : fmap_hypothetical_judgement f
        (hypothetical_instance_from_boundary_and_head _ B e)
      = hypothetical_instance_from_boundary_and_head _
          (fmap_hypothetical_boundary f B)
          (fun hjf_ob => Expression.fmap f (e hjf_ob)).
  Proof.
    destruct hjf as [ocl | ecl].
    - apply path_forall; intros [ ? | ]; apply idpath.
    - apply idpath.
  Defined.

End JudgementFmap.

Section JudgementNotations.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition make_context_judgement_total
        (Γ : raw_context Σ)
    : judgement_total Σ.
  Proof.
    exists form_context. apply make_context_judgement, Γ.
  Defined.

  Local Definition make_type_judgement_total
        (Γ : raw_context Σ) (A : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_object class_type)).
    exists Γ.
    intros [ [] | ]; exact A.
  Defined.

  Local Definition make_type_equality_judgement_total
             (Γ : raw_context Σ)
             (A A' : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equality class_type)).
    exists Γ.
    intros [ [] |  | ].
    exact A.
    exact A'.
  Defined.

  Local Definition make_term_judgement_total
             (Γ : raw_context Σ) (a : raw_term Σ Γ) (A : raw_type Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_object class_term)).
    exists Γ.
    intros [ [] | ].
    exact A.
    exact a.
  Defined.

  (* TODO: consistentise order with [make_term_judgement_total]. *)
  Local Definition make_term_equality_judgement_total
             (Γ : raw_context Σ) (A : raw_type Σ Γ) (a a': raw_term Σ Γ)
    : judgement_total Σ.
  Proof.
    exists (form_hypothetical (form_equality class_term)).
    exists Γ.
    intros [ [] | | ].
    exact A.
    exact a.
    exact a'.
  Defined.

End JudgementNotations.

Notation "'[!' |- Γ !]" := (make_context_judgement_total Γ) : judgement_scope.
Notation "'[!' Γ |- A !]" := (make_type_judgement_total Γ A) : judgement_scope.
Notation "'[!' Γ |- A ≡ A' !]" := (make_type_equality_judgement_total Γ A A') : judgement_scope.
Notation "'[!' Γ |- a ; A !]" :=  (make_term_judgement_total Γ a A) : judgement_scope.
Notation "'[!' Γ |- a ≡ a' ; A !]" := (make_term_equality_judgement_total Γ A a a') : judgement_scope.

Open Scope judgement_scope.

Section Presupposition.
(** TODO: the naming in this section seems a bit ugly. *)

(** Whenever an object appears in the boundary of an object judgement, then its
    boundary embeds into that boundary.

    NOTE. This is a special case of [boundary_slot_from_presupposition] below. It is
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
  Local Definition boundary_slot_from_presupposition
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
        destruct i as [ i' |  | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists (the_equality_sort _ (object_boundary_from_boundary_slots i' j)).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (the_equality_sort _ j). apply idpath.
        * (* i is LHS *)
          exists (the_equality_sort _ j). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.

  Local Definition slot_from_boundary
    {hjf : hypothetical_form}
    : Family.map (boundary_slot hjf) (slot hjf).
  Proof.
    destruct hjf as [ obj_cl | eq_cl ].
    - exists (the_boundary obj_cl).
      intros ; apply idpath.
    - apply Family.idmap.
  Defined.

  Local Definition slot_from_presupposition
    {hjf : hypothetical_form} (i : boundary_slot hjf)
    : Family.map
        (slot (form_object (boundary_slot _ i)))
        (slot hjf).
  Proof.
    eapply Family.compose.
    - apply slot_from_boundary.
    - apply boundary_slot_from_presupposition.
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
    - intros i. simple refine (Build_judgement_total _ _).
      + clear jb. destruct jf as [ | hjf].
        * destruct i as [].
        * destruct i as [ i | ].
          -- exact (form_hypothetical (form_object ((boundary_slot hjf) i))).
          -- exact form_context.
      + destruct jf as [ | hjf].
         * destruct i as [].
         * exists (pr1 jb).
           destruct i as [ i | ].
           -- intros j.
              refine (transport (fun cl => raw_expression _ cl _) _ _).
              ++ exact (Family.map_commutes (boundary_slot_from_presupposition i) j).
              ++ exact (pr2 jb (boundary_slot_from_presupposition i j)).
           -- constructor.
  Defined.

  (** The presuppositions of judgement [j]. *)
  Definition presupposition
      {Σ : signature σ} (j : judgement_total Σ)
    : family (judgement_total Σ)
  := presupposition_of_boundary (boundary_of_judgement j).

  (** Interactions between [fmap] along signature maps,
   and taking presuppositions. *)

  Local Definition fmap_presupposition_of_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} (B : boundary Σ jf)
      (p : presupposition_of_boundary B)
    : fmap_judgement_total f (presupposition_of_boundary B p)
    = presupposition_of_boundary (fmap_boundary f B) p.
  Proof.
    destruct jf as [ | hjf].
    - (* context *) destruct p. (* no presups *)
    - (* hyp *)
      recursive_destruct hjf; recursive_destruct p; try apply idpath;
        apply eq_by_expressions;
        intros j; recursive_destruct j; apply idpath.
  Defined.

  (* TODO: this should be an iso! *)
  Local Definition presupposition_fmap_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} (B : boundary Σ jf)
    : Family.map
        (presupposition_of_boundary (fmap_boundary f B))
        (Family.fmap (fmap_judgement_total f) (presupposition_of_boundary B)).
  Proof.
    exists idmap.
    intros i; apply fmap_presupposition_of_boundary.
  Defined.

  Local Definition fmap_presupposition `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement_total Σ)
      (p : presupposition J)
    : fmap_judgement_total f (presupposition J p)
    = presupposition (fmap_judgement_total f J) p.
  Proof.
    destruct J as [[ | hjf] J].
    - (* context *) destruct p. (* no presups *)
    - (* hyp *)
      recursive_destruct hjf; recursive_destruct p; try apply idpath;
        apply eq_by_expressions;
        intros j; recursive_destruct j; apply idpath.    
  Defined.

  (* TODO: this should be an iso!  And consistentise with [presupposition_fmap_boundary]. *)
  Local Definition fmap_presupposition_family `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement_total Σ)
    : Family.map
        (Family.fmap (fmap_judgement_total f) (presupposition J))
        (presupposition (fmap_judgement_total f J)).
  Proof.
    exists (fun p => p).
    intros p; apply inverse, fmap_presupposition.
  Defined.

End Presupposition.

Section Rename_Variables.
(** As discussed in [Syntax.Context], one can rename the variables of a judgement along an _isomorphism_ of shapes. *)

  Context {σ : shape_system} {Σ : signature σ}.

  (** Note: argument order follows general [rename] for expressions, not  [Context.rename]. *)
  Definition rename_hypothetical_boundary
      {γ γ' : σ} (f : γ -> γ')
      {hjf} (B : hypothetical_boundary Σ hjf γ)
    : hypothetical_boundary Σ hjf γ'.
  Proof.
    exact (fun j => rename f (B j)).
  Defined.

  (** Note: argument order follows [Context.rename], not general [rename] for expressions. *)
  (* TODO: consistentise with [rename_hypothetical_boundary]? *)
  Definition rename_hypothetical_judgement
      {γ} {hjf} (J : hypothetical_judgement Σ hjf γ)
      {γ' : shape_carrier σ} (f : γ' <~> γ)
    : hypothetical_judgement Σ hjf γ'.
  Proof.
    exact (fun j => rename (equiv_inverse f) (J j)).
  Defined.

  Local Definition rename
      (J : judgement_total Σ)
      {γ' : shape_carrier σ} (f : γ' <~> shape_of_judgement J)
    : judgement_total Σ.
  Proof.
    exists (form_of_judgement_total J).
    exists (Context.rename (context_of_judgement J) f).
    destruct J as [[ | ] J].
    - (* context judgement *)
      constructor.
    - (* hypothetical judgement *)
      exact (rename_hypothetical_judgement (hypothetical_part J) f).
  Defined.

  Context `{H_Funext : Funext}.

  Local Definition rename_rename
      (J : judgement_total Σ)
      {γ' : shape_carrier σ} (e : γ' <~> shape_of_judgement J)
      {γ'' : shape_carrier σ} (e' : γ'' <~> γ')
    : rename (rename J e) e'
      = rename J (equiv_compose e e').
  Proof.
    destruct J as [ [ | hjf ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)),
            (ap make_context_judgement),
            (ap (Build_raw_context _)).
      apply path_forall; cbn; intros i.
      apply inverse, rename_comp.
    - (* hypothetical judgement *)
      apply eq_by_expressions; cbn.
      + intros i. apply inverse, rename_comp.
      + intros i. unfold rename_hypothetical_judgement; cbn.
        apply inverse, rename_comp.
  Defined.

  Local Definition rename_idmap
      (J : judgement_total Σ)
    : rename J (equiv_idmap _)
      = J.
  Proof.
    destruct J as [ [ | hjf ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)).
      eapply concat.
      { eapply (ap make_context_judgement),
               (ap (Build_raw_context _)).
        apply path_forall; cbn; intros i.
        apply rename_idmap. }
      apply (ap (Build_judgement _)), contr_unit.
    - (* hypothetical judgement *)
      apply eq_by_expressions; cbn.
      + intros i. apply rename_idmap.
      + intros i. unfold rename_hypothetical_judgement; cbn.
        apply rename_idmap.
  Defined.

  Local Definition rename_inverse
      (J : judgement_total Σ)
      {γ' : shape_carrier σ} (e : shape_of_judgement J <~> γ')
    : rename (rename J (e^-1)) e = J.
  Proof.
    eapply concat. { apply rename_rename. }
    eapply concat. 2: { apply rename_idmap. }
    apply ap, ecompose_Ve.
  Defined.

  Lemma rename_hypothetical_boundary_idmap
      {γ : σ} {hjf} (B : hypothetical_boundary _ hjf γ)
    : rename_hypothetical_boundary idmap B = B.
  Proof.
    apply path_forall; intros i.
    apply Expression.rename_idmap.
  Defined.

End Rename_Variables.

Section Instantiation.
(** Interaction of judgements with metavariable instantiations *)

  Context {σ : shape_system} `{Funext}.

  Local Definition instantiate
      {a : arity σ} {Σ : signature σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (j : judgement_total (Metavariable.extend Σ a))
    : judgement_total Σ.
  Proof.
    exists (form_of_judgement_total j).
    exists (Context.instantiate _ I (context_of_judgement j)).
    destruct j as [jf J]; destruct jf; simpl in *.
    - constructor.
    - simpl. intro i.
      apply (instantiate_expression I (hypothetical_part J i)).
  Defined.

  Local Lemma fmap_instantiate
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (J : judgement_total (Metavariable.extend _ _))
    : fmap_judgement_total f (instantiate Γ I J)
    = instantiate
        (Context.fmap f Γ) 
        (instantiation_fmap f I)
        (fmap_judgement_total (Metavariable.fmap1 f a) J).
  Proof.
    destruct J as [[ | ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)), (ap (fun Γ => Build_judgement Γ _)).
      cbn. apply Context.fmap_instantiate.
    - (* hypothetical judgement *)
      apply eq_by_expressions. 
      + (* context part *)
        refine (coproduct_rect shape_is_sum _ _ _); intros i;
          unfold Context.instantiate.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
          apply fmap_rename.
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
          apply fmap_instantiate_expression.
      + intros i; apply fmap_instantiate_expression.
  Defined.

  Context {Σ : signature σ}.

  Local Lemma unit_instantiate
      {a} (J : judgement_total (Metavariable.extend Σ a))
    : instantiate [::] (unit_instantiation a)
        (fmap_judgement_total (Metavariable.fmap1 include_symbol _) J)
      = rename J (shape_sum_empty_inr _)^-1.
  Proof.
    destruct J as [ [ | hjf ] J ].
    - (* context judgement *)
      destruct J as [J []].
      simpl. unfold instantiate, rename. 
      apply ap, ap10, ap.
      apply Context.unit_instantiate.
    - (* hypothetical judgement *)
      apply eq_by_expressions.
      + refine (coproduct_rect shape_is_sum _ _ _).
        * apply (empty_rect _ shape_is_empty).
        * intros x.
          eapply concat. { refine (coproduct_comp_inj2 _). }
          eapply concat. { apply unit_instantiate_expression. }
          apply ap, ap, inverse. cbn.
          refine (coproduct_comp_inj2 _).
      + intros i; apply unit_instantiate_expression.
  Defined.

  Local Lemma instantiate_instantiate
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement_total (Metavariable.extend Σ b))
    : instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) j
    = rename
        (instantiate Γ I
          (instantiate Δ J
            (fmap_judgement_total (Metavariable.fmap1 include_symbol _) j)))
         (shape_assoc _ _ _)^-1.
  Proof.
    destruct j as [[ | jf ] j].
    - apply (ap (Build_judgement_total _)),
            (ap (fun Γ => Build_judgement Γ _)),
            (ap (fun A => Build_raw_context _ A)).
      apply path_forall.
      intros i; apply @Context.instantiate_instantiate_pointwise; auto.
    - apply eq_by_expressions.
      + apply @Context.instantiate_instantiate_pointwise; auto.
      + intros i. refine (instantiate_instantiate_expression _ _ _).
  Defined.

  (** The instantiation under [I] of any presupposition of a judgement [j]
      is equal to the corresponding presupposition of the instantiation of [j]
      itself under [I]. *)
  Definition instantiate_presupposition
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement_total _)
      (i : presupposition (instantiate _ I j))
    : instantiate _ I (presupposition j i)
      = presupposition (instantiate _ I j) i.
  Proof.
    apply (ap (Build_judgement_total _)). (* judgement form of presup unchanged *)
    destruct j as [[ | hjf] j].
    - destruct i. (* [j] is context judgement: no presuppositions. *)
    - (* [j] is a hypothetical judgement *)
      apply (ap (Build_judgement _)). (* context of presup unchanged *)
      destruct i as [ i | ].
      + (* hypothetical presupposition *)
        apply path_forall; intros k.
        recursive_destruct hjf;
        recursive_destruct i;
        recursive_destruct k;
        try apply idpath.
      + (* raw context *)
        apply idpath.
Defined.

End Instantiation.

Arguments instantiate : simpl nomatch.
