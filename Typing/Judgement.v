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

(** We first set up the combinatorics describing the “shapes” of the judgement forms — specifying how many expressions they will involve, and of what classes — before bringing in the actual syntax, and defining judgements themselves. *)
Section JudgementCombinatorics.

  (** We take as primitive only the _hypothetical_ judgment forms:
  [! Γ |- A !],
  [! Γ |- A ≡ A' !],
  [! Γ |- a ; A !],
  [! Γ |- a ≡ a' ; A !],
  and rules, derivations will be given purely in terms of these.
 
  Other judgement forms — e.g. well-formed contexts, context morphisms — are taken as _auxiliary_ judgements, defined afterwards from thes primitive ones. *)
  Local Inductive form : Type :=
  | form_object (cl : syntactic_class)
      (* a thing is a term, a thing is a type *)
  | form_equality (cl : syntactic_class).
      (* terms are equal, types are equal *)

  Local Definition is_object : form -> Type
    := fun jf => match jf with
                     | form_object _ => Unit
                     | form_equality _ => Empty
                  end.

  Local Definition class_of : form -> syntactic_class
    := fun jf => match jf with
                     | form_object cl => cl
                     | form_equality cl => cl
                  end.

  (** A _judgement_ will have of a piece of syntax for each _slot_ of the given judgement form: so e.g. the term judgement [! Γ |- a ; A !] has one type slot and one term slot.  To be able to describe constructions on judgements uniformly later, we define the slots in a structured way, dividing them into the _head slot_ and _boundary slots_. *)

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

  (** The boundary slots of a term or type judgement. *)
  Local Definition object_boundary_slot (cl : syntactic_class)
    : family syntactic_class
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | class_type => type_object_boundary
       (* Boundary of a term judgement: the type of the term *)
       | class_term => term_boundary_slot
     end.

  Inductive equality_boundary_slot_index cl
  :=
    | the_equality_sort : family_index (object_boundary_slot cl)
                          -> equality_boundary_slot_index cl
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
  Local Definition boundary_slot (hjf : form)
    : family syntactic_class
  := match hjf with
       (* object judgement boundary is the boundary of the object *)
       | form_object cl => object_boundary_slot cl
       (* equality judgement boundary: a boundary of the corresponding
          object-judgement, together with two objects of the given class *)
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
  Local Definition slot (hjf : form)
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

End JudgementCombinatorics.

Section Judgements.

  Context {σ : shape_system}.
  Context (Σ : signature σ).

  Local Record hypothetical_boundary γ : Type
    := { form_of_boundary : form
       ; boundary_expression :>
           forall i : boundary_slot form_of_boundary,
             raw_expression Σ (family_element _ i) γ }.

  Arguments form_of_boundary {_} _.
  Arguments boundary_expression {_} _.
 
  Record hypothetical_judgement γ : Type
    := { form_of_judgement : form
       ; judgement_expression :>
           forall i : slot form_of_judgement,
             raw_expression Σ (family_element _ i) γ }.
  Arguments form_of_judgement {_} _.
  Arguments judgement_expression {_} _.

  Local Record boundary : Type
  := { context_of_boundary : raw_context Σ
     ; hypothetical_part_of_boundary
         :> hypothetical_boundary context_of_boundary }.

  Record judgement : Type
  := { context_of_judgement : raw_context Σ
     ; hypothetical_part :> hypothetical_judgement context_of_judgement }.

  Definition shape_of_judgement (J : judgement) : shape_carrier σ
  := context_of_judgement J.

  Local Definition hypothetical_judgement_from_boundary_and_head
      {γ}
      (bdry : hypothetical_boundary γ)
      (head : is_object (form_of_boundary bdry)
              -> raw_expression Σ (class_of (form_of_boundary bdry)) γ)
    : hypothetical_judgement γ.
  Proof.
    destruct bdry as [hjf b]; exists hjf.
    destruct hjf as [ ocl | ecl ].
    - (* case: object judgement *)
      intros [ i | ].
      + apply b.
      + apply head. constructor.
    - (* case: equality judgement *)
      apply b.
  Defined.

  Definition hypothetical_boundary_of_judgement
      {γ} (J : hypothetical_judgement γ)
    : hypothetical_boundary γ.
  Proof.
    exists (form_of_judgement J).
    intros i. destruct J as [jf j].
      destruct jf as [ ob_jf | eq_jf ].
      + exact (j (the_boundary _ i)).
      + exact (j i).
  Defined.
  
  Definition boundary_of_judgement
    : judgement -> boundary.
  Proof.
    intros J. exists (context_of_judgement J).
    apply hypothetical_boundary_of_judgement, J.
  Defined.

End Judgements.

Arguments Build_hypothetical_boundary {_ _ _} _ _.
Arguments form_of_boundary {_ _ _} _. 
Arguments Build_hypothetical_judgement {_ _ _} _ _.
Arguments form_of_judgement {_ _ _} _. 
Arguments Build_boundary {_ _} _ _. 
Arguments context_of_boundary {_ _} _. 
Arguments Build_judgement {_ _} _ _. 
Arguments context_of_judgement {_ _} _. 
Arguments shape_of_judgement {_ _} _. 
Arguments hypothetical_part {_ _} _. 
Arguments boundary_of_judgement {_ _} _.
(* TODO: reinstate as needed
Arguments hypothetical_boundary : simpl nomatch.
Arguments Build_judgement {_ _ _} _ _.
Arguments context_of_judgement {_ _ _} j : simpl nomatch.
Arguments hypothetical_part {_ _ _} j : simpl nomatch.
Arguments make_context_judgement {_ _} _.
Arguments Build_judgement_total {_ _} _ _.
Arguments form_of_judgement_total {_ _} j : simpl nomatch.
Arguments boundary_of_judgement {_ _ _} _ : simpl nomatch.
Arguments shape_of_judgement {_ _ _} _ : simpl nomatch.
*)

Section JudgementFmap.

  Context {σ : shape_system}.

  Definition fmap_hypothetical_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {γ}
    : hypothetical_boundary Σ γ -> hypothetical_boundary Σ' γ.
  Proof.
    intros B. exists (form_of_boundary B).
    intros i. apply (Expression.fmap f), B.
  Defined.

  Local Definition fmap_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ)
    : boundary Σ'.
  Proof.
    exists (Context.fmap f (context_of_boundary B)).
    exact (fmap_hypothetical_boundary f B).
  Defined.

  Definition fmap_hypothetical_judgement
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ') {γ}
    : hypothetical_judgement Σ γ -> hypothetical_judgement Σ' γ.
  Proof.
    intros J. exists (form_of_judgement J).
    intros i. apply (Expression.fmap f), J.
  Defined.

  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : judgement Σ -> judgement Σ'.
  Proof.
    intros J.
    exists (Context.fmap f (context_of_judgement J)).
    exact (fmap_hypothetical_judgement f (hypothetical_part J)).
  Defined.

  Context `{Funext}.

  Definition fmap_hypothetical_boundary_idmap
      {Σ} {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary (Signature.idmap Σ) B = B.
  Proof. 
    apply (ap (Build_hypothetical_boundary _)).
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_boundary
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B)
      = fmap_hypothetical_boundary (Signature.compose f' f) B.
  Proof. 
    apply (ap (Build_hypothetical_boundary _)).
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_hypothetical_boundary_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_boundary Σ γ)
    : fmap_hypothetical_boundary (Signature.compose f' f) B
      = fmap_hypothetical_boundary f' (fmap_hypothetical_boundary f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_boundary.
  Defined.

  Definition fmap_hypothetical_judgement_idmap
      {Σ} {γ} (J : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement  (Signature.idmap Σ) J = J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply Expression.fmap_idmap.
  Defined.

  Definition fmap_fmap_hypothetical_judgement
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B)
      = fmap_hypothetical_judgement (Signature.compose f' f) B.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i.
    apply Expression.fmap_fmap.
  Defined.

  Definition fmap_hypothetical_judgement_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {γ} (B : hypothetical_judgement Σ γ)
    : fmap_hypothetical_judgement (Signature.compose f' f) B
      = fmap_hypothetical_judgement f' (fmap_hypothetical_judgement f B).
  Proof.
    apply inverse, fmap_fmap_hypothetical_judgement.
  Defined.

  Local Definition fmap_idmap
      {Σ} (J : judgement Σ)
    : fmap (Signature.idmap Σ) J = J.
  Proof.
    eapply concat.
      2: { eapply (ap (Build_judgement _)), fmap_hypothetical_judgement_idmap. }
      refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
      apply path_forall; intros i.
      apply Expression.fmap_idmap.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : fmap (Signature.compose f' f) J = fmap f' (fmap f J).
  Proof.
    eapply concat.
    2: { eapply (ap (Build_judgement _)), fmap_hypothetical_judgement_compose. }
    unfold fmap. simpl.
      refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _).
      apply path_forall; intros i.
      apply Expression.fmap_compose.
    (* TODO: easier if we generalise [eq_by_expressions]? *)
  Defined.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : fmap f' (fmap f J) = fmap (Signature.compose f' f) J.
  Proof.
    apply inverse, fmap_compose.
  Defined.

  Definition fmap_hypothetical_judgement_from_boundary_and_head
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {γ : σ} (B : hypothetical_boundary Σ γ)
      (e : is_object _ -> raw_expression Σ _ γ)
    : fmap_hypothetical_judgement f
        (hypothetical_judgement_from_boundary_and_head _ B e)
      = hypothetical_judgement_from_boundary_and_head _
          (fmap_hypothetical_boundary f B)
          (fun hjf_ob => Expression.fmap f (e hjf_ob)).
  Proof.
    destruct B as [jf B]. apply (ap (Build_hypothetical_judgement _)).
    destruct jf as [ocl | ecl].
    - apply path_forall; intros [ ? | ]; apply idpath.
    - apply idpath.
  Defined.

End JudgementFmap.

(** A tactic that is often handy working with syntax, especially slots:
recursively destruct some object of an iterated inductive type.

Currently only supports specific inductive types hand-coded here. *)
(* TODO: can this be generalised to work for arbitrary inductive types? *)
Ltac recursive_destruct x :=
    cbn in x;
    try match type of x with
    | form =>
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

  Local Definition eta_expand (j : judgement Σ)
    : judgement Σ.
  Proof.
    exists (context_of_judgement j).
    exists (form_of_judgement j).
    destruct j as [Γ [jf j]]. 
    intros i; set (i_keep := i).
    recursive_destruct jf;
        recursive_destruct i;
        exact (j i_keep).
  Defined.

  Local Definition eta (j : judgement Σ)
    : eta_expand j = j.
  Proof.
    apply (ap (Build_judgement _)), (ap (Build_hypothetical_judgement _)).
    destruct j as [Γ [jf j]]. 
    apply path_forall; intros i.
    recursive_destruct jf;
      recursive_destruct i;
      apply idpath.
  Defined.

  (** To give something for a judgement (e.g. to derive it), one can always eta-expand the judgement first. *)
  Local Definition canonicalise
      (P : judgement Σ -> Type)
      (j : judgement Σ)
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
      (j j' : judgement Σ)
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
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {hjf : form} {J J' : _}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_J : forall i, J i = J' i)
    : Build_judgement (Build_raw_context γ Γ)
                      (Build_hypothetical_judgement hjf J)
    = Build_judgement (Build_raw_context γ Γ')
                      (Build_hypothetical_judgement hjf J').
  Proof.
    eapply concat.
    { eapply (ap (Build_judgement _)),
      (ap (Build_hypothetical_judgement _)), path_forall; exact e_J. }
    apply (ap (fun Γ => Build_judgement (Build_raw_context γ Γ) _)).
    apply path_forall; auto.
  Defined.

  (** When two judgements have the same form and are over the same shape, 
  then they are equal if all expressions involved (in both the context and
  the hypothetical part) are equal.

  Often useful in cases where the equality of expressions is for a uniform
  reason, such as functoriality/naturality lemmas. 

  For cases where the specific form of the judgement is involved in the 
  difference, [eq_by_eta] may be cleaner. *)
  Local Definition boundary_eq_by_expressions
      {γ : σ} {Γ Γ' : γ -> raw_type Σ γ}
      {hjf : form} {B B' : _}
      (e_Γ : forall i, Γ i = Γ' i)
      (e_B : forall i, B i = B' i)
    : Build_boundary (Build_raw_context γ Γ)
                      (Build_hypothetical_boundary hjf B)
    = Build_boundary (Build_raw_context γ Γ')
                      (Build_hypothetical_boundary hjf B').
  Proof.
    eapply concat.
    { eapply (ap (Build_boundary _)),
      (ap (Build_hypothetical_boundary _)), path_forall; exact e_B. }
    apply (ap (fun Γ => Build_boundary (Build_raw_context γ Γ) _)).
    apply path_forall; auto.
  Defined.

End Equality_Lemmas.

Section JudgementNotations.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition make_type_judgement
        (Γ : raw_context Σ) (A : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_object class_type).
    intros [ [] | ]; exact A.
  Defined.

  Local Definition make_type_equality_judgement
             (Γ : raw_context Σ)
             (A A' : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_equality class_type).
    intros [ [] |  | ].
    - exact A.
    - exact A'.
  Defined.

  Local Definition make_term_judgement
             (Γ : raw_context Σ) (a : raw_term Σ Γ) (A : raw_type Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_object class_term).
    intros [ [] | ].
    - exact A.
    - exact a.
  Defined.

  (* TODO: consistentise order with [make_term_judgement]. *)
  Local Definition make_term_equality_judgement
             (Γ : raw_context Σ) (A : raw_type Σ Γ) (a a': raw_term Σ Γ)
    : judgement Σ.
  Proof.
    exists Γ, (form_equality class_term).
    intros [ [] | | ].
    - exact A.
    - exact a.
    - exact a'.
  Defined.

End JudgementNotations.

Notation "'[!' Γ |- A !]" := (make_type_judgement Γ A) : judgement_scope.
Notation "'[!' Γ |- A ≡ A' !]"
  := (make_type_equality_judgement Γ A A') : judgement_scope.
Notation "'[!' Γ |- a ; A !]"
  :=  (make_term_judgement Γ a A) : judgement_scope.
Notation "'[!' Γ |- a ≡ a' ; A !]"
  := (make_term_equality_judgement Γ A a a') : judgement_scope.

Open Scope judgement_scope.


(** A key notion is the _presuppositions_ of a judgement.

For instance, the presuppositions of [ Γ |- a : A ] are the judgements [ |- Γ ] and [ Γ |- A type ].

As with judgements themselves, we first describe set up the combinatorics indexing the constructions involved. *)

Section PresuppositionsCombinatorics.
(** Whenever an object appears in the boundary of an object judgement, then its
    boundary embeds into that boundary.

    NOTE. This is a special case of [boundary_slot_from_presupposition] below.
    It is abstracted out because it’s used twice: directly for object
    judgements, and as part of the case for equality judgements.

    In fact it’s almost trivial, so could easily be inlined; but conceptually
    it is the same thing both times, and in type theory with more judgements,
    it would be less trivial, so we keep it factored out. *)

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
    {hjf : form} (i : boundary_slot hjf)
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
          exists
            (the_equality_sort _ (object_boundary_from_boundary_slots i' j)).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (the_equality_sort _ j). apply idpath.
        * (* i is LHS *)
          exists (the_equality_sort _ j). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.

  Local Definition slot_from_boundary
    {hjf : form}
    : Family.map (boundary_slot hjf) (slot hjf).
  Proof.
    destruct hjf as [ obj_cl | eq_cl ].
    - exists (the_boundary obj_cl).
      intros ; apply idpath.
    - apply Family.idmap.
  Defined.

  Local Definition slot_from_presupposition
    {hjf : form} (i : boundary_slot hjf)
    : Family.map
        (slot (form_object (boundary_slot _ i)))
        (slot hjf).
  Proof.
    eapply Family.compose.
    - apply slot_from_boundary.
    - apply boundary_slot_from_presupposition.
  Defined.

End PresuppositionsCombinatorics.

Section Presuppositions.
(** TODO: the naming in this section seems a bit ugly. *)

  Context {σ : shape_system}.

  (** The presuppositions of a judgment boundary [jb] *)
  Definition presupposition_of_boundary
      {Σ : signature σ} (B : boundary Σ)
    : family (judgement Σ).
  Proof.
  (* Note: destructing [jf] once early makes this definition look cleaner.

   However, destructing [jf] as late as possible, and clearing [jb] when
   possible, gives stronger computational behaviour:
   it keeps the index set and judgement forms independent of [Σ], [jb]. *)
    simple refine (Build_family _ _ _).
    - exact (boundary_slot (form_of_boundary B)).
    - intros i. exists (context_of_boundary B).
      exists (form_object (boundary_slot _ i)).
      intros j.
      refine (transport (fun cl => raw_expression _ cl _) _ _).
      + exact (Family.map_commutes (boundary_slot_from_presupposition i) j).
      + exact (B (boundary_slot_from_presupposition i j)).
  Defined.

  (** The presuppositions of judgement [j]. *)
  Definition presupposition
      {Σ : signature σ} (j : judgement Σ)
    : family (judgement Σ)
  := presupposition_of_boundary (boundary_of_judgement j).

  (** Interactions between functoriality under signature maps,
   and taking presuppositions. *)

  Local Definition fmap_presupposition_of_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ) (p : presupposition_of_boundary B)
    : fmap f (presupposition_of_boundary B p)
    = presupposition_of_boundary (fmap_boundary f B) p.
  Proof.
    destruct B as [Γ [hjf B]].
    recursive_destruct hjf; recursive_destruct p; try apply idpath;
      refine (eq_by_expressions _ _);
      intros j; recursive_destruct j; apply idpath.
  Defined.

  (* TODO: this should be an iso! *)
  Local Definition presupposition_fmap_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ)
    : Family.map
        (presupposition_of_boundary (fmap_boundary f B))
        (Family.fmap (fmap f) (presupposition_of_boundary B)).
  Proof.
    exists idmap.
    intros i; apply fmap_presupposition_of_boundary.
  Defined.

  Local Definition fmap_presupposition `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
      (p : presupposition J)
    : fmap f (presupposition J p)
    = presupposition (fmap f J) p.
  Proof.
    destruct J as [Γ [hjf J]].
      recursive_destruct hjf; recursive_destruct p; try apply idpath;
        refine (eq_by_expressions _ _);
        intros j; recursive_destruct j; apply idpath.    
  Defined.

  (* TODO: this should be an iso!  And consistentise with [presupposition_fmap_boundary]. *)
  Local Definition fmap_presupposition_family `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : Family.map
        (Family.fmap (fmap f) (presupposition J))
        (presupposition (fmap f J)).
  Proof.
    exists (fun p => p).
    intros p; apply inverse, fmap_presupposition.
  Defined.

End Presuppositions.

Section Rename_Variables.
(** One can rename the variables of a judgement along an _isomorphism_ of shapes.  (Cf. discussion at [Context.rename].) *)
(* TODO: redo all this now that context judgement expunged. *)

  Context {σ : shape_system} {Σ : signature σ}.

  (** Note: argument order follows general [rename] for expressions, not  [Context.rename]. *)
  Definition rename_hypothetical_boundary
      {γ γ' : σ} (f : γ -> γ')
      (B : hypothetical_boundary Σ γ)
    : hypothetical_boundary Σ γ'.
  Proof.
    exists (form_of_boundary B).
    exact (fun j => rename f (B j)).
  Defined.

  (** Note: argument order follows [Context.rename], not general [rename] for expressions. *)
  (* TODO: consistentise with [rename_hypothetical_boundary]! *)
  Definition rename_hypothetical_judgement
      {γ} (J : hypothetical_judgement Σ γ)
      {γ' : shape_carrier σ} (f : γ' <~> γ)
    : hypothetical_judgement Σ γ'.
  Proof.
    exists (form_of_judgement J).
    exact (fun j => rename (equiv_inverse f) (J j)).
  Defined.

  Local Definition rename
      (J : judgement Σ)
      {γ' : shape_carrier σ} (f : γ' <~> shape_of_judgement J)
    : judgement Σ.
  Proof.
    exists (Context.rename (context_of_judgement J) f).
    exists (form_of_judgement J).
    exact (rename_hypothetical_judgement (hypothetical_part J) f).
  Defined.

  Context `{H_Funext : Funext}.

  (* TODO: reorder the following lemmas, for consistency with usual *)
  Local Definition rename_rename
      (J : judgement Σ)
      {γ' : shape_carrier σ} (e : γ' <~> shape_of_judgement J)
      {γ'' : shape_carrier σ} (e' : γ'' <~> γ')
    : rename (rename J e) e'
      = rename J (equiv_compose e e').
  Proof.
    refine (eq_by_expressions _ _); cbn.
    - intros i. apply inverse, rename_comp.
    - intros i. unfold rename_hypothetical_judgement; cbn.
        apply inverse, rename_comp.
  Defined.

  Local Definition rename_idmap
      (J : judgement Σ)
    : rename J (equiv_idmap _)
      = J.
  Proof.
    refine (eq_by_expressions _ _); cbn.
    - intros i. apply rename_idmap.
    - intros i. unfold rename_hypothetical_judgement; cbn.
      apply rename_idmap.
  Defined.

  Local Definition rename_inverse
      (J : judgement Σ)
      {γ' : shape_carrier σ} (e : shape_of_judgement J <~> γ')
    : rename (rename J (e^-1)) e = J.
  Proof.
    eapply concat. { apply rename_rename. }
    eapply concat. 2: { apply rename_idmap. }
    apply ap, ecompose_Ve.
  Defined.

  Lemma rename_hypothetical_boundary_idmap
      {γ : σ} (B : hypothetical_boundary _ γ)
    : rename_hypothetical_boundary idmap B = B.
  Proof.
    apply (ap (Build_hypothetical_boundary _)).
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
      (j : judgement (Metavariable.extend Σ a))
    : judgement Σ.
  Proof.
    exists (Context.instantiate _ I (context_of_judgement j)).
    exists (form_of_judgement j).
    intro i.
    apply (instantiate_expression I (hypothetical_part j i)).
  Defined.

  Local Lemma fmap_instantiate
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (J : judgement (Metavariable.extend _ _))
    : fmap f (instantiate Γ I J)
    = instantiate
        (Context.fmap f Γ) 
        (instantiation_fmap f I)
        (fmap (Metavariable.fmap1 f a) J).
  Proof.
    refine (eq_by_expressions _ _). 
    - (* context part *)
      refine (coproduct_rect shape_is_sum _ _ _); intros i;
        unfold Context.instantiate.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
        apply fmap_rename.
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
        apply fmap_instantiate_expression.
    - intros i; apply fmap_instantiate_expression.
  Defined.

  Context {Σ : signature σ}.

  Local Lemma unit_instantiate
      {a} (J : judgement (Metavariable.extend Σ a))
    : instantiate [::] (unit_instantiation a)
        (fmap (Metavariable.fmap1 include_symbol _) J)
      = rename J (shape_sum_empty_inr _)^-1.
  Proof.
    refine (eq_by_expressions _ _). 
    - refine (coproduct_rect shape_is_sum _ _ _).
      + apply (empty_rect _ shape_is_empty).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply unit_instantiate_expression. }
        apply ap, ap, inverse. cbn.
        refine (coproduct_comp_inj2 _).
    - intros i; apply unit_instantiate_expression.
  Defined.

  Local Lemma instantiate_instantiate
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement (Metavariable.extend Σ b))
    : instantiate
        (Context.instantiate _ I Δ)
        (instantiate_instantiation I J) j
    = rename
        (instantiate Γ I
          (instantiate Δ J
            (fmap (Metavariable.fmap1 include_symbol _) j)))
         (shape_assoc _ _ _)^-1.
  Proof.
    refine (eq_by_expressions _ _).
      + apply @Context.instantiate_instantiate_pointwise; auto.
      + intros i. refine (instantiate_instantiate_expression _ _ _).
  Defined.

  (** The instantiation under [I] of any presupposition of a judgement [j]
      is equal to the corresponding presupposition of the instantiation of [j]
      itself under [I]. *)
  Definition instantiate_presupposition
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement _)
      (i : presupposition (instantiate _ I j))
    : instantiate _ I (presupposition j i)
      = presupposition (instantiate _ I j) i.
  Proof.
    apply (ap (Build_judgement _)). (* context of presup unchanged *)
    apply (ap (Build_hypothetical_judgement _)). (* form of presup unchanged *)
    destruct j as [Δ [hjf J]].
    (* hypothetical presupposition *)
    apply path_forall; intros k.
    recursive_destruct hjf;
      recursive_destruct i;
      recursive_destruct k;
      apply idpath.
Defined.

End Instantiation.

Arguments instantiate : simpl nomatch.
