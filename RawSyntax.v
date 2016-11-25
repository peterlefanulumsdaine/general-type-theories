
Require Import Auxiliary.

(* Background: abstracting proto-contexts *)

Section Shape_Systems.

(* TODO: possibly rename as “context shapes”, “shape systems”, …?  *)
Record Shape_System :=
  { Shape :> Type
  ; positions : Shape -> Type (* maybe should be to sets?? *)
  ; shape_empty : Shape
  ; shape_is_empty : is_empty (positions shape_empty)
  ; shape_coprod : Shape -> Shape -> Shape
  ; shape_is_coprod
     : forall γ δ : Shape,
       is_coprod (positions (shape_coprod γ δ)) (positions γ) (positions δ)
  ; shape_extend : Shape -> Shape
  ; shape_is_plusone         (* TODO: change to is_extend (Andrej?) *)
     : forall γ : Shape,
       is_plusone (positions (shape_extend γ)) (positions γ)
  }.

Global Arguments shape_coprod {_} _ _.
Global Arguments shape_is_coprod {_} [_ _].
Global Arguments shape_is_empty {_}.

Coercion positions : Shape >-> Sortclass.

End Shape_Systems.

Parameter Proto_Cxt : Shape_System.
(* TODO: improve naming *)

Section Signatures.

  Inductive Syn_Class : Type := Ty | Tm.

  Definition Arity : Type
    := Family (Syn_Class * Proto_Cxt).

  (* Entries in the family represent arguments of a constructor; the [Proto_Cxt] component represents the variables bound in each argument.

  For instance, the [Π-intro] rule (i.e. fully annotated λ-abstraction) would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,1)] ]; application would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,0), (Tm,0)]].

  The use of [Family] instead of just [list] serves two purposes.  Firstly, it abstracts the aspects of the [list] version that we really need, and so makes the code significantly cleaner/more robust.  Secondly, it allows this definition to be re-used for non-finitary syntax, although we do not intend to explore that for now. *)

  (* Access functions for arity *)
  Definition arg_class {a : Arity} (i : a) : Syn_Class := fst (a i).
  Definition arg_pcxt {a : Arity} (i : a) : Proto_Cxt := snd (a i).

  Definition Signature : Type
    := Family (Syn_Class * Arity).

  Definition class {Σ : Signature} (S : Σ) : Syn_Class
  := fst (Σ S).

  Definition arity {Σ : Signature} (S : Σ) : Arity
  := snd (Σ S).

End Signatures.

Section Raw_Syntax.

  Context {Σ : Signature}.

  (* A raw syntactic expression of a syntactic class, relative to a context *)
  Inductive Raw_Syntax
    : Syn_Class -> Proto_Cxt -> Type
  :=
  (* a variable in a context is a term in that context *)
    | var_raw (γ : Proto_Cxt) (i : γ)
        : Raw_Syntax Tm γ
    (* relative to a context [γ], given a symbol [S], if for each of its
       arguments we have a raw syntactic expression relative to [γ] extended by
       the argument's arity, [S args] is a raw syntactic expression over [γ] *)
    | symb_raw (γ : Proto_Cxt) (S : Σ)
               (args : forall (i : arity S),
                   Raw_Syntax (arg_class i)
                              (shape_coprod γ (arg_pcxt i)))
      : Raw_Syntax (class S) γ.

  Global Arguments var_raw [_] _.
  Global Arguments symb_raw [_] _ _.

  (* A raw context is a proto-ctx ("collection of identifiers") and a raw syntactic type expression
     for each identifier in the proto-ctx. *)
  Record Raw_Context
  := { Proto_Cxt_of_Raw_Context :> Proto_Cxt
     ; var_type_of_Raw_Context
         :> forall i : Proto_Cxt_of_Raw_Context,
            Raw_Syntax Ty Proto_Cxt_of_Raw_Context
     }.

  Definition Raw_Context_Map (γ δ : Proto_Cxt)
    := δ -> Raw_Syntax Tm γ.

End Raw_Syntax.

Global Arguments Raw_Syntax _ _ _ : clear implicits.
Global Arguments Raw_Context _ : clear implicits.
Global Arguments Raw_Context_Map _ _ _ : clear implicits.

Section Raw_Subst.

  Context {Σ : Signature}.

  (* First define weakening, as an auxiliary function for substition. *)

  (* Actually easier to define not just weakening, but “weakening + contraction
     + exchange”, i.e. substitution of variables for variables. *)
  Fixpoint Raw_Weaken {γ γ' : Proto_Cxt} (f : γ -> γ')
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Syntax Σ cl γ'.
  Proof.
    destruct e as [ γ i | γ S args ].
  - exact (var_raw (f i)).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ _ _ _ (args i)).
    simple refine (coprod_rect (shape_is_coprod) _ _ _); cbn.
    + intros x. apply (coprod_inj1 (shape_is_coprod)). exact (f x).
    + intros x. apply (coprod_inj2 (shape_is_coprod)). exact x.
  Defined.

  Definition Raw_Context_Map_Extending (γ γ' δ : Proto_Cxt)
    : Raw_Context_Map Σ γ' γ
   -> Raw_Context_Map Σ (shape_coprod γ' δ) (shape_coprod γ δ).
  Proof.
    intros f.
    simple refine (coprod_rect (shape_is_coprod) _ _ _); cbn.
    - intros i. refine (Raw_Weaken _ (f i)).
      apply (coprod_inj1 (shape_is_coprod)).
    - intros i. apply var_raw.
      apply (coprod_inj2 (shape_is_coprod)), i.
  Defined.

  Fixpoint Raw_Subst
      {γ γ' : Proto_Cxt} (f : Raw_Context_Map Σ γ' γ)
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Syntax Σ cl γ'.
  Proof.
    destruct e as [ γ i | γ S args ].
  - exact (f i).
  - refine (symb_raw S _). intros i.
    refine (Raw_Subst _ _ _ _ (args i)).
    apply Raw_Context_Map_Extending. exact f.
  Defined.

End Raw_Subst.

Section Raw_Context_Construction.

Definition empty_Raw_Context {Σ} : Raw_Context Σ.
Proof.
  exists (shape_empty _). apply (empty_rect _ shape_is_empty).
Defined.

Definition snoc_Raw_Context {Σ} (Γ : Raw_Context Σ) (A : Raw_Syntax Σ Ty Γ)
  : Raw_Context Σ.
Proof.
  exists (shape_extend _ Γ). 
  apply (plusone_rect _ _ (shape_is_plusone _ _)).
  - refine (Raw_Weaken _ A).
    (* As we put the type into the context, we weaken it to live over the extended context. *)
    apply (plusone_next _ _ (shape_is_plusone _ _)).
  - intros i. refine (Raw_Weaken _ (Γ i)).
    apply (plusone_next _ _ (shape_is_plusone _ _)).
Defined.

End Raw_Context_Construction.

Notation " [: :] " := (empty_Raw_Context) (format "[: :]") : cxt_scope.
Notation " [: x ; .. ; z :] " := (snoc_Raw_Context .. (snoc_Raw_Context (empty_Raw_Context) x) .. z) : cxt_scope.
Open Scope cxt_scope.


Section Judgements.
  (* The four basic forms are “hypothetical”, i.e. over a context. *)
  Inductive Hyp_Judgt_Form
    := obj_HJF (cl : Syn_Class) | eq_HJF (cl : Syn_Class).

  (* Contexts are also a judgement form. *)
  Inductive Judgt_Form
    := Cxt_JF | HJF (hjf : Hyp_Judgt_Form).

  (* Indices for each kind of judgement form. *)
  (* TODO if we need to access the head and boundaries. *)

  Definition Hyp_Judgt_Form_Slots (hjf : Hyp_Judgt_Form)
    : Family Syn_Class
    := match hjf with
        (* Head of the type judgement *)
        | obj_HJF Ty => [< Ty >]
        (* Both types involved in the equality *)
        | eq_HJF Ty  => [< Ty ; Ty >]
        (* Head: term ; Boundary: its type *)
        | obj_HJF Tm => [< Tm ; Ty >]
        (* Boundary : the type ; both terms involved *)
        | eq_HJF Tm  => [< Ty ; Tm ; Tm >]
      end.

  Definition Judgt_Form_Instance Σ (jf : Judgt_Form) : Type
  := match jf with
       | Cxt_JF => Raw_Context Σ
       | HJF hjf => { Γ : Raw_Context Σ
                   & forall i : Hyp_Judgt_Form_Slots hjf,
                         Raw_Syntax Σ (val _ i) Γ }
     end.

  Definition Judgt_Instance Σ
    := { jf : Judgt_Form & Judgt_Form_Instance Σ jf }.

  (* TODO: this is horrible, but is needed below for instantiations.  Would be better to inline it, once we have somehow refactored how judgement instances are defined.

  One option: “slots”.  Other options: ???

  If “slots”, then need TODO: infrastructure of families from lists. *)
  (* Definition Fmap_Judgt_Instance {Σ Σ'} (f : Proto_Cxt -> Proto_Cxt) *)
  (*   (g : forall cl γ, Raw_Syntax Σ cl γ -> Raw_Syntax Σ' cl (f γ)) *)
  (*   (h : Raw_Context Σ -> Raw_Context Σ') *)
  (* : Judgt_Instance Σ -> Judgt_Instance Σ'. *)
  (* Admitted. *)

End Judgements.

Section Algebraic_Extensions.

  (* The extension of a signature by symbols representing metavariables, as used to write each rule.

  The *arity* here would be the overall argument of the constructor that the rule introduces: the metavariable symbols introduced correspond to the arguments of the arity.

  E.g. lambda-abstraction has arity < (Ty,•), (Ty,{x}), (Tm,{x}) >.  So in the metavariable extension by this arity, we add three symbols — call them A, B, and b — with arities as follows:

  Symbol   Class  Arity
  A        Ty     < >
  B        Ty     <(Tm,•)>
  b        Tm     <(Tm,•)>

  allowing us to write expressions like x:A |– b(x) : B(x). 
  *)

  Definition metavariable_arity (γ : Proto_Cxt) : Arity
  := {| Inds := γ ; val i := (Tm, shape_empty _) |}.

  Definition Metavariable_Extension (Σ : Signature) (a : Arity) : Signature.
  Proof.
    refine (Sum_Family Σ _).
    refine (Fmap_Family _ a).
    intros cl_γ. exact (fst cl_γ, metavariable_arity (snd cl_γ)).
  Defined.

  Definition Instantiation (a : Arity) (Σ : Signature) (γ : Proto_Cxt)
    : Type
  := forall i : a,
       Raw_Syntax Σ (arg_class i) (shape_coprod γ (arg_pcxt i)).

  Definition instantiate
      {a : Arity} {Σ : Signature} {γ : Proto_Cxt}
      (I : Instantiation a Σ γ)
      {cl} {δ} (e : Raw_Syntax (Metavariable_Extension Σ a) cl δ)
    : Raw_Syntax Σ cl (shape_coprod γ δ).
  Proof.
    induction e as [ δ i | δ [S | M] args Inst_arg ].
  - refine (var_raw _).
    exact (coprod_inj2 (shape_is_coprod) i).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ (Inst_arg i)).
    apply (coprod_assoc
             shape_is_coprod shape_is_coprod
             shape_is_coprod shape_is_coprod).
  - simpl in M. (* Substitute [args] into the expression [I M]. *)
    refine (Raw_Subst _ (I M)).
    refine (coprod_rect shape_is_coprod _ _ _).
    + intros i. apply var_raw, (coprod_inj1 shape_is_coprod), i.
    + intros i.
      refine (Raw_Weaken _ (Inst_arg i)). cbn.
      refine (fmap_coprod shape_is_coprod shape_is_coprod _ _).
      exact (fun j => j).
      exact (coprod_empty_r shape_is_coprod shape_is_empty).
  Defined.

  Global Arguments instantiate {_ _ _} _ [_ _] _.

  Definition instantiate_context
      {a : Arity} {Σ : Signature} {Γ : Raw_Context Σ}
      (I : Instantiation a Σ Γ)
      (Δ : Raw_Context (Metavariable_Extension Σ a))
    : Raw_Context Σ.
  Proof.
     exists (shape_coprod Γ Δ).
        apply (coprod_rect shape_is_coprod).
        + intros i.
          refine (Raw_Weaken _ (Γ i)).
          exact (coprod_inj1 shape_is_coprod).
        + intros i.
          exact (instantiate I (Δ i)).
  Defined.

  Definition instantiate_ji
      {a : Arity} {Σ : Signature} {Γ : Raw_Context Σ}
      (I : Instantiation a Σ Γ)
      (e : Judgt_Instance (Metavariable_Extension Σ a))
    : Judgt_Instance Σ.
  Proof.
    destruct e as [jf jfi]. exists jf ; destruct jf ; simpl in *.
    - apply (instantiate_context I). assumption.
    - destruct jfi as [Δ hjfi].
      simple refine (existT _ _ _).
      + apply (instantiate_context I). assumption.
      + simpl. intro i. apply (instantiate I (hjfi i)).
  Defined.

End Algebraic_Extensions.


Section Raw_Rules.

  Context {Σ : Signature}.

  Record Raw_Rule
  :=
    { RR_metas : Arity
    ; RR_prem : Family (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    ; RR_concln : (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    }.

  Definition CCs_of_RR (R : Raw_Rule)
    : Family (Closure_Condition (Judgt_Instance Σ)).
  Proof.
    exists { Γ : Raw_Context Σ & Instantiation (RR_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Fmap_Family _ (RR_prem R)).
      apply (instantiate_ji I).
    - apply (instantiate_ji I).
      apply (RR_concln R).
  Defined.

End Raw_Rules.

Global Arguments Raw_Rule _ : clear implicits.

Section Raw_Type_Theories.

  Definition Raw_Type_Theory
  := { Σ : Signature & Family (Raw_Rule Σ) }.

(*
  Definition Derivation_TT {Σ} (Rs : Family (Raw_Rule Σ))
    : Judgt_Instance Σ -> Type.
*)


End Raw_Type_Theories.
