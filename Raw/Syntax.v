Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystems.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.DeductiveClosure.

(* Throughout, we fix a shape system.  It can be implicit in almost everything that depends on it.

TODO: modules would probably be a better way to treat this. *)

Section Signatures.

  Context {σ : Shape_System}.

  Inductive Syn_Class : Type := Ty | Tm.

  Definition Arity : Type
    := Family (Syn_Class * Shape σ).

  (* Entries in the family represent arguments of a constructor; the [σ] component represents the variables bound in each argument.

  For instance, the [Π-intro] rule (i.e. fully annotated λ-abstraction) would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,1)] ]; application would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,0), (Tm,0)]].

  The use of [Family] instead of e.g. [list] serves two purposes.  Firstly, it abstracts the aspects of the [list] version that we really need, and so makes the code significantly cleaner/more robust.  Secondly, it allows this definition to be later re-used for non-finitary syntax, although we do not intend to explore that for now. *)

  (* Access functions for arity *)
  Definition arg_class {a : Arity} (i : a) : Syn_Class := fst (a i).
  Definition arg_pcxt {a : Arity} (i : a) : σ := snd (a i).

  Definition Signature : Type
    := Family (Syn_Class * Arity).

  Definition class {Σ : Signature} (S : Σ) : Syn_Class
  := fst (Σ S).

  Definition arity {Σ : Signature} (S : Σ) : Arity
  := snd (Σ S).

End Signatures.

Arguments Signature _ : clear implicits.
Arguments Arity _ : clear implicits.

Section Raw_Syntax.

  Context {σ : Shape_System}.
  Context {Σ : Signature σ}.

  (* A raw syntactic expression of a syntactic class, relative to a context *)
  Inductive Raw_Syntax
    : Syn_Class -> Shape σ -> Type
  :=
    (* a variable in a context is a term in that context *)
    | var_raw (γ : Shape σ) (i : γ)
        : Raw_Syntax Tm γ
    (* relative to a context [γ], given a symbol [S], if for each of its
       arguments we have a raw syntactic expression relative to [γ] extended by
       the argument's arity, [S args] is a raw syntactic expression over [γ] *)
    | symb_raw (γ : σ) (S : Σ)
               (args : forall (i : arity S),
                   Raw_Syntax (arg_class i)
                              (shape_coproduct γ (arg_pcxt i)))
      : Raw_Syntax (class S) γ.

  Global Arguments var_raw [_] _.
  Global Arguments symb_raw [_] _ _.

  (* A raw context is a proto-ctx ("collection of identifiers") and a raw syntactic type expression
     for each identifier in the proto-ctx. *)
  Record Raw_Context
  := { Proto_Context_of_Raw_Context :> Shape σ
     ; var_type_of_Raw_Context
         :> forall i : Proto_Context_of_Raw_Context,
            Raw_Syntax Ty Proto_Context_of_Raw_Context
     }.

  Definition Raw_Context_Map (γ δ : σ)
    := δ -> Raw_Syntax Tm γ.

  (* A couple of utility functions: *)

  (* A useful abbreviation for giving functions constructing raw syntax:
  the type of suitable arguments for a given arity, in a given context. *)
  Definition Args (a : Arity _) γ : Type
  := forall (i : a),
    Raw_Syntax (arg_class i) (shape_coproduct γ (arg_pcxt i)).

  (* Useful, with [idpath] as the equality argument, when want wants to construct the smybol argument interactively — this is difficult with original [symb_raw] due to [class S] appearing in the conclusion. *)
  Definition symb_raw'
      {γ} {cl} (S : Σ) (e : class S = cl)
      (args : Args (arity S) γ)
    : Raw_Syntax cl γ.
  Proof.
    destruct e.
    apply symb_raw; auto.
  Defined.

End Raw_Syntax.

Global Arguments Raw_Syntax {_} _ _ _ : clear implicits.
Global Arguments Raw_Context {_} _ : clear implicits.
Global Arguments Raw_Context_Map {_} _ _ _ : clear implicits.
Global Arguments Args {_} _ _ _ : clear implicits.

Section Raw_Subst.

  Context {σ : Shape_System}.
  Context {Σ : Signature σ}.

  (* First define weakening, as an auxiliary function for substition. *)

  (* Actually easier to define not just weakening, but “weakening + contraction
     + exchange”, i.e. substitution of variables for variables. *)
  Fixpoint Raw_Weaken {γ γ' : σ} (f : γ -> γ')
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Syntax Σ cl γ'.
  Proof.
    destruct e as [ γ i | γ S args ].
  - exact (var_raw (f i)).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ _ _ _ (args i)).
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn.
    + intros x. apply (coproduct_inj1 (shape_is_coproduct)). exact (f x).
    + intros x. apply (coproduct_inj2 (shape_is_coproduct)). exact x.
  Defined.

  Definition Raw_Context_Map_Extending (γ γ' δ : σ)
    : Raw_Context_Map Σ γ' γ
   -> Raw_Context_Map Σ (shape_coproduct γ' δ) (shape_coproduct γ δ).
  Proof.
    intros f.
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn.
    - intros i. refine (Raw_Weaken _ (f i)).
      apply (coproduct_inj1 (shape_is_coproduct)).
    - intros i. apply var_raw.
      apply (coproduct_inj2 (shape_is_coproduct)), i.
  Defined.

  Fixpoint Raw_Subst
      {γ γ' : σ} (f : Raw_Context_Map Σ γ' γ)
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

Context {σ : Shape_System}.
Context {Σ : Signature σ}.

Definition empty_Raw_Context : Raw_Context Σ.
Proof.
  exists (shape_empty _). apply (empty_rect _ shape_is_empty).
Defined.

Definition snoc_Raw_Context (Γ : Raw_Context Σ) (A : Raw_Syntax Σ Ty Γ)
  : Raw_Context Σ.
Proof.
  exists (shape_extend _ Γ).
  apply (plusone_rect _ _ (shape_is_plusone _ _)).
  - refine (Raw_Weaken _ A).
    (* As we put the type into the context, we weaken it to live over the extended context. *)
    apply (plusone_inj _ _ (shape_is_plusone _ _)).
  - intros i. refine (Raw_Weaken _ (Γ i)).
    apply (plusone_inj _ _ (shape_is_plusone _ _)).
Defined.

End Raw_Context_Construction.

Notation " [: :] " := (empty_Raw_Context) (format "[: :]") : cxt_scope.
Notation " [: x ; .. ; z :] " := (snoc_Raw_Context .. (snoc_Raw_Context (empty_Raw_Context) x) .. z) : cxt_scope.
Open Scope cxt_scope.


Section Judgements.
  Context {σ : Shape_System}.
  Context (Σ : Signature σ).

  (* The four basic forms are “hypothetical”, i.e. over a context. *)
  Inductive Hyp_Judgt_Form
    := obj_HJF (cl : Syn_Class) | eq_HJF (cl : Syn_Class).

  Definition is_obj_HJF : Hyp_Judgt_Form -> Type
    := fun hjf => match hjf with
                     | obj_HJF _ => Unit
                     | eq_HJF _ => Empty
                  end.

  Definition class_of_HJF : Hyp_Judgt_Form -> Syn_Class
    := fun hjf => match hjf with
                     | obj_HJF cl => cl
                     | eq_HJF cl => cl
                  end.

  (* Contexts are also a judgement form. *)
  Inductive Judgt_Form
    := Cxt_JF | HJF (hjf : Hyp_Judgt_Form).

  (* Indices for each kind of judgement form. *)
  (* TODO if we need to access the head and boundaries. *)

  Definition Hyp_Obj_Judgt_Bdry_Slots (cl : Syn_Class)
  := match cl with
       (* No hypothetical part in boundary of a type judgement *)
       | Ty => [< >]
       (* Boundary of a term judgement: the type of the term *)
       | Tm => [< Ty >]
     end.

  Definition Hyp_Judgt_Bdry_Slots (hjf : Hyp_Judgt_Form)
    : Family Syn_Class
  := match hjf with
       (* object judgement boundary: as defined in [Hyp_Obj_Judgt_Bdry_Slots] *)
       | obj_HJF cl => Hyp_Obj_Judgt_Bdry_Slots cl
       (* equality judgement boundary: a boundary of the corresponding object-judgement, together with two objects of the given class *)
       | eq_HJF cl  => Snoc (Snoc (Hyp_Obj_Judgt_Bdry_Slots cl) cl) cl
     end.

  Definition Hyp_Judgt_Form_Slots (hjf : Hyp_Judgt_Form)
    : Family Syn_Class
  := match hjf with
       (* Equality case: boundary is everything *)
       | eq_HJF cl =>
           Hyp_Judgt_Bdry_Slots (eq_HJF cl)
       (* Object case: add the head slot *)
       | obj_HJF cl =>
           Snoc (Hyp_Judgt_Bdry_Slots (obj_HJF cl)) cl
     end.
  (* NOTE: the order of slots for term judgements follows “dependency order” — later slots are (morally) dependent on earlier ones, so the type comes before the term.  However, the functions in section [Judgement_Notations] below follow standard written order, so the term comes before the type. *)

  Definition Hyp_Judgt_Bdry_Instance (hjf : Hyp_Judgt_Form) γ : Type
  := forall i : Hyp_Judgt_Bdry_Slots hjf, Raw_Syntax Σ (fam_element _ i) γ.

  Definition Hyp_Judgt_Form_Instance (hjf : Hyp_Judgt_Form) γ : Type
  := forall i : Hyp_Judgt_Form_Slots hjf, Raw_Syntax Σ (fam_element _ i) γ.

  Definition Judgt_Bdry_Instance (jf : Judgt_Form) : Type
  := match jf with
       | Cxt_JF => Unit
       | HJF hjf => { Γ : Raw_Context Σ
                   & Hyp_Judgt_Bdry_Instance hjf Γ }
     end.

  Definition Judgt_Form_Instance (jf : Judgt_Form) : Type
  := match jf with
       | Cxt_JF => Raw_Context Σ
       | HJF hjf => { Γ : Raw_Context Σ
                   & Hyp_Judgt_Form_Instance hjf Γ }
     end.

  Definition Judgt_Instance
    := { jf : Judgt_Form & Judgt_Form_Instance jf }.

  Definition Hyp_Judgt_Instance_from_bdry_plus_head {hjf : Hyp_Judgt_Form} {γ}
      (bdry : Hyp_Judgt_Bdry_Instance hjf γ)
      (head : is_obj_HJF hjf -> Raw_Syntax Σ (class_of_HJF hjf) γ)
    : Hyp_Judgt_Form_Instance hjf γ.
  Proof.
    destruct hjf as [ ocl | ecl ].
    - (* case: object judgement *)
      intros [ i | ].
      + apply bdry.
      + apply head. constructor.
    - (* case: equality judgement *)
      apply bdry.
  Defined.

End Judgements.

Section Judgement_Notations.

  Context {σ : Shape_System}.
  Context {Σ : Signature σ}.

Definition give_Cxt_ji
  (Γ : Raw_Context Σ)
  : Judgt_Instance Σ.
Proof.
  exists Cxt_JF.
  exact Γ.
Defined.

Definition give_Ty_ji
  (Γ : Raw_Context Σ) (A : Raw_Syntax Σ Ty Γ)
  : Judgt_Instance Σ.
Proof.
  exists (HJF (obj_HJF Ty)).
  exists Γ.
  intros [ [] | ]; exact A.
Defined.

Definition give_TyEq_ji
  (Γ : Raw_Context Σ) (A A' : Raw_Syntax Σ Ty Γ)
  : Judgt_Instance Σ.
Proof.
  exists (HJF (eq_HJF Ty)).
  exists Γ.
  intros [ [ [] | ] | ].
  exact A.
  exact A'.
Defined.

Definition give_Tm_ji
  (Γ : Raw_Context Σ) (a : Raw_Syntax Σ Tm Γ) (A : Raw_Syntax Σ Ty Γ)
  : Judgt_Instance Σ.
Proof.
  exists (HJF (obj_HJF Tm)).
  exists Γ.
  intros [ [ [] | ] | ].
  exact A.
  exact a.
Defined.

(* TODO: consistentise order with [give_Term_ji]. *)
Definition give_TmEq_ji
  (Γ : Raw_Context Σ) (A : Raw_Syntax Σ Ty Γ) (a a': Raw_Syntax Σ Tm Γ)
  : Judgt_Instance Σ.
Proof.
  exists (HJF (eq_HJF Tm)).
  exists Γ.
  intros [ [ [ [] | ] | ] | ].
  exact A.
  exact a.
  exact a'.
Defined.

End Judgement_Notations.

Notation "'[Cxt!' |- Γ !]" := (give_Cxt_ji Γ) : judgement_scope.
Notation "'[Ty!' Γ |- A !]" := (give_Ty_ji Γ A) : judgement_scope.
Notation "'[TyEq!' Γ |- A ≡ A' !]" := (give_TyEq_ji Γ A A') : judgement_scope.
Notation "'[Tm!' Γ |- a ; A !]" := (give_Tm_ji Γ a A) : judgement_scope.
Notation "'[TmEq!' Γ |- a ≡ a' ; A !]" := (give_TmEq_ji Γ A a a') : judgement_scope.

Open Scope judgement_scope.

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

  Context {σ : Shape_System}.

  Definition simple_arity (γ : σ) : @Arity σ
  := {| fam_index := γ ; fam_element i := (Tm, shape_empty _) |}.

  Definition Metavariable_Extension (Σ : Signature σ) (a : @Arity σ) : Signature σ.
  Proof.
    refine (Sum Σ _).
    refine (Fmap_Family _ a).
    intros cl_γ. exact (fst cl_γ, simple_arity (snd cl_γ)).
  Defined.

  Definition inr_Metavariable {Σ : Signature σ} {a : @Arity σ}
    : a -> Metavariable_Extension Σ a
  := inr.

  Definition inl_Symbol {Σ : Signature σ} {a : @Arity σ}
    : Σ -> Metavariable_Extension Σ a
  := inl.

  (* TODO: not sure if this coercion is a good idea.  See how/if it works for a bit, then reconsider? *)
  (* Coercion inl_Symbol : Inds >-> Inds. *)

  (* To use rules, one *instantiates* their metavariables, as raw syntax of the ambient signature, over some context. *)
  Definition Instantiation (a : @Arity σ) (Σ : Signature σ) (γ : σ)
    : Type
  := forall i : a,
       Raw_Syntax Σ (arg_class i) (shape_coproduct γ (arg_pcxt i)).

  (* Given such an instantiation, one can translate syntax over the extended signature into syntax over the base signature. *)
  Definition instantiate
      {a : @Arity σ} {Σ : Signature σ} {γ : σ}
      (I : Instantiation a Σ γ)
      {cl} {δ} (e : Raw_Syntax (Metavariable_Extension Σ a) cl δ)
    : Raw_Syntax Σ cl (shape_coproduct γ δ).
  Proof.
    induction e as [ δ i | δ [S | M] args Inst_arg ].
  - refine (var_raw _).
    exact (coproduct_inj2 (shape_is_coproduct) i).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ (Inst_arg i)).
    apply (coproduct_assoc
             shape_is_coproduct shape_is_coproduct
             shape_is_coproduct shape_is_coproduct).
  - simpl in M. (* Substitute [args] into the expression [I M]. *)
    refine (Raw_Subst _ (I M)).
    refine (coproduct_rect shape_is_coproduct _ _ _).
    + intros i. apply var_raw, (coproduct_inj1 shape_is_coproduct), i.
    + intros i.
      refine (Raw_Weaken _ (Inst_arg i)). cbn.
      refine (Coproduct.fmap shape_is_coproduct shape_is_coproduct _ _).
      exact (fun j => j).
      exact (coproduct_empty_r shape_is_coproduct shape_is_empty).
  Defined.

  Global Arguments instantiate {_ _ _} _ [_ _] _.

  Definition instantiate_context
      {a : @Arity σ} {Σ : @Signature σ} {Γ : Raw_Context Σ}
      (I : Instantiation a Σ Γ)
      (Δ : Raw_Context (Metavariable_Extension Σ a))
    : Raw_Context Σ.
  Proof.
     exists (shape_coproduct Γ Δ).
        apply (coproduct_rect shape_is_coproduct).
        + intros i.
          refine (Raw_Weaken _ (Γ i)).
          exact (coproduct_inj1 shape_is_coproduct).
        + intros i.
          exact (instantiate I (Δ i)).
  Defined.

  Definition instantiate_ji
      {a : @Arity σ} {Σ : Signature σ} {Γ : Raw_Context Σ}
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

Section Metavariable_Notations.

(* Arities of symbols will arise in two ways:

  1. Arities we write by hand.

    These will typically use [< … >] notation.

  2. Arities of metavariables, from [Metavariable_Extension].

    These will have only (Ty, shape_empty) arguments, and be indexed by the positions of some protocxt, which will itself probably be built up by [shape_extend].

  So we give functions/notations for giving arguments for each of these forms.

  Eventually, one should be able to write e.g.

  [S/ A ; e1 , e2 , e3 /]

  [M/ A ; e1 , e2 , e3 /]

  for the expression consisting of a symbol S (resp. a metavariable symbol M) applied to expressions e1, e2, e3.

  For now we provide the [M/ … /] version, but not yet the general [S/ … /] version.
*)

Context {σ : Shape_System}.
Context {Σ : Signature σ}.

Definition empty_metavariable_args {γ}
  : Args Σ (simple_arity (shape_empty _)) γ
:= empty_rect _ shape_is_empty _.

Definition snoc_metavariable_args {γ δ : σ}
  : Args Σ (simple_arity δ) γ
  -> Raw_Syntax Σ Tm γ
  -> Args Σ (simple_arity (shape_extend _ δ)) γ.
Proof.
  intros ts t.
  simple refine (plusone_rect _ _ (shape_is_plusone _ δ) _ _ _); cbn.
  - refine (Raw_Weaken _ t).
    exact (coproduct_inj1 shape_is_coproduct).
  - exact ts.
Defined.

End Metavariable_Notations.

Notation " '[M/' A /] " := (symb_raw (inr_Metavariable A) empty_metavariable_args) : raw_syntax_scope.

Notation " '[M/' A ; x , .. , z /] "
  := (symb_raw (inr_Metavariable A) (snoc_metavariable_args .. (snoc_metavariable_args (empty_metavariable_args) x) .. z)) : raw_syntax_scope.

Open Scope raw_syntax_scope.

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
      refine (Fmap_Family _ (RR_prem R)).
      apply (instantiate_ji I).
    - apply (instantiate_ji I).
      apply (RR_concln R).
  Defined.

  Definition Raw_Type_Theory := Family Raw_Rule.

End Raw_Rules.

Arguments CCs_of_RR {_ _} _.

