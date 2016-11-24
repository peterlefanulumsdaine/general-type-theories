
Require Import Auxiliary.

(* Background: abstracting proto-contexts *)

Section ProtoCxts.

Record ProtoCxtSystem :=
  { ProtoCxt :> Type
  ; vars : ProtoCxt -> Type (* maybe should be to sets?? *)
  ; protocxt_empty : ProtoCxt
  ; protocxt_is_empty : is_empty (vars protocxt_empty)
  ; protocxt_coprod : ProtoCxt -> ProtoCxt -> ProtoCxt
  ; protocxt_is_coprod
     : forall γ δ : ProtoCxt,
       is_coprod (vars (protocxt_coprod γ δ)) (vars γ) (vars δ)
  ; protocxt_extend : ProtoCxt -> ProtoCxt
  ; protocxt_is_plusone         (* TODO: change to is_extend (Andrej?) *)
     : forall γ : ProtoCxt,
       is_plusone (vars (protocxt_extend γ)) (vars γ)
  }.

Global Arguments protocxt_coprod {_} _ _.
Global Arguments protocxt_is_coprod {_} [_ _].
Global Arguments protocxt_is_empty {_}.

Coercion vars : ProtoCxt >-> Sortclass.

End ProtoCxts.

Parameter PCxt : ProtoCxtSystem.
(* TODO: improve naming *)

Section Signatures.

  Inductive Syn_Class : Type := Ty | Tm.

  Definition Arity : Type
    := Family (Syn_Class * PCxt).

  (* Entries in the family represent arguments of a constructor; the [ProtoCxt] component represents the variables bound in each argument.

  For instance, the [Π-intro] rule (i.e. fully annotated λ-abstraction) would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,1)] ]; application would have arity [ Family_from_List [(Ty,0), (Ty,1), (Tm,0), (Tm,0)]].

  The use of [Family] instead of just [list] serves two purposes.  Firstly, it abstracts the aspects of the [list] version that we really need, and so makes the code significantly cleaner/more robust.  Secondly, it allows this definition to be re-used for non-finitary syntax, although we do not intend to explore that for now. *)

  (* Access functions for arity *)
  Definition arg_class {a : Arity} (i : a) : Syn_Class := fst (a i).
  Definition arg_pcxt {a : Arity} (i : a) : PCxt := snd (a i).

  Definition Signature : Type
    := Family (Syn_Class * Arity).

  Definition class {Σ : Signature} (S : Σ) : Syn_Class
  := fst (Σ S).

  Definition arity {Σ : Signature} (S : Σ) : Arity
  := snd (Σ S).

  (* Alternatives:
    := { Symbols : Syn_Class -> Arity -> Type }.

  or
    := { Symbols : Syn_Class -> Type
       ; arity : forall cl, Symbols cl -> Arity }.

  or
    := { Symbol : Type ;
         class : Symbol -> Syn_Class ;
         arity : Symbol -> Arity }.
  *)

End Signatures.

Section Raw_Syntax.

  Context {Σ : Signature}.

  (* A raw syntactic expression of a syntactic class, relative to a context *)
  Inductive Raw_Syntax
    : Syn_Class -> PCxt -> Type
  :=
  (* a variable in a context is a term in that context *)
    | var_raw (γ : PCxt) (i : γ)
        : Raw_Syntax Tm γ
    (* relative to a context [γ], given a symbol [S], if for each of its
       arguments we have a raw syntactic expression relative to [γ] extended by
       the argument's arity, [S args] is a raw syntactic expression over [γ] *)
    | symb_raw (γ : PCxt) (S : Σ)
               (args : forall (i : arity S),
                   Raw_Syntax (arg_class i)
                              (protocxt_coprod γ (arg_pcxt i)))
      : Raw_Syntax (class S) γ.

  Global Arguments var_raw [_] _.
  Global Arguments symb_raw [_] _ _.

  (* A raw context is a proto-ctx ("collection of identifiers") and a raw syntactic type expression 
     for each identifier in the proto-ctx. *)
  Record Raw_Context
  := { PCxt_of_Raw_Context :> PCxt
     ; var_type_of_Raw_Context
         :> forall i : PCxt_of_Raw_Context,
            Raw_Syntax Ty PCxt_of_Raw_Context
     }.

  Definition Raw_Context_Map (γ δ : PCxt)
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
  Fixpoint Raw_Weaken {γ γ' : PCxt} (f : γ -> γ')
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Syntax Σ cl γ'.
  Proof.
    destruct e as [ γ i | γ S args ].
  - exact (var_raw (f i)).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ _ _ _ (args i)).
    simple refine (coprod_rect (protocxt_is_coprod) _ _ _); cbn.
    + intros x. apply (coprod_inj1 (protocxt_is_coprod)). exact (f x).
    + intros x. apply (coprod_inj2 (protocxt_is_coprod)). exact x.
  Defined.

  Definition Raw_Context_Map_Extending (γ γ' δ : PCxt)
    : Raw_Context_Map Σ γ' γ
   -> Raw_Context_Map Σ (protocxt_coprod γ' δ) (protocxt_coprod γ δ).
  Proof.
    intros f.
    simple refine (coprod_rect (protocxt_is_coprod) _ _ _); cbn.
    - intros i. refine (Raw_Weaken _ (f i)).
      apply (coprod_inj1 (protocxt_is_coprod)).
    - intros i. apply var_raw.
      apply (coprod_inj2 (protocxt_is_coprod)), i.
  Defined.

  Fixpoint Raw_Subst
      {γ γ' : PCxt} (f : Raw_Context_Map Σ γ' γ)
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

Section Algebraic_Extensions.

  Definition Extend (Σ : Signature) (a : Arity) : Signature.
  Proof.
    refine (Sum_Family Σ _).
    refine (Fmap_Family _ a).
    intros cl_γ. refine (fst cl_γ,_).
    refine {| Inds := snd (cl_γ) ; val := _ |}.
    intros i. exact (Tm, protocxt_empty _).
  Defined.

  Definition Instantiation (a : Arity) (Σ : Signature) (γ : PCxt)
    : Type
  := forall i : a,
       Raw_Syntax Σ (arg_class i) (protocxt_coprod γ (arg_pcxt i)).

  Definition instantiate
      (a : Arity) (Σ : Signature) (γ : PCxt)
      (I : Instantiation a Σ γ)
      {cl} {δ} (e : Raw_Syntax (Extend Σ a) cl δ)
    : Raw_Syntax Σ cl (protocxt_coprod γ δ).
  Proof.
    induction e as [ δ i | δ [S | M] args Inst_arg ].
  - refine (var_raw _).
    exact (coprod_inj2 (protocxt_is_coprod) i).
  - refine (symb_raw S _). intros i.
    refine (Raw_Weaken _ (Inst_arg i)).
    apply (coprod_assoc
             protocxt_is_coprod protocxt_is_coprod
             protocxt_is_coprod protocxt_is_coprod).
  - simpl in M. (* Substitute [args] into the expression [I M]. *)
    refine (Raw_Subst _ (I M)).
    refine (coprod_rect protocxt_is_coprod _ _ _).
    + intros i. apply var_raw, (coprod_inj1 protocxt_is_coprod), i.
    + intros i. 
      refine (Raw_Weaken _ (Inst_arg i)). cbn.
      refine (fmap_coprod protocxt_is_coprod protocxt_is_coprod _ _).
      exact (fun j => j).
      exact (coprod_empty_r protocxt_is_coprod protocxt_is_empty).
  Defined.

End Algebraic_Extensions.

Section Judgements.
  (* The four basic forms are “hypothetical”, i.e. over a context. *)
  Inductive Hyp_Judgt_Form
    := obj_HJF (cl : Syn_Class) | eq_HJF (cl : Syn_Class).
  
  (* Contexts are also a judgement form. *)
  Inductive Judgt_Form
    := Cxt_JF | JF (hjf : Hyp_Judgt_Form).
  
  Definition Hyp_Judgt_Bdry_Instance Σ (hjf : Hyp_Judgt_Form) (γ : PCxt) : Type
    := match hjf with
         | obj_HJF Ty => unit
         | eq_HJF Ty => (Raw_Syntax Σ Ty γ) * (Raw_Syntax Σ Ty γ)
         | obj_HJF Tm => (Raw_Syntax Σ Ty γ)
         | eq_HJF Tm => (Raw_Syntax Σ Ty γ) * (Raw_Syntax Σ Tm γ) * (Raw_Syntax Σ Tm γ) 
       end.

  Definition Hyp_Judgt_Head_Instance Σ (hjf : Hyp_Judgt_Form) (γ : PCxt) : Type
    := match hjf with
         | obj_HJF cl => Raw_Syntax Σ cl γ
         | eq_HJF cl => unit
       end.

  Definition Judgt_Form_Instance Σ (jf : Judgt_Form) : Type
  := match jf with 
       | Cxt_JF => Raw_Context Σ
       | JF hjf => { γ : Raw_Context Σ 
                   & Hyp_Judgt_Bdry_Instance Σ hjf γ
                   * Hyp_Judgt_Head_Instance Σ hjf γ }
     end.

  Definition Judgt_Instance Σ
    := { jf : Judgt_Form & Judgt_Form_Instance Σ jf }.

End Judgements.

(* Could (?should) abstract away [Judgt_Instance] to an arbitrary type in the def of closure conditions and deductive closure. *)
Section Deductive_Closure.

  Definition Derivability_Relation Σ
    := Judgt_Instance Σ -> Type.

  Record Closure_Condition Σ
    :=
      { CC_prem : Family (Judgt_Instance Σ)
      ; CC_concln : Judgt_Instance Σ
      }.

  Arguments CC_prem [_] _.
  Arguments CC_concln [_] _.

  Inductive Deductive_Closure {Σ}
    (Rs : Family (Closure_Condition Σ))
      : Derivability_Relation Σ
  := deduce 
      (R : Rs)
      (prem_derivs : forall p : CC_prem (Rs R),
                         Deductive_Closure Rs (CC_prem _ p))
     : Deductive_Closure Rs (CC_concln (Rs R)).

End Deductive_Closure.



