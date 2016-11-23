
Require Import Auxiliary.
Require Import Vectors.Fin.

(* Background: abstracting proto-contexts *)

Section ProtoCxts.

Record ProtoCxtSystem :=
  { ProtoCxt :> Type
  ; vars : ProtoCxt -> Type (* maybe should be to sets?? *)
  ; protocxt_coprod : ProtoCxt -> ProtoCxt -> ProtoCxt
  ; protocxt_is_coprod
     : forall γ δ : ProtoCxt,
       is_coprod (vars (protocxt_coprod γ δ)) (vars γ) (vars δ)
  ; protocxt_extend : ProtoCxt -> ProtoCxt
  ; protocxt_is_plusone
     : forall γ : ProtoCxt,
       is_plusone (vars (protocxt_extend γ)) (vars γ)
  }.

Global Arguments protocxt_coprod {_} _ _.

Coercion vars : ProtoCxt >-> Sortclass.

Definition deBruijn : ProtoCxtSystem.
Proof.
  simple refine (Build_ProtoCxtSystem _ _ _ _ _ _).
  - exact nat.
  - exact Fin.t. (* should be fin *)
  - admit. (* should be + *)
  - admit.
  - admit. (* should be +1 *)
  - admit.
Admitted.

Definition natVars : ProtoCxtSystem.
Proof.
  simple refine (Build_ProtoCxtSystem _ _ _ _ _ _).
  - admit. (* finite subsets of nat *)
  - admit. (* should be El *)
  - admit. (* should be some implementation of disjoint union *)
  - admit.
  - admit. (* should be some choice of fresh var *)
  - admit.
Admitted.

(* Should also generalise to any constructively infinite type. *)
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

  Record Signature : Type
    := { Symbol : Type ;
         class : Symbol -> Syn_Class ;
         arity : Symbol -> Arity }.

  Global Arguments class {_} _.
  Global Arguments arity {_} _.

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

  Parameter (Σ : Signature).

  Inductive Raw_Syntax
  : Syn_Class -> PCxt -> Type
    :=
    | var_raw (γ : PCxt) (i : γ)
        : Raw_Syntax Tm γ
    | symb_raw (γ : PCxt) (S : Symbol Σ)
               (args : forall (i : arity S),
                   Raw_Syntax (arg_class i)
                              (protocxt_coprod γ (arg_pcxt i)))
      : Raw_Syntax (class S) γ.

  Record Raw_Context
  := { PCxt_of_Raw_Context :> PCxt
     ; var_type_of_Raw_Context
         : forall i : PCxt_of_Raw_Context,
           Raw_Syntax Ty PCxt_of_Raw_Context
     }.
  
  Coercion var_type_of_Raw_Context : Raw_Context >-> Funclass.

  Definition Raw_Context_Map (γ δ : PCxt)
    := δ -> Raw_Syntax Tm γ.

  (* Not really weakining, but weakening + contraction + exchange *)
  Fixpoint Raw_Weaken {γ γ' : PCxt} (f : γ -> γ')
      {cl : Syn_Class} (t : Raw_Syntax cl γ)
    : Raw_Syntax cl γ'.
  Proof.
    destruct t as [ γ i | γ S args ].
  - exact (var_raw _ (f i)).
  - refine (symb_raw γ' S _). intros i.
    refine (Raw_Weaken _ _ _ _ (args i)).
    simple refine (coprod_rect _ _ _ (protocxt_is_coprod _ _ _) _ _ _); cbn.
    + intros x. apply (inj1 _ _ _ (protocxt_is_coprod _ _ _)), f, x.
    + intros x. apply (inj2 _ _ _ (protocxt_is_coprod _ _ _)), x.
  Defined.
  (* TODO: add implicit arguments as the above terms indicate *)

  Definition Raw_Context_Map_Extending (γ γ' δ : PCxt)
    : Raw_Context_Map γ' γ
   -> Raw_Context_Map (protocxt_coprod γ' δ) (protocxt_coprod γ δ).
  Proof.
    intros f.
    simple refine (coprod_rect _ _ _ (protocxt_is_coprod _ _ _) _ _ _); cbn.
    - intros i. refine (Raw_Weaken _ (f i)). 
      apply (inj1 _ _ _ (protocxt_is_coprod _ _ _)).
    - intros i. refine (var_raw _ _). 
      apply (inj2 _ _ _ (protocxt_is_coprod _ _ _)), i.
  Defined.

  Fixpoint Raw_Subst
      {γ γ' : PCxt} (f : Raw_Context_Map γ' γ)
      {cl : Syn_Class} (t : Raw_Syntax cl γ)
    : Raw_Syntax cl γ'.
  Proof.
    destruct t as [ γ i | γ S args ].
  - exact (f i).
  - refine (symb_raw γ' S _). intros i.
    refine (Raw_Subst _ _ _ _ (args i)).
    apply Raw_Context_Map_Extending. exact f.
  Defined.

End Raw_Syntax.



