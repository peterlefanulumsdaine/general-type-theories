
Require Import Auxiliary.
Require Import Vectors.Fin.

(* Background: abstracting proto-contexts *)

Parameter is_coprod : forall X Y Z : Type, Type.
Parameter is_extend_by_1 : forall X Y : Type, Type.

Section ProtoCxts.

Record ProtoCxtSystem :=
  { ProtoCxt :> Type
  ; vars : ProtoCxt -> Type (* should be to sets?? *)
  ; protocxt_coprod : ProtoCxt -> ProtoCxt -> ProtoCxt
  ; _ : forall γ δ : ProtoCxt, is_coprod (vars (protocxt_coprod γ δ)) (vars γ) (vars δ)
  ; protocxt_extend : ProtoCxt -> ProtoCxt
  ; _ : forall γ : ProtoCxt, is_extend_by_1 (vars (protocxt_extend γ)) (vars γ)
  }.

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

  Record Signature : Type
    := { Symbol : Type ;
         class : Symbol -> Syn_Class ;
         arity : Symbol -> Arity }.

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

  (* If I put these in their respective section, it doesn't apply in this
   * one...  *)
  Arguments class {_} _.
  Arguments arity {_} _.
  Arguments protocxt_coprod {_} _ _.

  Inductive Raw_Syntax (Σ : Signature)
  : Syn_Class -> PCxt -> Type
    :=
    | var_raw (γ : PCxt) (i : γ)
        : Raw_Syntax Σ Tm γ
    | symb_raw (γ : PCxt) (S : Symbol Σ)
               (args : forall (i : arity S),
                   Raw_Syntax Σ (fst (arity S i))
                                (protocxt_coprod γ (snd (arity S i))))
      : Raw_Syntax Σ (class S) γ.

End Raw_Syntax.
