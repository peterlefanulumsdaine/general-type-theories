
Require Import HoTT.
Close Scope mc_scope. (* to make notations like [A * B] work easily *)

Require Import Auxiliary.Family.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.All.


(* Main goal of this file: theorem stating unique typing, for any tight type theory. *)

Theorem unique_typing {σ} {Σ : signature σ} (T : flat_type_theory Σ)
    (tight_type_theory : _ -> Type) (* tightness to be defined below *) 
    (T_tight : tight_type_theory T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : FlatTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Abort.


(* TODO: upstream contents of this section periodically, but keep this section as a holding pen as long as the file is under heavy development. *)   
Section Auxiliary.

  Record functional_relation {A B} (R : A -> B -> Type) : Type
  := {
    total (x:A) : { y : B & R x y } ;
    unique {x} {y y'}: R x y -> R x y' -> y = y' 
  }.

  Definition function_of_functional_relation
      {A B} {R : A -> B -> Type} (R_fun : functional_relation R)
    : A -> B
  := fun a => (total _ R_fun a).1.

  Coercion function_of_functional_relation : functional_relation >-> Funclass.

  Definition function_of_functional_relation_is_related
      {A B} {R : A -> B -> Type} {R_fun : functional_relation R} 
    : forall a : A, R a (R_fun a)
  := fun a => (total _ R_fun a).2.

  Record is_one_to_one_correspondence {A B} (R : A -> B -> Type)
  := {
    forward : functional_relation R ;
    backward : functional_relation (flip R)
  }.

End Auxiliary.

Section Fix_Scope_System.

Context {σ : scope_system}.

Definition flat_rule_object_premise {Σ : signature σ} (R : flat_rule Σ)
    : Type
  := {i : flat_rule_premise R
          & Judgement.is_object (form_of_judgement (flat_rule_premise R i))}.

Definition premise_introduces_meta {Σ : signature σ} {R : flat_rule Σ}
    (p : flat_rule_object_premise R) (m : flat_rule_metas R)
  : Type.
Proof.
  refine (Judgement.head (flat_rule_premise R p.1) p.2 = _).
  admit.
  (* slightly subtle:
  can’t just say “the head of premise p is the generic application of m”;
   need to say “the class is the same, the scope is the same,
   and modulo these, the head is the correct application”. *)
Admitted.

Definition is_tight_rule {Σ : signature σ} (R : flat_rule Σ)
  : Type
:= is_one_to_one_correspondence (@premise_introduces_meta _ R).

Definition flat_type_theory_object_rule
    {Σ : signature σ} (T : flat_type_theory Σ)
  : Type
:= { R :T & Judgement.is_object (form_of_judgement (flat_rule_conclusion (T R))) }.

Definition rule_introduces_symbol {Σ : signature σ} {T : flat_type_theory Σ}
    (R : flat_type_theory_object_rule T) (S : Σ)
  : Type.
Proof.
  (* similar to [premise_introduces_meta] above. *)
Admitted.

Definition is_tight_type_theory {Σ : signature σ} (T : flat_type_theory Σ)
    : Type
  := (forall R : T, is_tight_rule (T R))
     * is_one_to_one_correspondence (@rule_introduces_symbol _ T).

Theorem unique_typing {Σ : signature σ} (T : flat_type_theory Σ)
    (T_tight : is_tight_type_theory T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : FlatTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Proof.
Admitted.


(* Sketch proof: see paper. *)


End Fix_Scope_System.
