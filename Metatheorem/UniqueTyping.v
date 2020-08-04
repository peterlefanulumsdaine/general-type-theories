
Require Import HoTT.

Require Import Auxiliary.Family.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.All.

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

  Record one_to_one_correspondence {A B} (R : A -> B -> Type)
  := {
    forward : functional_relation R ;
    backward : functional_relation (flip R)
  }.

End Auxiliary.


Definition tight_rule {σ} {Σ : signature σ} (R : flat_rule Σ)
  : Type.
(* Outline: the relation between object premises P of R and arguments a of its arity
  given by “P introduces the metavariable for a”
  is a one-to-one correspondence. *)
Admitted. (* TODO: define tightness *)


Definition tight_type_theory {σ} {Σ : signature σ} (T : flat_type_theory Σ)
  : Type.
(* Outline: every rule of T is tight,
  and the relation between object rules R of T and symbols S of Σ
  given by “R introduces S”
  is a one-to-one correspondence. *)
Admitted. (* TODO: define tightness *)

(* Main goal of this file: theorem stating unique typing, for any tight type theory. *)

Theorem unique_typing {σ} {Σ : signature σ} (T : flat_type_theory Σ)
    (T_tight : tight_type_theory T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : FlatTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : FlatTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Abort.

(* Sketch proof: see paper. *)
