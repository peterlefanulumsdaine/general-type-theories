
Require Import Auxiliary.Family.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.All.

Definition tight_type_theory {σ} {Σ : signature σ} (T : flat_type_theory Σ)
  : Type.
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
