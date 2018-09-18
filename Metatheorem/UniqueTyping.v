
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Raw.RawTypeTheory.
Require Import Typed.TypeTheory.

(* Main goal of this file: theorem stating unique typing, for any (fully typed) type theory. *)

Theorem unique_typing {σ : shape_system} (T : raw_type_theory σ)
    (Σ := RawTypeTheory.signature T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : RawTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : RawTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : RawTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Abort.

(* Sketch proof: ????

Presumably: will need to generalised to derivations with hypotheses — specifcally, to derivations over an arbitrary _algebraic  extension_ of a type theory. *)
