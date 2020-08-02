
Require Import Auxiliary.Family.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.PresentedRawTypeTheory.
Require Import Presented.TypeTheory.

(* Main goal of this file: theorem stating unique typing, for any (fully typed) type theory. *)

Theorem unique_typing {σ : scope_system} (T : presented_raw_type_theory σ)
    (Σ := PresentedRawTypeTheory.signature T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : PresentedRawTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : PresentedRawTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : PresentedRawTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Abort.

(* Sketch proof: ????

Presumably: will need to generalised to derivations with hypotheses — specifcally, to derivations over an arbitrary _algebraic  extension_ of a type theory. *)
