
Require Import HoTT.

Require Import Syntax.All.
Require Import Typing.All.
Require Import Metatheorem.UniqueTyping.
Require Import Metatheorem.Elimination.
Require Import Metatheorem.Presuppositions.


Definition acceptable {σ} {Σ : signature σ} (T : raw_type_theory Σ)
  : Type
:= (is_tight_type_theory T)
  * (substitutive T)
  * (congruous T)
  * (presuppositive_raw_type_theory T).
