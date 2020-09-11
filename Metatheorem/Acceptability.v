
Require Import HoTT.

Require Import Syntax.All.
Require Import Typing.All.
Require Import Metatheorem.UniqueTyping.
Require Import Metatheorem.SubstElimination.
Require Import Metatheorem.Presuppositions.


Definition acceptable {σ} {Σ : signature σ} (T : flat_type_theory Σ)
  : Type
:= (is_tight_type_theory T)
  * (substitutive T)
  * (congruous T)
  * (presuppositive_flat_type_theory T).
  
      


        
