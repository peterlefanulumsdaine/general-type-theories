Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.TypeTheory.
Require Import Raw.SignatureMap.
Require Import Raw.Rule.
Require Import WellTyped.TypeTheory.

Section MartinLöfTypeTheory.
  Context {σ : shape_system}.

  Definition Σ : signature σ.
  Proof.
    refine [< _; _ >].
    - exact (class_type, [< >]). (* U *)
    - simple refine (class_type, [< (class_term, shape_empty σ) >]). (* El *)
  Defined.

  Local Definition U_formation_rule_index : (hypothetical_form * arity σ)
    := (form_object class_type  (* Formation of a type *)
       , [< >]).                (* With no (object) premises *)

  Local Definition El_formation_rule_index : (hypothetical_form * arity σ)
    := (form_object class_type
       , [< (class_term, shape_empty σ) >]).

  (* Definition f : *)


  Definition theory : Type_Theory σ.
   simple refine (Build_Type_Theory _ _ _).
   - exact ([< U_formation_rule_index ; El_formation_rule_index >]).
   - admit.
   - intros.
     destruct i as [U_form | El_form].
     + (* the universe formation rule *)
       simple refine (@Build_rule _ _ _ _ _ _).
       * { simple refine (@Build_algebraic_extension _ _ _ _ _ _ _).
           - simple refine [< >]. (* no equality premises *)
           - simple refine (@Build_well_founded_order _ _ _ _).
             + intros x y.
               refine (match (x, y) with (inl x', inl y') => _ | z => _ end).
               * cbn in x'.
                 exact True.
               * destruct z.
                 destruct f2.
               * destruct z.
                 destruct f1.
             + 


 f : 1+0 -> 1


pullback

         }
     + admit.
  Admitted.

  Theorem is_well_typed : is_well_typed_type_theory theory.
  Proof.
    admit.
  Admitted.

End MartinLoefTypeTheory.
