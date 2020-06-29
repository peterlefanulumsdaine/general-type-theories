Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Judgement.
Require Import Presented.AlgebraicExtension.
Require Import Presented.RawTypeTheory.
Require Import Presented.RawRule.
Require Import Presented.TypeTheory.

Section MartinLöfTypeTheory.
  Context {σ : shape_system}.

  Definition Σ : signature σ.
  Proof.
    refine [< _; _ >].
    - exact (class_type, [< >]). (* U *)
    - simple refine (class_type, [< (class_term, shape_empty σ) >]). (* El *)
  Defined.

  Local Definition U_formation_rule_index
    : (form * arity σ)
  := (form_object class_type  (* Formation of a type *)
       , [< >]).                (* With no (object) premises *)

  Local Definition El_formation_rule_index : (form * arity σ)
    := (form_object class_type
       , [< (class_term, shape_empty σ) >]).

  (* Definition f : *)

  Local Definition theory : type_theory σ.
   simple refine (Build_type_theory _ _ _).
   1: simple refine (Build_raw_type_theory _ _ _).
   - exact ([< U_formation_rule_index ; El_formation_rule_index >]).
   - admit.
   - intros.
     destruct i as [ [] |  ].
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
             + admit.
             + admit.
           - admit.
           - admit.
         }
       * admit.

     + admit. (* the element formation rule *)
  Admitted. (* [MartinLofTypeTheory.theory] : much work to do *)

  Local Theorem is_well_typed : TypeTheory.is_well_typed theory.
  Proof.
    admit.
  Admitted.  (* [MartinLofTypeTheory.is_well_typed] : much work to do *)

End MartinLöfTypeTheory.
