Require Import Auxiliary.Coproduct.

(* _Shape Systems_ abstract the kind of shapes that contexts can have.

  There are several motivations for this:

  - firstly, it allows the same code to simultaneously cover both syntax with de Bruijn indices and syntax with named variables — those will be two examples of shape systems.
  - secondly, it abstracts just the properties of both those settings that are really needed in the definition of substitution etc., hence giving a clean and robust interface.
  - thirdly, it is written with an eye towards possible later generalisation to infinitary settings, where genuinely different shape systems might occur.
*)

Section Shape_Systems.

(* TODO: possibly rename as “context shapes”, “shape systems”, …?  *)
Record Shape_System :=
  { Shape :> Type
  ; positions : Shape -> Type (* maybe should be to sets?? *)
  ; shape_empty : Shape
  ; shape_is_empty : is_empty (positions shape_empty)
  ; shape_coproduct : Shape -> Shape -> Shape
  ; shape_is_coproduct
     : forall γ δ : Shape,
       is_coproduct (positions (shape_coproduct γ δ)) (positions γ) (positions δ)
  ; shape_extend : Shape -> Shape
  ; shape_is_plusone         (* TODO: change to is_extend (Andrej?) *)
     : forall γ : Shape,
       is_plusone (positions (shape_extend γ)) (positions γ)
  }.

Global Arguments shape_coproduct {_} _ _.
Global Arguments shape_is_coproduct {_} [_ _].
Global Arguments shape_is_empty {_}.

Coercion positions : Shape >-> Sortclass.

End Shape_Systems.

