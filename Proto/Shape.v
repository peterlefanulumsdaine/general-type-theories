Require Import Auxiliary.Coproduct.

(* A _Shape_ abstract the kind of shapes that contexts and bindings can have.

  There are several motivations for this:

  - firstly, it allows the same code to simultaneously cover both syntax with de Bruijn
    indices and syntax with named variables — those will be two examples of shape systems.

  - secondly, it abstracts just the properties of both those settings that are really
    needed in the definition of substitution etc., hence giving a clean and robust
    interface.

  - thirdly, it is written with an eye towards possible later generalisation to infinitary
    settings, where genuinely different shape systems might occur.
*)

(** A record describing shapes that can be used for contexts and bindings. *)
Record shape :=
  { shape_carrier :> Type
  ; shape_position : shape_carrier -> Type (* each shape has some positions, maybe should map to sets *)
  ; shape_empty : shape_carrier (* the empty *)
  ; shape_is_empty : is_empty (shape_position shape_empty) (* the empty shape binds nothing *)
  ; shape_sum : shape_carrier -> shape_carrier -> shape_carrier (* the sum of two shapes *)
  ; shape_is_sum (* the positions in the sum are the sum of positions *)
     : forall γ δ : shape_carrier,
       Coproduct.is_coproduct (shape_position (shape_sum γ δ)) (shape_position γ) (shape_position δ)
  ; shape_extend : shape_carrier -> shape_carrier (* a shape extended by one more more position *)
  ; shape_is_extend
     : forall γ : shape_carrier,
       Coproduct.is_plusone (shape_position (shape_extend γ)) (shape_position γ)
  }.

Global Arguments shape_sum {_} _ _.
Global Arguments shape_is_sum {_} [_ _].
Global Arguments shape_is_empty {_}.

Coercion shape_position : shape_carrier >-> Sortclass.
