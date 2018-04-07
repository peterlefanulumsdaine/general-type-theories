(** General-purpose auxiliary material for the development. *)

Require Import HoTT.

(** Flip arguments of a binary function, as in Haskell. *)
Definition flip {X Y Z : Type}
  : (X -> Y -> Z) -> Y -> X -> Z
:= fun f y x => f x y.

