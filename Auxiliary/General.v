(** General-purpose auxiliary material for the development. *)

Require Import HoTT.

(** Flip arguments of a binary function, as in Haskell. *)
Definition flip {X Y Z : Type}
  : (X -> Y -> Z) -> Y -> X -> Z
:= fun f y x => f x y.

Definition ap2 {X Y Z} (f : X -> Y -> Z)
    {x x'} (e_x : x = x') {y y'} (e_y : y = y')
  : f x y = f x' y'.
Proof.
  exact (ap _ e_y @ ap (fun x => f x _) e_x).
Defined.
