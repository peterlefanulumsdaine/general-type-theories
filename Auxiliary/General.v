(** General-purpose auxiliary material for the development. *)

Require Import HoTT.

(** Flip arguments of a binary function, as in Haskell. *)
Definition flip {X Y Z : Type}
  : (X -> Y -> Z) -> Y -> X -> Z
:= fun f y x => f x y.

(** [ap_1back], etc: versions of [ap] that act on an earlier-than-last argument of a multi-argument function (but always an argument on which nothing later depends).  *)
(* NOTE: unfortunately, invocation as [apply ap_1back] doesn’t seem to work in the common situation where the output type [Z] doesn’t depend on all the intervening arguments.  Instead, use [rapply @ap_1back] or similar. *)
Definition ap_1back {X Y} {Z} (f : forall (x:X) (y:Y), Z y)
    {x x'} (e : x = x') y
  : f x y = f x' y.
Proof.
  exact (ap (fun x => f x y) e).
Defined.

Definition ap_2back {X Y1} {Y2} {Z}
   (f : X -> forall (y1:Y1) (y2 : Y2 y1), Z y1 y2)
   {x x'} (e : x = x') y1 y2
  : f x y1 y2 = f x' y1 y2.
Proof.
  exact (ap (fun x => f x y1 y2) e).
Defined.

Definition ap_3back {X Y1} {Y2} {Y3} {Z}
   (f : X -> forall (y1:Y1) (y2 : Y2 y1) (y3 : Y3 y1 y2), Z y1 y2 y3)
   {x x'} (e : x = x') y1 y2 y3
  : f x y1 y2 y3 = f x' y1 y2 y3.
Proof.
  exact (ap (fun x => f x y1 y2 y3) e).
Defined.

Definition ap2 {X Y Z} (f : X -> Y -> Z)
    {x x'} (e_x : x = x') {y y'} (e_y : y = y')
  : f x y = f x' y'.
Proof.
  eapply concat.
  - apply ap, e_y.
  - try apply ap_1back.
(* At time of writing, [apply ap_1back] fails here; I don’t understand why.

If the build ever breaks here, that’s good news: it presumably means [apply ap_1back] now works here, and so hopefully we can replace it not only here but everywhere in the development where we currently use slightly more verbose invocations of [ap_1back], [ap_2back], etc. *)
    rapply @ap_1back. apply e_x.
Defined.

(* This lemma could profitaly be factored as a general principle about equivalences:
given [e:X<~>Y], to prove [forall y, P y], it suffices to prove [forall x, P (e x)]. *)
Lemma inverse_sufficient {X} {x y:X} (P : x = y -> Type)
  : (forall e, P (e^)) -> (forall e, P e).
Proof.
  intros H e.
  eapply transport.
  - eapply inv_V.
  - apply H.
Defined.
