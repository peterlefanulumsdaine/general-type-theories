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

Definition ap_4back {X Y1} {Y2} {Y3} {Y4} {Z}
   (f : X ->
     forall (y1:Y1)
            (y2 : Y2 y1)
            (y3 : Y3 y1 y2)
            (y4 : Y4 y1 y2 y3),
       Z y1 y2 y3 y4)
   {x x'} (e : x = x') y1 y2 y3 y4
  : f x y1 y2 y3 y4 = f x' y1 y2 y3 y4.
Proof.
  exact (ap (fun x => f x y1 y2 y3 y4) e).
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

Definition ap3 {X1 X2 X3 Y} (f : X1 -> X2 -> X3 -> Y)
    {x1 x1'} (e1 : x1 = x1')
    {x2 x2'} (e2 : x2 = x2')
    {x3 x3'} (e3 : x3 = x3')
  : f x1 x2 x3 = f x1' x2' x3'.
Proof.
  destruct e1, e2, e3; apply idpath.
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

Lemma some_ne_none {A} {a:A} : Some a <> None.
Proof.
  intros e.
  apply true_ne_false.
  exact (ap (fun x : option A => if x then true else false) e).
Defined.

Definition sigma_type_eq `{Funext}
    {A} {B B'} (e : forall x, B x = B' x)
  : { x:A & B x } = {x:A & B' x}.
Proof.
  apply path_forall in e.
  apply ap, e.
Defined.

Definition equiv_path_sigma_type_eq `{Funext}
   {A} {B B'} (e : forall x, B x = B' x)
   (xy : { x:A & B x })
  : equiv_path _ _ (sigma_type_eq e) xy
    = (xy.1; equiv_path _ _ (e xy.1) xy.2).
Proof.
  unfold sigma_type_eq.
  set (e' := path_forall _ _ e).
  simple refine (_ @ _).
  exact (xy.1; equiv_path _ _ (ap10 e' xy.1) xy.2).
  - destruct e'; apply idpath.
  - apply ap, ap10, ap, ap.
    apply ap10_path_forall.
Defined.

(** Some useful infrastructure for the [option] type. *)
Section Option.

  Definition fmap_option {A B} (f : A -> B) : option A -> option B
  := fun a => match a with
    | Some a => Some (f a)
    | None => None
  end.

End Option.