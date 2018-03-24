Require Import HoTT.

(** A slightly idiosyncratic approach to binary coproducts, coproduct with unit, and empty types. *)

Section EmptyType.

  (* The fact that [X] is an empty type. *)
  Record is_empty (X : Type)
    :=
      { empty_rect : forall (P : X -> Type), forall x, P x }.

End EmptyType.

Section PlusOne.

(** The fact that [X1 = X + 1]. *)
Record is_plusone (X1 X : Type)
:=
  { plusone_one : X1
  ; plusone_inj : X -> X1
  ; plusone_rect
    : forall (P : X1 -> Type)
             (f_one : P plusone_one)
             (f_inj : forall x, P (plusone_inj x)),
      forall x, P x
  ; plusone_comp_one
    : forall (P : X1 -> Type)
             (f_one : P plusone_one)
             (f_inj : forall x, P (plusone_inj x)),
      plusone_rect P f_one f_inj plusone_one = f_one
  ; plusone_comp_inj
    : forall (P : X1 -> Type)
             (f_one : P plusone_one)
             (f_inj : forall x, P (plusone_inj x)),
      forall x, plusone_rect P f_one f_inj (plusone_inj x) = f_inj x
  }.

(* TODO: consider argument implicitnesses *)
(* Also: unnecessary size increase occurs, due to the large quantification in the recursor/computors.
  TODO: make the field itself an equivalent small type (e.g. “the map to the actual sum induced by inj1, inj2 is an equiv”) and then define the recursor as a lemma. *)
(* TODO: as with [is_coproduct], fix size issues. *)

End PlusOne.

Section BinaryCoproduct.

(** The fact that [X = X1 + X2]. *)
Record is_coproduct (X X1 X2 : Type)
:=
  { coproduct_inj1 : X1 -> X
  ; coproduct_inj2 : X2 -> X
  ; coproduct_rect
    : forall (P : X -> Type)
             (f1 : forall x1, P (coproduct_inj1 x1))
             (f2 : forall x2, P (coproduct_inj2 x2)),
      forall x, P x
  ; coproduct_comp_inj1
    : forall (P : X -> Type)
             (f1 : forall x1, P (coproduct_inj1 x1))
             (f2 : forall x2, P (coproduct_inj2 x2)),
      forall x1, coproduct_rect P f1 f2 (coproduct_inj1 x1) = f1 x1
  ; coproduct_comp_inj2
    : forall (P : X -> Type)
             (f1 : forall x1, P (coproduct_inj1 x1))
             (f2 : forall x2, P (coproduct_inj2 x2)),
      forall x2, coproduct_rect P f1 f2 (coproduct_inj2 x2) = f2 x2
  }.

Global Arguments coproduct_inj1 [_ _ _] _ _.
Global Arguments coproduct_inj2 [_ _ _] _ _.
Global Arguments coproduct_rect [_ _ _] _ _ _ _ _.
Global Arguments coproduct_comp_inj1 [_ _ _ _ _ _ _] _.
Global Arguments coproduct_comp_inj2 [_ _ _ _ _ _ _] _.

Local Definition assoc {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : X_YZ -> XY_Z.
  refine (coproduct_rect H_X_YZ _ _ _).
  - intro x.
    exact (coproduct_inj1 H_XY_Z (coproduct_inj1 H_XY x)).
  - refine (coproduct_rect H_YZ _ _ _).
    + intro y.
      exact (coproduct_inj1 H_XY_Z (coproduct_inj2 H_XY y)).
    + intro z.
      exact (coproduct_inj2 H_XY_Z z).
Defined.

Local Definition fmap {X Y XY X' Y' XY'}
           (H : is_coproduct XY X Y)
           (H' : is_coproduct XY' X' Y')
           (fX : X -> X') (fY : Y -> Y')
  : XY -> XY'.
Proof.
  eapply coproduct_rect.
  - exact H.
  - intro x. exact (coproduct_inj1 H' (fX x)).
  - intro y. exact (coproduct_inj2 H' (fY y)).
Defined.

Local Definition empty_right {X Y XY}
           (H_XY : is_coproduct XY X Y)
           (H_Y : is_empty Y)
  : XY -> X.
Proof.
  eapply coproduct_rect.
  exact H_XY.
  exact (fun x => x).
  apply H_Y.
Defined.

End BinaryCoproduct.

