Require Import HoTT.HoTT.

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
(* Also: unnecessary size increase occurs, due to the large quantification in the recursor/computors. TODO: make the field itself an equivalent small type (e.g. “the map to the actual sum induced by inj1, inj2 is an equiv”) and then define the recursor as a lemma. *)
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

Local Definition assoc_rtol {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : X_YZ -> XY_Z.
Proof.
  refine (coproduct_rect H_X_YZ _ _ _).
  - intro x.
    exact (coproduct_inj1 H_XY_Z (coproduct_inj1 H_XY x)).
  - refine (coproduct_rect H_YZ _ _ _).
    + intro y.
      exact (coproduct_inj1 H_XY_Z (coproduct_inj2 H_XY y)).
    + intro z.
      exact (coproduct_inj2 H_XY_Z z).
Defined.

Local Definition assoc_ltor {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : XY_Z -> X_YZ.
Proof.
  refine (coproduct_rect H_XY_Z _ _ _).
  - refine (coproduct_rect H_XY _ _ _).
    + intro x.
      exact (coproduct_inj1 H_X_YZ x).
    + intro y.
      exact (coproduct_inj2 H_X_YZ (coproduct_inj1 H_YZ y)).
  - intro z.
    exact (coproduct_inj2 H_X_YZ (coproduct_inj2 H_YZ z)).
Defined.

Local Definition assoc_ltortol {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : forall w : XY_Z,
    assoc_rtol H_XY H_XY_Z H_YZ H_X_YZ
      (assoc_ltor H_XY H_XY_Z H_YZ H_X_YZ
        w)
    = w.
Proof.
  apply (coproduct_rect H_XY_Z);
    [ apply (coproduct_rect H_XY) | ];
    intros;
    unfold assoc_rtol, assoc_ltor;
    repeat progress rewrite ? coproduct_comp_inj2, ? coproduct_comp_inj1;
    apply idpath.
Defined.

Local Definition assoc_rtoltor {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : forall w : X_YZ,
    assoc_ltor H_XY H_XY_Z H_YZ H_X_YZ
      (assoc_rtol H_XY H_XY_Z H_YZ H_X_YZ
        w)
    = w.
Proof.
  apply (coproduct_rect H_X_YZ);
    [ | apply (coproduct_rect H_YZ) ];
    intros;
    unfold assoc_rtol, assoc_ltor;
    repeat progress rewrite ? coproduct_comp_inj2, ? coproduct_comp_inj1;
    try apply idpath.
Defined.

Local Definition assoc_equiv {X Y Z XY YZ XY_Z X_YZ}
           (H_XY : is_coproduct XY X Y)
           (H_XY_Z : is_coproduct XY_Z XY Z)
           (H_YZ : is_coproduct YZ Y Z)
           (H_X_YZ : is_coproduct X_YZ X YZ)
  : XY_Z <~> X_YZ.
Proof.
  apply (equiv_adjointify
           (assoc_ltor H_XY H_XY_Z H_YZ H_X_YZ)
           (assoc_rtol H_XY H_XY_Z H_YZ H_X_YZ)).
  - intro; apply assoc_rtoltor.
  - intro; apply assoc_ltortol.
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
  - exact H_XY.
  - exact (fun x => x).
  - apply H_Y.
Defined.

Definition coproduct_empty_inj1_is_equiv
    {X E XE} (H_XE : is_coproduct XE X E) (H_E : is_empty E)
  : IsEquiv (coproduct_inj1 H_XE).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply (coproduct_rect H_XE).
    + intros i; exact i.
    + apply (empty_rect _ H_E).
  - unfold pointwise_paths; apply (coproduct_rect H_XE).
    + intros i. apply ap.
      refine (coproduct_comp_inj1 _).
    + apply (empty_rect _ H_E).
  - intros i. refine (coproduct_comp_inj1 _).
Defined.

Definition coproduct_empty_inj2_is_equiv
    {E Y EY} (H_EY : is_coproduct EY E Y) (H_E : is_empty E)
  : IsEquiv (coproduct_inj2 H_EY).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply (coproduct_rect H_EY).
    + apply (empty_rect _ H_E).
    + intros i; exact i.
  - unfold pointwise_paths; apply (coproduct_rect H_EY).
    + apply (empty_rect _ H_E).
    + intros i. apply ap.
      refine (coproduct_comp_inj2 _).
  - intros i. refine (coproduct_comp_inj2 _).
Defined.

End BinaryCoproduct.

