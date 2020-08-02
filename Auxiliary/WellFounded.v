Require Import HoTT.

Open Scope type_scope.
(* NOTE: The reason for this “Open Scope” is that when the HoTT library is imported, [mc_scope] overrides use of notations such as [A + B] for types, or at least, make them require explicit scope annotations.  If there’s a better way to make such notations easily usable (besides this or closing [mc_scope]), we should ue that here instead. *)

Definition is_well_founded {X : Type} (R : Relation X)
  := forall P : X -> Type,
     (forall x : X, (forall y : X, R y x -> P y) -> P x)
     -> (forall x : X, P x).

Record well_founded_order {X : Type}
:= { well_founded_order_lt :> Relation X
   ; well_founded : is_well_founded well_founded_order_lt
   ; transitive : Transitive well_founded_order_lt (* TODO: rename this *)
 }.

Arguments well_founded_order : clear implicits.

Identity Coercion id_relation : Relation >-> Funclass.
(* Required in order to apply [well_founded_order] (or other things coercing to [relation]) to arguments *)

(* An order is well-founded if it embeds into a known well-founded order. *)
Definition well_founded_if_embeds {X Y} (f : X -> Y)
    {RX : Relation X} {RY : Relation Y} (RY_wf : is_well_founded RY)
    (H_f : forall x x', RX x x' -> RY (f x) (f x'))
  : is_well_founded RX.
Proof.
  intros P P_hereditary.
  set (Q := fun y:Y => forall x:X, (f x = y) -> P x).
  assert (H_Q : forall y, Q y).
  { apply RY_wf.
    intros y Q_below_y x e_fx_y.
    destruct e_fx_y. rename Q_below_y into Q_below_fx.
    apply P_hereditary.
    intros x' lt_x'_x.
    simple refine (Q_below_fx (f x') _ _ _).
    + apply H_f; assumption.
    + apply idpath.
  }
  intros x. refine (H_Q (f x) x _). apply idpath.
Defined.

Local Definition pullback {X Y} (f : X -> Y)
  : well_founded_order Y -> well_founded_order X.
Proof.
  intros lt.
  exists (fun x x' => lt (f x) (f x')).
  - apply (well_founded_if_embeds f (well_founded lt)). intros; assumption.
  - intros x x' x'' lt_x_x' lt_x'_x''.
    apply (transitive lt _ (f x')); assumption.
Defined.

Local Definition family_sum
  {X : Type} (lt_X : well_founded_order X)
  {Y : X -> Type} (lt_Y : forall x, well_founded_order (Y x))
  : well_founded_order {x:X & Y x}.
Proof.
  simple refine (Build_well_founded_order _ _ _ _).
  - intros xy xy'.
    refine (lt_X xy.1 xy'.1
            + { e : xy.1 = xy'.1 & lt_Y _ (transport Y e xy.2) xy'.2}).
  - intros P P_hereditary.
    set (PX := fun x => forall y, P (x;y)).
    assert (PX_total : forall x, PX x).
    { apply (well_founded lt_X).
      intros x PX_below_x.
      unfold PX. apply (well_founded (lt_Y x)).
      intros y Px_below_y.
      apply (P_hereditary (x;y)).
      intros [x' y'] [ lt_x_x' | [e lt_y_y'] ].
      + apply PX_below_x, lt_x_x'.
      + simpl in *. destruct e. apply Px_below_y, lt_y_y'.
    }
    intros [x y]; apply PX_total.
  - intros [x y] [x' y'] [x'' y'']
           [ lt_x_x' | e_lt_y_y' ] [ lt_x'_x'' | e_lt_y'_y''].
    + apply inl. apply (transitive lt_X _ x'); assumption.
    + apply inl. destruct (e_lt_y'_y''.1). assumption.
    + apply inl. destruct (e_lt_y_y'.1). assumption.
    + apply inr. cbn in *.
      destruct e_lt_y_y' as [ e lt_y_y']; destruct e.
      destruct e_lt_y'_y'' as [ e' lt_y'_y'']; destruct e'.
      cbn in *. exists (idpath _).
      apply (transitive (lt_Y x) _ y'); assumption.
Defined.

(* If [f : X -> Y] from a well-ordered [X] to a [Y] with a relation reflects
   order then a predicate of the form [P o f] is hereditary. *)
Lemma push_along_embedding
    {X} (lt_X : well_founded_order X)
    {Y} (lt_Y : Relation Y) (f : X -> Y)
    (P : Y -> Type)
  : (forall x x', lt_Y (f x) (f x') -> lt_X x x')
  -> (forall x : X, (forall x', lt_Y (f x') (f x) -> P (f x')) -> P (f x))
  -> (forall x : X, P (f x)).
Proof.
  intro f_embeds.
  intros p x.
  apply (well_founded lt_X (fun x => P (f x))).
  intros y H.
  apply p.
  intros ? ?.
  apply H.
  now apply f_embeds.
Defined.

Local Definition sum {X Y} :
  well_founded_order X -> well_founded_order Y -> well_founded_order (X + Y).
Proof.
  intros lt_X lt_Y.
  pose (lt := fun (u v : X + Y) =>
                match u, v with
                | inl x, inl x' => lt_X x x'
                | inr y, inr y' => lt_Y y y'
                | _, _ => False
                end).
  exists lt.
  - intros P f [x | y].
    + apply (push_along_embedding lt_X lt inl P) ; auto.
      intros ? H.
      apply f.
      intros [? | ?]; [intros ? | intros []].
      now apply H.
    + apply (push_along_embedding lt_Y lt inr P) ; auto.
      intros ? H.
      apply f.
      intros [? | ?]; [intros [] | intros ?].
      now apply H.
  - intros [x1|y1] [x2|y2] [x3|y3] H1 H2;
      try (now destruct H1 || now destruct H2).
    + now apply (transitive _ _ x2).
    + now apply (transitive _ _ y2).
Defined.

Local Definition empty : well_founded_order Empty.
Proof.
  refine {| well_founded_order_lt := (fun _ _ => True) |}.
  - intros _ _ [].
  - intros [].
Defined.

(** Well-founded order on an option type where [None] is the last element. *)
Local Definition linear_option {X} (lt_X : well_founded_order X)
  : well_founded_order (option X).
Proof.
  pose (lt := fun (x y : option X) =>
                       match x, y with
                       | None, _ => False
                       | Some _, None  => True
                       | Some u, Some v => lt_X u v
                       end).
  simple refine {| well_founded_order_lt := lt |}.
  - intros P f [x|].
    + apply (well_founded lt_X (fun z => P (Some z))).
      intros ? H.
      apply f.
      intros [? | ]; [ intros ? | intros []].
      now apply H.
    + apply f.
      intros [? | ]; [ intros ? | intros []].
      apply (well_founded lt_X (fun z => P (Some z))).
      intros ? H.
      apply f.
      intros [? | ]; [ intros ? | intros []].
      now apply H.
  - intros [x|] [y|] [z|] lt_x_y lt_y_z ; try now destruct lt_x_y.
    + now apply (transitive lt_X _ y).
    + constructor.
Defined.

(** Well-founded order on an option type where [None] is incomparable to [Some _]. *)
Local Definition raw_option {X} {lt_X : well_founded_order X}
  : well_founded_order (option X).
Proof.
  pose (lt := fun (x y : option X) =>
                match x, y with
                | None, _ => False
                | _, None => False
                | Some u, Some v => lt_X u v
                end).
  simple refine {| well_founded_order_lt := lt |}.
  - intros P f [x|].
    + apply (well_founded lt_X (fun z => P (Some z))).
      intros ? H.
      apply f.
      intros [? | ]; [ intros ? | intros []].
      now apply H.
    + apply f.
      intros [y|] [].
  - intros [x|] [y|] [z|] lt_x_y lt_y_z ; try now destruct lt_x_y.
    + now apply (transitive lt_X _ y).
    + destruct lt_y_z.
Defined.

(** A tactic that genereates a well-order on the type [option (option (.... empty))]. *)
Ltac use_linear_order :=
  match goal with
  | |- well_founded_order Empty => exact empty
  | |- well_founded_order (option ?T) => apply linear_option ; use_linear_order
  | _ => fail
  end.

(** A tactic that genereates a raw well-order on a combination of +, option and Empty. *)
Ltac use_flat_order :=
  match goal with
  | |- well_founded_order Empty => exact empty
  | |- well_founded_order (option _) => apply linear_option ; use_flat_order
  | |- well_founded_order (Datatypes.sum _ _) => apply sum ; use_flat_order
  | _ => fail
  end.

Local Definition lex_product {X Y}
    (lt_X : well_founded_order X) (lt_Y : well_founded_order Y)
  : well_founded_order (X*Y).
Proof.
  refine (pullback _ (family_sum lt_X (fun x => lt_Y))).
  intros xy. exact (fst xy; snd xy).
Defined.

(* TODO: find better name; see https://mathoverflow.net/questions/296349/ *)
Definition semi_reflexive_product
           {X Y} (lt_X : well_founded_order X) (lt_Y : well_founded_order Y)
  : well_founded_order (X*Y).
Proof.
  exists (fun xy xy' => ((lt_X (fst xy) (fst xy') * lt_Y (snd xy) (snd xy'))
                         + ((fst xy = fst xy') * lt_Y (snd xy) (snd xy'))
                         + (lt_X (fst xy) (fst xy') * (snd xy = snd xy')))).
  - apply (well_founded_if_embeds idmap (well_founded (lex_product lt_X lt_Y))).
    intros [x y] [x' y'] [[[lx ly] | [e ly]] | [lx e]].
    + apply inl; assumption.
    + apply inr. exists e. destruct e; exact ly.
    + apply inl; assumption.
  - intros [x y] [x' y'] [x'' y'']
      [[[l_x_x' l_y_y'] | [e_x_x' l_y_y']] | [l_x_x' e_y_y']]
      [[[l_x'_x'' l_y'_y''] | [e_x'_x'' l_y'_y'']] | [l_x'_x'' e_y'_y'']];
    cbn in *.
    + apply inl, inl. split.
      * eapply transitive; eassumption.
      * eapply transitive; eassumption.
    + apply inl, inl. split.
      * destruct e_x'_x''; assumption.
      * eapply transitive; eassumption.
    + apply inl, inl. split.
      * eapply transitive; eassumption.
      * destruct e_y'_y''; assumption.
    + apply inl, inl. split.
      * destruct e_x_x'; assumption.
      * eapply transitive; eassumption.
    + apply inl, inr. split.
      * destruct e_x_x'; assumption.
      * eapply transitive; eassumption.
    + apply inl, inl. split.
      * destruct e_x_x'; assumption.
      * destruct e_y'_y''; assumption.
    + apply inl, inl. split.
      * eapply transitive; eassumption.
      * destruct e_y_y'; assumption.
    + apply inl, inl. split.
      * destruct e_x'_x''; assumption.
      * destruct e_y_y'; assumption.
    + apply inr. split.
      * eapply transitive; eassumption.
      * destruct e_y_y'; assumption.
Defined.
