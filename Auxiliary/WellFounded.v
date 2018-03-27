Require Import HoTT.

Definition is_well_founded {X : Type} (R : relation X)
  := forall P : X -> Type,
     (forall x : X, (forall y : X, R y x -> P y) -> P x)
     -> (forall x : X, P x).

Record well_founded_order {X : Type}
:= { well_founded_order_lt :> relation X
   ; well_founded : is_well_founded well_founded_order_lt
   ; transitive : Transitive well_founded_order_lt
 }.

Arguments well_founded_order _ : clear implicits.

Identity Coercion id_relation : relation >-> Funclass.
(* Required in order to apply [well_founded_order] (or other things coercing to [relation]) to arguments *)

Local Definition pullback {X Y} (f : X -> Y)
  : well_founded_order Y -> well_founded_order X.
Proof.
  intros lt.
  exists (fun x x' => lt (f x) (f x')).
  - intros P P_hereditary.
    set (Q := fun y:Y => forall x:X, (f x = y) -> P x).
    assert (H_Q : forall y, Q y).
    { apply (well_founded lt).
      intros y Q_below_y x e_fx_y.
      destruct e_fx_y. rename Q_below_y into Q_below_fx.
      apply P_hereditary.
      intros x' lt_x'_x.
      simple refine (Q_below_fx (f x') _ _ _).
      + assumption.
      + apply idpath.
    }
    intros x. refine (H_Q (f x) x _). apply idpath.
  - intros x x' x'' lt_x_x' lt_x'_x''.
    apply (transitive lt _ (f x')); assumption.
Defined.
