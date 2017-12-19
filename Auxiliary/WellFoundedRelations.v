Require Import HoTT.

Definition Well_founded {X : Type} (R : relation X)
  := forall P : X -> Type,
     (forall x:X, (forall y:X, R y x -> P y) -> P x)
     -> (forall x:X, P x).


