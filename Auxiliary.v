
Open Scope type_scope.
Open Scope list_scope.

Inductive Empty : Type := .

Definition ap {A B} (f : A -> B) {a a' : A} (p : a = a')
  : f a = f a'
:= match p with eq_refl _ => eq_refl _ end.
  
Definition transport {A} {B : A -> Type} {a a' : A} (p : a = a')
  : B a -> B a'
:= fun b => match p with eq_refl _ => b end.
  
Fixpoint entries {A} (l : list A)
  := match l with nil => Empty_set | (a :: l') => unit + entries l' end.

Fixpoint lookup {A} (l : list A) : entries l -> A
  := match l with
     | nil => fun i => match i with end
     | (a :: l') => fun i => 
           match i with inl _ => a | inr i' => lookup l' i' end
     end.

Fixpoint fmap_list {A B} (f : A -> B) (l : list A) : list B
  := match l with nil => nil | (a :: l') => (f a) :: (fmap_list f l') end.

Fixpoint replicate {A:Type} (n:nat) (a:A) : list A
  := match n with O => nil | S n' => a :: (replicate n' a) end.

(* Heterogeneous vector types, for saying things like “a list A_1, …, A_n, where each A_i is a type over the context so far”. *)
Inductive Het_Vec {X} {A : X -> Type} (x0:X) (f : forall x, A x -> X)
  : X -> Type
:= nil_HV : Het_Vec x0 f x0 | cons_HV {x} (a:A x) : Het_Vec x0 f (f x a).


Section Families.

Record Family (X : Type) := { Inds :> Type ; val : Inds -> X }.

Global Arguments Inds [_] F : rename.
Global Arguments val [_] F _ : rename.
Coercion val : Family >-> Funclass.

Definition Sum_Family {X} (Y1 Y2 : Family X) : Family X
  := {| Inds := Y1 + Y2
      ; val y := match y with inl y => Y1 y | inr y => Y2 y end |}.

Notation "Y1 + Y2" := (Sum_Family Y1 Y2) : fam_scope.
Delimit Scope fam_scope with fam.
Bind Scope fam_scope with Family.

(* TODO: fmap of families *)
End Families.

(* Redeclare notations globally *)
Notation "Y1 + Y2" := (Sum_Family Y1 Y2) : fam_scope.

(* A sligtly idiosyncratic approach to coproducts of types, used for systems of proto-contexts. *)
Section Coprods.

Record is_coprod (X X1 X2 : Type)
:=
  { inj1 : X1 -> X
  ; inj2 : X2 -> X
  ; coprod_rect
    : forall (P : X -> Type)
             (f1 : forall x1, P (inj1 x1))
             (f2 : forall x2, P (inj2 x2)),
      forall x, P x
  ; coprod_comp1
    : forall (P : X -> Type)
             (f1 : forall x1, P (inj1 x1))
             (f2 : forall x2, P (inj2 x2)),
      forall x1, coprod_rect P f1 f2 (inj1 x1) = f1 x1
  ; coprod_comp2
    : forall (P : X -> Type)
             (f1 : forall x1, P (inj1 x1))
             (f2 : forall x2, P (inj2 x2)),
      forall x2, coprod_rect P f1 f2 (inj2 x2) = f2 x2
  }.

(* TODO: consider naming conventions here! *)
(* TODO: consider argument plicitnesses *)
(* Also: unnecessary size increase occurs, due to the large quantification in the recursor/computors.
  TODO: make the field itself an equivalent small type (e.g. “the map to the actual sum induced by inj1, inj2 is an equiv”) and then define the recursor as a lemma. *)

Record is_plusone (X X0 : Type)
:=
  { plusone_top : X
  ; plusone_next : X0 -> X
  ; plusone_rect
    : forall (P : X -> Type)
             (f_top : P plusone_top)
             (f_next : forall x, P (plusone_next x)),
      forall x, P x
  ; plusone_comp_top
    : forall (P : X -> Type)
             (f_top : P plusone_top)
             (f_next : forall x, P (plusone_next x)),
      plusone_rect P f_top f_next plusone_top = f_top
  ; plusone_comp_next
    : forall (P : X -> Type)
             (f_top : P plusone_top)
             (f_next : forall x, P (plusone_next x)),
      forall x, plusone_rect P f_top f_next (plusone_next x) = f_next x
  }.

(* TODO: consider argument plicitnesses *)
(* TODO: as with [is_coprod], fix size issues. *)

End Coprods.

