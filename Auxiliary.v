
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


