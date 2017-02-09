(* Open Scope type_scope. *)
(* Open Scope list_scope. *)

(* Fixpoint entries {A} (l : list A) *)
(*   := match l with nil => Empty | (a :: l') => Unit + entries l' end. *)

(* Fixpoint lookup {A} (l : list A) : entries l -> A *)
(*   := match l with *)
(*      | nil => fun i => match i with end *)
(*      | (a :: l') => fun i => *)
(*            match i with inl _ => a | inr i' => lookup l' i' end *)
(*      end. *)

(* Fixpoint fmap_list {A B} (f : A -> B) (l : list A) : list B *)
(*   := match l with nil => nil | (a :: l') => (f a) :: (fmap_list f l') end. *)

(* Fixpoint replicate {A:Type} (n:nat) (a:A) : list A *)
(*   := match n with O => nil | S n' => a :: (replicate n' a) end. *)

(* (* Heterogeneous vector types, for saying things like “a list A_1, …, A_n, where each A_i is a type over the context so far”. *) *)
(* Inductive Het_Vec {X} {A : X -> Type} (x0:X) (f : forall x, A x -> X) *)
(*   : X -> Type *)
(* := nil_HV : Het_Vec x0 f x0 | cons_HV {x} (a:A x) : Het_Vec x0 f (f x a). *)
