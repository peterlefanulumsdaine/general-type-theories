Require HoTT.

(** A family in [X] is given by an index type and the map taking indices to elements in [X] *)
Record Family (X : Type) :=
  { fam_index :> Type
  ; fam_element :> fam_index -> X
  }.

Global Arguments fam_index [_] F : rename.
Global Arguments fam_element [_] F _ : rename.

(** The empty family. *)
Definition Empty (X : Type) : Family X.
Proof.
  exists Overture.Empty.
  intros [].
Defined.

Definition Sum {X} (Y1 Y2 : Family X) : Family X
  := {| fam_index := Y1 + Y2
      ; fam_element y := match y with inl y => Y1 y | inr y => Y2 y end |}.

Definition Fmap {X Y} (f : X -> Y) (K : Family X) : Family Y.
Proof.
  exists K.
  exact (fun i => f (K i)).
Defined.

Definition Singleton {X} (x:X) : Family X.
Proof.
  exists Overture.Unit.
  intros _; exact x.
Defined.

Definition Snoc {X} (K : Family X) (x : X) : Family X.
Proof.
  exists (option K).
  intros [i | ].
  - exact (K i).
  - exact x.
Defined.

Notation "Y1 + Y2" := (Sum Y1 Y2) : fam_scope.
Open Scope fam_scope.
Notation " [< >] " := (Empty _) (format "[< >]") : fam_scope.
Notation " [< x >] " := (Singleton x) : fam_scope.
Notation " [< x ; .. ; z >] " := (Snoc .. (Snoc (Empty _) x) .. z) : fam_scope.

(*Alternative: start with [Singleton] instead of [Empty], i.e.

  Notation " [ x ; y ; .. ; z ] " := (Snoc .. (Snoc (Singleton x) y) .. z) : fam_scope.

For by-hand case-by-case proofs on finite families, that might be a little nicer, avoiding a vacuous step.  TODO: see how these are used in practice; consider this choice. *)
