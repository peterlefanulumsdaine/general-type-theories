Require Import HoTT.

(** A family in [X] is given by an index type and the map taking indices to elements in [X]. *)
Record family (X : Type) :=
  { family_index :> Type
  ; family_element :> family_index -> X
  }.

Global Arguments family_index [_] F : rename.
Global Arguments family_element [_] F _ : rename.

(* Lemma for equalities of families (requiring funext).
   TODO: consider naming conventions for such lemmas. *)
Local Definition eq `{Funext} {X} {c c' : family X}
    (e : family_index c = family_index c')
    (e' : forall i:c, c i = c' (equiv_path _ _ e i) )
  : c = c'.
Proof.
  destruct c, c'; cbn in *.
  destruct e. apply ap.
  apply path_forall; intros i; apply e'.
Defined.

(** The empty family. *)
Local Definition empty (X : Type) : family X.
Proof.
  exists Overture.Empty.
  intros [].
Defined.

Local Definition sum {X} (Y1 Y2 : family X) : family X
  := {| family_index := Y1 + Y2
      ; family_element y := match y with inl y => Y1 y | inr y => Y2 y end |}.

Local Definition fmap {X Y} (f : X -> Y) (K : family X) : family Y.
Proof.
  exists K.
  exact (fun i => f (K i)).
Defined.

Local Definition singleton {X} (x:X) : family X.
Proof.
  exists Overture.Unit.
  intros _; exact x.
Defined.

Local Definition adjoin {X} (K : family X) (x : X) : family X.
Proof.
  exists (option K).
  intros [i | ].
  - exact (K i).
  - exact x.
Defined.

Notation "Y1 + Y2" := (sum Y1 Y2) : family_scope.
Open Scope family_scope.
Notation " [< >] " := (empty _) (format "[< >]") : family_scope.
Notation " [< x >] " := (singleton x) : family_scope.
Notation " [< x ; y ; .. ; z >] " := (adjoin .. (adjoin (singleton x) y) .. z) : family_scope.

Delimit Scope family_scope with family.

(*Alternative: start with [singleton] instead of [empty], i.e.

  Notation " [ x ; y ; .. ; z ] " := (adjoin .. (adjoin (singleton x) y) .. z) : family_scope.

For by-hand case-by-case proofs on finite families, that might be a little nicer, avoiding a vacuous step.  TODO: see how these are used in practice; consider this choice. *)

(* Reindexing of a family along a map into the index type *)
Local Definition reindex {A} (K : family A) {X} (f : X -> K) : family A
  := {|
       family_index := X ;
       family_element := K o f
     |}.

(* The subfamily of a family determined by a predicate on the index type (which of course can make use of the values of the family) *)
Local Definition subfamily {A} (K : family A) (P : K -> Type) : family A
  := reindex K (pr1 : { i:K & P i } -> K).

(* The subfamily of a family determined by a predicate on the value type *)
Local Definition filter {A} (K : family A) (P : A -> Type) : family A
  := subfamily K (P o K).

(* The monadic *bind* operation for families. *)
Local Definition bind {A B}
  (K : family A) (f : A -> family B) : family B.
Proof.
  exists { i : K & f (K i) }.
  intros [i j].
  exact (f (K i) j).
Defined.

Section FamilyMap.

  Local Definition map {A} (K L : family A)
    := { f : family_index K -> family_index L & forall i : K, L (f i) = K i }.

  (* Re-grouping of [Build_map]: useful when the map and equality components for each input are most easily given together, e.g. if they involve an induction on the input. *)
  Definition Build_map' {A} (K L : family A)
      (f : forall i:K, { j:L & L j = K i })
    : map K L.
  Proof.
    exists (fun i => pr1 (f i)).
    intros i. exact (pr2 (f i)).
  Defined.


  Local Definition map_index_action {A} {K L : family A}
    : map K L -> (K -> L)
  := pr1.
  Coercion map_index_action : map >-> Funclass.

  Local Definition map_commutes {A} {K L : family A}
    : forall f : map K L,
      forall i : K, L (f i) = K i
  := pr2.

  Local Definition idmap {X} (K : family X)
    : map K K.
  Proof.
    econstructor.
    intro; constructor.
  Defined.

  Local Definition map_sum {X}
      {K K' : family X} (f : map K K')
      {L L' : family X} (g : map L L')
    : map (sum K L) (sum K' L').
  Proof.
    simple refine (_;_).
    - intros [ i | j ].
      + apply inl, f, i.
      + apply inr, g, j.
    - intros [ i | j ];
      simpl; apply map_commutes.
  Defined.

  Local Definition map_inl {X} {K K' : family X}
    : map K (K + K').
  Proof.
    exists inl.
    intro; apply idpath.
  Defined.

  Local Definition map_inr {X} {K K' : family X}
    : map K' (K + K').
  Proof.
    exists inr.
    intro; apply idpath.
  Defined.

  Local Definition map_fmap
      {X Y} (f : X -> Y)
      {K K' : family X} (g : map K K')
    : map (fmap f K) (fmap f K').
  Proof.
    exists g.
    intros i. cbn. apply ap. apply map_commutes.
  Defined.

  Local Definition inclusion
      {A : Type} (K : family A) (P : K -> Type)
    : map (subfamily K P) K.
  Proof.
    exists pr1.
    intros; apply idpath.
  Defined.

  Local Lemma map_adjoin `{Funext}
      {X Y} (f : X -> Y)
      (K : family X) (x : X)
    : fmap f (adjoin K x) = adjoin (fmap f K) (f x).
  Proof.
    simple refine (eq _ _).
    - apply idpath.
    - intros [? | ]; apply idpath.
  Defined.

End FamilyMap.
