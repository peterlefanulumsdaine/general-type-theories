Require Import HoTT.

(** Library for _families_. 

This is the traditional sense of e.g. “a family of rings {R_i}_(i \in I)”: that is, a family of widgets consists of an index type I, together with a map from I to the type of widgets.  These can also be seen as _multisets_, or _multi-valued elements_ of a type.  

In many contexts, they are a good constructive alternative where classically one might use a _set_ of widgets; so the vocabulary and notation we use reflects that.

Here we provide:

- families, and maps of families (over maps of their value types), forming (roughly) a displayed category;
- basic constructions on families: empty families, sums, singleton families, etc;
- notations for all the above; in partiular, a list-like notation for finite families, e.g. [ [< 1, 5, 5, 3 >] : family nat ].
*)

 
(** A family in [X] is given by an index type and the map taking indices to elements in [X]. *)
Record family (X : Type) :=
  { family_index :> Type
  ; family_element :> family_index -> X
  }.

Global Arguments family_index [_] F : rename.
Global Arguments family_element [_] F _ : rename.

Delimit Scope family_scope with family.
Open Scope family_scope.

(** Lemma for equalities of families (assuming funext). *)
(* TODO: consider naming conventions for such lemmas. *)
Local Definition eq `{Funext} {X} {c c' : family X}
    (e : family_index c = family_index c')
    (e' : forall i:c, c i = c' (equiv_path _ _ e i) )
  : c = c'.
Proof.
  destruct c, c'; cbn in *.
  destruct e. apply ap.
  apply path_forall; intros i; apply e'.
Defined.

(** The category of families:

One can consider maps between families _over_ (or _modulo_) maps between the types they’re from, in the sense of a _displayed category_ (arXiv:1705.04296). 

 Given [f : A -> B] and families [K] from [A] and [L] from [B],
 a map over [f] from [K] to [L] is a function [ff] from elements of [K] to 
 elements of [L], such that for any element [i : K], its realisation [K i]
 as an element of [A] is mapped under [f] to the realisation [L (ff i)] in
 [B]. *)
Local Definition map_over {A B} (f : A -> B) (K : family A) (L : family B)
  := { ff : K -> L
     & forall i : K, L (ff i) = f (K i) }.

(** For the special case of a map between families from the same type, a map of families is a map of their indices/elements, commuting with the evaluation map. *)
Local Definition map {A} (K L : family A)
  := map_over idmap K L.

(** Re-grouping of constructor function for [map]: useful when the map and equality components for each input are most easily given together, e.g. if they involve an induction on the input. *)
Local Definition Build_map' {A B} (f : A -> B) (K : family A) (L : family B)
    (g : forall i:K, { j:L & L j = f (K i) })
  : map_over f K L.
Proof.
  exists (fun i => pr1 (g i)).
  intros i. exact (pr2 (g i)).
Defined.

Local Definition map_index_action
    {A B} (f : A -> B) (K : family A) (L : family B)
  : map_over f K L -> (K -> L)
:= pr1.
Coercion map_index_action : map_over >-> Funclass.

(** Trivial conversion, needed for the coercion [map_index_action] to
 work on [map] as well as [map_over]. *)
Local Definition map_over_of_map {A} {K L : family A}
  : map K L -> map_over idmap K L
:= idmap.
Coercion map_over_of_map : map >-> map_over.

Local Definition map_over_commutes
  {A B} {f : A -> B} {K : family A} {L : family B}
  : forall ff : map_over f K L,
    forall i : K, L (ff i) = f (K i)
:= pr2.

Local Definition map_commutes
  {A} {K L : family A}
  : forall f : map K L,
    forall i : K, L (f i) = K i
:= pr2.

(** Several equality lemmas for maps. *)
Local Definition map_over_eq `{Funext}
    {X X'} {f : X -> X'}
    {K} {L} {ff gg : map_over f K L}
    (e_map : forall k:K, ff k = gg k)
    (e_comm : forall k:K,
      map_over_commutes ff k
      = ap L (e_map k) @ map_over_commutes gg k)
  : ff = gg.
Proof.
  destruct ff as [ff_ob ff_comm], gg as [gg_ob gg_comm].
  set (e_map' := path_forall _ _ e_map : ff_ob = gg_ob).
  assert (ee : e_map == ap10 e_map').
    { intros i; apply inverse, ap10_path_forall. }
  destruct e_map'. apply ap.
  apply path_forall; intros k.
  cbn in e_comm.
  eapply concat. { apply e_comm. }
  eapply concat. { eapply ap10, ap, ap, ee. }
  apply concat_1p.
Defined.

Definition map_eq `{Funext} {X} {K L : family X} {f g : map K L}
  (e_map : forall k:K, f k = g k)
  (e_comm : forall k:K,
      map_commutes f k = ap L (e_map k) @ map_commutes g k)
  : f = g.
Proof.
  exact (map_over_eq e_map e_comm).
Defined.

Local Definition map_over_eq' `{Funext}
    {X X'} {f : X -> X'}
    {K} {L} {ff gg : map_over f K L}
  : (forall k:K, { e : ff k = gg k
       & map_over_commutes ff k
         = ap L e @ map_over_commutes gg k } )
  -> ff = gg.
Proof.
  intros e.
  simple refine (map_over_eq _ _); intros k.
  - exact (e k).1.
  - exact (e k).2.
Defined.

Local Definition map_eq' `{Funext} {X} {K L : family X} {f g : map K L}
  : (forall k:K, { e : f k = g k
       & map_commutes f k = ap L e @ map_commutes g k } )
  -> f = g.
Proof.
  intros e. exact (map_over_eq' e).
Defined.

Local Definition idmap {X} (K : family X)
  : map K K.
Proof.
  econstructor.
  intro; constructor.
Defined.

Local Definition compose_over {X Y Z} {g : Y -> Z} {f : X -> Y}
   {K} {L} {M} (gg : map_over g L M) (ff : map_over f K L)
  : map_over (g o f) K M.
Proof.
  exists (compose gg ff).
  intros. refine (_ @ _).
  - apply map_over_commutes.
  - apply ap; apply map_over_commutes.
Defined.

Local Definition compose {X} {K L M : family X} (g : map L M) (f : map K L)
  : map K M
:= compose_over g f.

(** This lemma [map_transport] is essentially transport for [map_over] in
the base map, but given in a form that provides better computational 
behaviour: the action on indices is not stuck under a transport. 

The next lemma, [transport_map], shows that this is indeed equal to the
transport. Where possible, though, one should simply avoid using that
[transport] by using this [map_transport] instead. *)
(* TODO: consider naming *)
Local Definition map_transport
    {X Y} {f f' : X -> Y} (e : f = f')
    {K} {L} (ff : map_over f K L)
  : map_over f' K L.
Proof.
  exists ff.
  intros k.
  exact (map_over_commutes ff _ @ ap10 e _).
Defined.

(* TODO: consider naming *)
Local Lemma transport_map `{Funext}
    {X Y} {f f' : X -> Y} (e : f = f')
    {K} {L} (ff : map_over f K L)
  : transport (fun g => map_over g _ _) e ff
    = map_transport e ff.
Proof.
  destruct e. apply map_over_eq'; intros k.
  exists (idpath _); cbn.
  apply inverse.
  eapply concat. { apply concat_1p. }
  apply concat_p1.
Defined.

Local Lemma id_left `{Funext}
    {X} {K K' : family X} {f : map K K'}
  : compose (idmap K') f = f.
Proof.
  apply map_eq'.
  intros i. exists (idpath _); cbn.
  apply ap, ap_idmap.
Defined.

Local Lemma id_right `{Funext}
    {X} {K K' : family X} {f : map K K'}
  : compose f (idmap K) = f.
Proof.
  apply map_eq'.
  intros i. exists (idpath _); cbn.
  eapply concat. { apply concat_p1. }
  apply inverse, concat_1p.
Defined.

Local Lemma map_from_eq
    {X} {K K' : family X} (e : K = K')
  : map K K'.
Proof.
  destruct e. apply idmap.
Defined.

(** Families are (pseudo-)functorial in their value types; categorically, they form a fibration over types.*)

Local Definition fmap {X Y} (f : X -> Y) (K : family X) : family Y.
Proof.
  exists K.
  exact (fun i => f (K i)).
Defined.

Local Lemma map_to_fmap
    {X X'} (f : X -> X') (K : family X)
  : map_over f K (fmap f K).
Proof.
  exists Overture.idmap.
  intros i; apply idpath.
Defined.

(** Note that these are in fact judgementally equal! But it’s often helpful to make the conversion explicit. *)
Local Lemma map_vs_map_over
    {X X'} (f : X -> X')
    (K : family X) (K' : family X')
  : map (fmap f K) K' <~> map_over f K K'.
Proof.
  exact (equiv_idmap _).
Defined.

Local Lemma fmap_idmap
    {X} (K : family X)
  : fmap Overture.idmap K = K.
Proof.
  apply idpath.
Defined.

Local Lemma fmap_compose {X Y Z} (f : X -> Y) (g : Y -> Z) (K : family X)
  : fmap (g o f) K = fmap g (fmap f K).
Proof.
  apply idpath.
Defined.

Local Definition map_fmap
    {X Y} (f : X -> Y)
    {K K' : family X} (g : map K K')
  : map (fmap f K) (fmap f K').
Proof.
  exists g.
  intros i. cbn. apply ap. apply map_commutes.
Defined.

Local Lemma map_fmap_compose `{Funext}
    {X Y} (f : X -> Y)
    {K K' K'' : family X} (g' : map K' K'') (g : map K K')
  : compose (map_fmap f g') (map_fmap f g)
    = map_fmap f (compose g' g). 
Proof.
  apply map_eq'.
  intros k; exists (idpath _); cbn.
  apply inverse.
  eapply concat. { apply concat_1p. }
  eapply concat. { apply ap_pp. }
  apply ap.
  eapply concat. {apply ap, ap_idmap. }
  apply inverse, ap_idmap.
Defined.

(** The empty family, and its universal property. *)
Local Definition empty (X : Type) : family X.
Proof.
  exists Overture.Empty.
  intros [].
Defined.

Notation " [< >] " := (empty _) (format "[< >]") : family_scope.

Local Definition empty_rect {X Y} {f : X -> Y} {K : family Y}
  : map_over f (empty X) K.
Proof.
  simple refine (_;_); intros [].
Defined.

Local Definition empty_rect_unique `{Funext} {X Y} (f : X -> Y)
  {K} (ff : map_over f (empty X) K)
  : ff = empty_rect.
Proof.
  apply map_over_eq'; intros [].
Defined.


(** Sums of families, and their universal property, functoriality, etc. *)
Local Definition sum {X} (Y1 Y2 : family X) : family X
  := {| family_index := Y1 + Y2
      ; family_element y := match y with inl y => Y1 y | inr y => Y2 y end |}.

Notation "Y1 + Y2" := (sum Y1 Y2) : family_scope.

Local Definition inl {X} {K K' : family X}
  : map K (K + K').
Proof.
  exists inl.
  intro; apply idpath.
Defined.

Local Definition inr {X} {K K' : family X}
  : map K' (K + K').
Proof.
  exists inr.
  intro; apply idpath.
Defined.

Local Definition sum_rect {X} {Y} {f : X -> Y}
    {K1 K2} {L} (ff1 : map_over f K1 L) (ff2 : map_over f K2 L)
  : map_over f (K1 + K2) L.
Proof.
  simple refine (_;_).
  - intros [ x | x ]; [apply ff1 | apply ff2]; apply x. 
  - intros [ x | x ]; cbn; apply map_over_commutes.
Defined.

Local Definition sum_fmap
    {X Y} {f : X -> Y}
    {K} {K'} (gg : map_over f K K')
    {L} {L'} (hh : map_over f L L')
  : map_over f (sum K L) (sum K' L').
Proof.
  simple refine (_;_).
  - intros [ i | j ].
    + apply inl, gg, i.
    + apply inr, hh, j.
  - intros [ i | j ];
    simpl; apply map_over_commutes.
Defined.

Local Lemma sum_fmap_compose_over `{Funext}
    {X X' X''} {f' : X' -> X''} {f : X -> X'}
    {K} {K'} {K''} (g' : map_over f' K' K'') (g : map_over f K K')
    {L} {L'} {L''} (h' : map_over f' L' L'') (h : map_over f L L')
  : compose_over (sum_fmap g' h') (sum_fmap g h)
    = sum_fmap (compose_over g' g) (compose_over h' h).
Proof.
  simple refine (map_over_eq' _).
  intros [k | l]; exists (idpath _);
    apply inverse, concat_1p.
Defined.

Local Lemma sum_fmap_compose `{Funext}
    {X}
    {K K' K'' : family X} (g' : map K' K'') (g : map K K')
    {L L' L'' : family X} (h' : map L' L'') (h : map L L')
  : compose (sum_fmap g' h') (sum_fmap g h)
    = sum_fmap (compose g' g) (compose h' h).
Proof.
  exact (sum_fmap_compose_over g' g h' h).
Defined.

Local Definition sum_symmetry {X} (K L : family X)
  : map (K + L) (L + K).
Proof.
  apply sum_rect; [ apply inr | apply inl ].
Defined.

Local Lemma fmap_sum `{Funext}
    {X Y} (f : X -> Y)
     (K1 K2 : family X)
  : fmap f (sum K1 K2) = sum (fmap f K1) (fmap f K2).
Proof.
  simple refine (eq _ _).
  - apply idpath.
  - intros [? | ?]; apply idpath.
Defined.


(** Singleton families *)
Local Definition singleton {X} (x:X) : family X.
Proof.
  exists Overture.Unit.
  intros _; exact x.
Defined.


(** Adjoining one element to a family; acts as [option], on the index type *)
Local Definition adjoin {X} (K : family X) (x : X) : family X.
Proof.
  exists (option K).
  intros [i | ].
  - exact (K i).
  - exact x.
Defined.

Local Definition some {X} (K : family X) (x : X)
  : map K (adjoin K x).
Proof.
  exists (@Some _).
  intros i; apply idpath.
Defined.

Local Lemma fmap_adjoin `{Funext}
    {X Y} (f : X -> Y)
    (K : family X) (x : X)
  : fmap f (adjoin K x) = adjoin (fmap f K) (f x).
Proof.
  simple refine (eq _ _).
  - apply idpath.
  - intros [? | ]; apply idpath.
Defined.

Notation " [< x >] " := (singleton x) : family_scope.

(** A list-like notation for families. *)
Notation " [< x ; y ; .. ; z >] " := (adjoin .. (adjoin (singleton x) y) .. z) : family_scope.


(** The monadic _bind_ operation for families.  At least heuristically, families form a monad; this allows Haskell-like monadic programming with them.

(Actually making families a monad in any precise category-theoretic sense runs into both size issues and h-level issues, so we don’t attempt that here.)  *)
Local Definition bind {A B}
  (K : family A) (f : A -> family B) : family B.
Proof.
  exists { i : K & f (K i) }.
  intros [i j].
  exact (f (K i) j).
Defined.

(* TODO: make an iso? *)
Lemma bind_fmap_mid
    {A A'} (f : A -> A')
    {B} (K : family A) (L : A' -> family B)
  : map
      (bind K (fun a => L (f a)))
      (bind (fmap f K) L).
Proof.
  apply idmap.
Defined.

Lemma bind_fmap2
    {A} (K : family A)
    {B B'} (f : B -> B')
    {L} {L'} (ff : forall a, map_over f (L a) (L' a))
  : map_over f
      (bind K L)
      (bind K L').
Proof.
  apply Build_map'. intros [i j].
  exists (i ; ff _ j).
  apply (map_over_commutes (ff _)).
Defined.

(* TODO: make an iso? *)
Lemma fmap_bind
    {B B'} (f : B -> B')
    {A} (K : family A) (L : A -> family B)
  : map
      (fmap f (bind K L))
      (bind K (fun a => fmap f (L a))).
Proof.
  apply idmap.
Defined.

(** Reindexing of a family along a map into the index type *)
Local Definition reindex {A} (K : family A) {X} (f : X -> K) : family A
  := {|
       family_index := X ;
       family_element := K o f
     |}.

(** The subfamily of a family determined by a predicate on the index type (which of course can make use of the values of the family) *)
Local Definition subfamily {A} (K : family A) (P : K -> Type) : family A
  := reindex K (pr1 : { i:K & P i } -> K).

Local Definition subfamily_inclusion
    {A : Type} (K : family A) (P : K -> Type)
  : map (subfamily K P) K.
Proof.
  exists pr1.
  intros; apply idpath.
Defined.


(** The subfamily of a family determined by a predicate on the value type *)
Local Definition filter {A} (K : family A) (P : A -> Type) : family A
  := subfamily K (P o K).


