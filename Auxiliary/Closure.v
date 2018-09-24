(** _Closure systems_ are a general abstract setting for derivations / inductively defined predicates.

A _closure condition_ or _rule_, over an ambient set [X], means just a family of elements of [X] (the _premises_) together with another element (the _conclusion_).

Given a family of closure conditions — a _closure system_ — one can consider the inductively defined predicate generated by these closure conditions, plus any initial family of elements (_hypotheses_).  Viewed proof-relevantly, that is precisely the predicate of _derivations_, using the rules of the closure system and the given hypotheses. *)

Require Import HoTT.
Require Import Auxiliary.Family.

(** A rule on [X] is just a family of _premises_ and a _conclusion_, abstracting
the form of inference rules. *)
Local Record rule (X : Type) :=
  {
    premises : family X ;
    conclusion : X
  }.

Arguments premises [_] _.
Arguments conclusion [_] _.

Local Definition rule_eq {X} {c c' : rule X}
  : premises c = premises c'
  -> conclusion c = conclusion c'
  -> c = c'.
Proof.
  destruct c, c'; cbn.
  intros e e'; destruct e, e'.
  apply idpath.
Defined.

(** Map a rule in [X] to a rule in [Y] along a map [f : X -> Y]. *)
Local Definition rule_fmap {X Y} (f : X -> Y) : rule X -> rule Y.
Proof.
  intros [ps c].
  exact {| premises := Family.fmap f ps ; conclusion := f c |}.
Defined.



(** A closure system is a family of rules. *)
Local Definition system (X : Type) := family (rule X).

(** Closure systems form a displayed category in two different ways:

- “simple maps”: these are just family maps, so we don’t need to define/develop them here.
- _closure system maps_, given below; these are (roughly) Kleisli maps for the “derivability” monad, so can’t be defined until after derivations and some infrastructure have been set up. *)


Section Derivations.

(** Derivations generated by the given family of rules [C] and hypotheses [H].  *)
Local Inductive derivation {X} (C : system X) (H : family X) : X -> Type :=
  | hypothesis : forall (i : H), derivation C H (H i)
  | deduce (r : C) :
      (forall (p : premises (C r)), derivation C H (premises (C r) p))
      -> derivation C H (conclusion (C r)).

(** Due to the dependency in conclusions, it is often tricky to give derivations
in tactic proofs: [apply hypothesis], [apply deduce] often fail to unify.

The following lemmas allow one to write e.g.:

    simple refine (Closure.deduce' _ _ _).
    - (interactively select the desired rule) 
    - (show it has the right conclusion; often just [apply idpath])
    - (now derive the premises)

      simple refine (Closure.hypothesis' _ _).
    - (interactively select the desired hypothesis) 
    - (show it has the right conclusion; often just [apply idpath])
*)
Local Definition deduce' {X} {C : system X} {H : family X}
  {x : X} (r : C) (e : conclusion (C r) = x)
  (d_prems : forall p : premises (C r), derivation C H (premises (C r) p))
  : derivation C H x
:= transport _ e (deduce C H r d_prems).

Local Definition hypothesis' {X} {C : system X} {H : family X}
  {x : X} (h : H) (e : H h = x)
  : derivation C H x
:= transport _ e (hypothesis C H h).

(** Given a derivation [d] from hypotheses [H], and for each hypothesis [h]
    a derivation of it from hypotheses [G], we can graft the derivations onto
    [d] to get a derivation from hypotheses [G]. *)
Local Definition graft {X} (C : system X)
    {H} {x} (d : derivation C H x)
    {G} (f : forall i : H, derivation C G (H i))
  : derivation C G x.
Proof.
  induction d.
  (* hypothesis *)
  - now apply f.
  (* deduction step *)
  - now apply (deduce _ _ r).
Defined.

(** For using [graft] interactively, similar to [deduce'], [hypothesis']. 
 Use as:

  refine (graft _ _ _).
  - (give derivation d for grafting) 
  - (show it has correct conclusion)
  - (derive premises of d)

*)
Local Definition graft' {X} {C : system X}
    {H} {x} {x'} (d : derivation C H x') (e : x' = x)
    {G} (f : forall i : H, derivation C G (H i))
  : derivation C G x
:= transport _ e (graft C d f).

(** General functoriality of derivations, in simple (non-Kleisli) maps of closure systems.

Can be recovered from their later functoriality in (Kleisli) closure system maps, but this is conceptually a simpler and standalone thing. *)
Local Definition derivation_fmap_simple_over
    {X X'} (f : X -> X')
    {T : system X} {T' : system X'} (fT : Family.map_over (rule_fmap f) T T')
    {H H'} (fH : Family.map_over f H H')
    {x} (D : derivation T H x)
  : derivation T' H' (f x).
Proof.
  induction D as [ h | r _ Ds].
  - simple refine (hypothesis' _ _).  
    + exact (fH h).
    + apply Family.map_over_commutes.
  - simple refine (deduce' _ _ _).
    + exact (fT r).
    + eapply concat. { apply ap, Family.map_over_commutes. }
      apply idpath.
    + refine (transport
        (fun (prems:family _) => forall p : prems, derivation T' H' (prems p))
        _^ _).
      apply ap, Family.map_over_commutes.
      exact Ds.
Defined.

(** Functoriality of derivations in simple maps of theories *)
Local Definition derivation_fmap1_simple
    {X} {T T': system X} (f : Family.map T T') {H} {x}
    (D : derivation T H x)
  : derivation T' H x.
Proof.
  exact (derivation_fmap_simple_over _ f (Family.idmap H) D).
Defined.

(** Functoriality of derivations in their hypotheses. *)
Local Definition derivation_fmap2
    {X} {T : system X} {H H'} (f : Family.map H H') {x}
    (D : derivation T H x)
  : derivation T H' x.
Proof.
  refine (graft _ D _); intros i.
  apply (hypothesis' (f i)).
  apply Family.map_commutes.
Defined.

End Derivations.

Section Closure_System_Maps.

(** In general, one can consider maps between closure systems _over_ maps between the sets they’re on, in the sense of a _displayed category_ (arXiv:1705.04296).

  A map from a closure system [C] on [X] to a closure system [D] on [Y], over [f : X -> Y] gives for each rule [C i] of [C] a derivation in [D] of the conclusion of [C i] from the premises of [C i]. *)
Local Definition map_over {X Y} (f : X -> Y) (C : system X) (D : system Y)
  : Type
:= forall i : C, derivation D
     (Family.fmap f (premises (C i))) (f (conclusion (C i))).

(** A map from a closure system [C] to a closure system [D] gives, for each
    rule [C i] in [C i] in [C], a derivation in [D] of the conclusion of [C i]
    from the premises of [C i]. *)
Local Definition map {X} (C D : system X) : Type
  := map_over idmap C D.

(** We can of always map a closure system to itself by deducing the
    conclusion of every rule by simply applying the rule. *)
Local Definition idmap {X} (C : system X) : map C C.
Proof.
  intro i.
  apply deduce.
  intro p.
  now apply hypothesis.
Defined.

(** More generally, a family map between closure systems gives a closure map between them.

An alternative point of view here is that family maps could be taken as the basic maps between closure systems; closure system maps are then Kleisli maps for the monad sending a closure system to its family of derivability conditions, and this definition is then the unit map of that monad.  We do not take that approach as primary since it creates various complications, e.g. size issues.  *)
Local Definition map_from_family_map
    {X Y} {f : X -> Y} {C : system X} {D : system Y}
  : Family.map_over (rule_fmap f) C D -> map_over f C D.
Proof.
  intros ff i.
  refine (deduce' (ff i) _ _).
  - refine (ap _ (Family.map_over_commutes _ _)).
  - set (Df := premises (D (ff i))) in *.
    set (e := ap _ (Family.map_over_commutes ff i)^ : _ = Df).
    destruct e.
    intro p. apply hypothesis.
Defined.

(** Given a closure system map from [C] to [D],
   we can map derivations over [C] to derivations over [D]. *)
Local Fixpoint derivation_fmap_over
    {X Y} {f : X -> Y} {C : system X} {D : system Y} (ff : map_over f C D)
    {H} {x} (d : derivation C H x)
  : derivation D (Family.fmap f H) (f x).
Proof.
  destruct d as [i | r d_prems].
  - refine (hypothesis _ (Family.fmap f H) i).
  - refine (graft _ (ff r) _).
    intro i. apply (derivation_fmap_over _ _ _ _ _ ff), d_prems.
Defined.

Arguments derivation_fmap_over : simpl nomatch.

(** Although [derivation_fmap] is just a special case of [derivation_fmap_over],
 it is given separately since the specialised statement works better in
 interactive proofs.

 Specifically, while [Family.fmap idmap H] is in fact judgementally
 equal to [H], the unification performed by [apply] doesn’t always recognise
 this. *)
Local Definition derivation_fmap
    {X} {C D : system X} (f : map C D)
    {H} {x} (d : derivation C H x)
  : derivation D H x
:= derivation_fmap_over f d.

Arguments derivation_fmap : simpl nomatch.

Local Definition compose_over {X Y Z} {f : X -> Y} {g : Y -> Z}
    {K} {L} {M} (ff : map_over f K L) (gg : map_over g L M)
  : map_over (g o f) K M.
Proof.
  intros k.
  exact (derivation_fmap_over gg (ff k)).
Defined.

Local Definition compose_over' {X Y Z} (f : X -> Y) (g : Y -> Z)
    {K} {L} {M} (ff : map_over f K L) (gg : map_over g L M)
    {h} (e : h = g o f)
  : map_over h K M.
Proof.
  exact (transport (fun m => map_over m K M) e^ (compose_over ff gg)).
Defined.

End Closure_System_Maps.

Section Sums.

(** The sum of closure systems is just their sum as families. *)

Local Definition inl {X} {C D : system X}
  : map C (C + D)
:= map_from_family_map Family.inl.

Local Definition inr {X} {C D : system X}
  : map D (C + D)
:= map_from_family_map Family.inr.

Local Lemma sum_rect {X} {Y} {f : X -> Y}
    {K1 K2} {L} (ff1 : map_over f K1 L) (ff2 : map_over f K2 L)
  : map_over f (K1 + K2) L.
Proof.
  intros [ x | x ]; [apply ff1 | apply ff2].
Defined.

(** Analogue of [Family.sum_fmap] *)
Local Definition sum_fmap
    {X Y} {f : X -> Y}
    {C} {D} (ff : map_over f C D)
    {C'} {D'} (ff' : map_over f C' D')
  : map_over f (Family.sum C C') (Family.sum D D').
Proof.
  intros [r | r'].
  - exact (derivation_fmap1_simple Family.inl (ff _)).
  - exact (derivation_fmap1_simple Family.inr (ff' _)).
 Defined.

Local Definition sum_fmap1
    {X} {C D : system X} (ff : map C D) {C'}
  : map (C + C') (D + C').
Proof.
  exact (sum_fmap ff (idmap _)).
Defined.

Local Definition sum_fmap2
    {X} {C C' D' : system X} (ff : map C' D')
  : map (C + C') (C + D').
Proof.
  exact (sum_fmap (idmap _) ff).
Defined.

End Sums.


Section Axioms.

(** Having a hypothesis of [x] is equivalent to having [x] as an axiom in the closure system. It’s sometimes convenient to have both these options available, and convert between them. *)
Local Definition axiom {X} (x:X) : rule X
  := {| premises := [<>]; conclusion := x |}.

Local Definition axioms {X} (H : family X) : system X
  := Family.fmap axiom H.

Definition axioms_vs_hypotheses {X}
    (T : system X) (H1 H2 : family X) (x:X)
  : derivation T (H1 + H2) x
  <-> derivation (T + axioms H1) H2 x.
Proof.
  split.
  - intro d. refine (graft _ (derivation_fmap inl d) _).
    intros [h1 | h2].
    + refine (deduce (T+Family.fmap axiom H1) _ (Datatypes.inr h1) _).
      intros [].
    + exact (hypothesis _ _ h2).
  - intros d; induction d as [ h2 | [r | h1] _ ds ].
    + exact (hypothesis _ (_+_) (Datatypes.inr h2)).
    + exact (deduce _ _ r ds). 
    + exact (hypothesis _ (H1+_) (Datatypes.inl h1)).
Defined.

End Axioms.