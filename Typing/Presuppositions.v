Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.
Require Import Syntax.Metavariable.
Require Import Typing.Context.
Require Import Typing.Judgement.

(** A key notion is the _presuppositions_ of a judgement.

For instance, the judgement [ Γ |- a : A ] has just one presupposition: [ Γ |- A type ].  The judgement [ Γ |- A ≡ B ] has two presuppositions, [ Γ |- A type ] and [ Γ |- B type ].

As with judgements themselves, we first describe set up the combinatorics indexing the constructions involved. *)

Section PresuppositionsCombinatorics.

(** Whenever an object appears in the boundary of an object judgement, then its
    boundary embeds into that boundary.

    NOTE. This is a special case of [boundary_slot_from_presupposition] below.
    It is abstracted out because it’s used twice: directly for object
    judgements, and as part of the case for equality judgements.

    In fact it’s almost trivial, so could easily be inlined; but conceptually
    it is the same thing both times, and in type theory with more judgements,
    it would be less trivial, so we keep it factored out. *)
  Definition object_boundary_from_boundary_slots
    {cl : syntactic_class} (i : Judgement.object_boundary_slot cl)
    : Family.map
        (Judgement.object_boundary_slot (Judgement.object_boundary_slot cl i))
        (Judgement.object_boundary_slot cl).
  Proof.
    apply Family.Build_map'. intros j.
    destruct cl as [ | ]; cbn in i.
    (* Ty: nothing to do, no objects in boundary *)
    - destruct i.
    (* Tm: i must be type, so again nothing left, no j in its boundary *)
    - destruct i as []; destruct j.
  Defined.

(** Wherever an judgement [I] occurs as a presupposition of a judgement [J],
there is a canonical embedding of the slots of [I] into the slots of [J]. *)
  Definition boundary_slot_from_presupposition
    {jf : form} (i : Judgement.boundary_slot jf)
    : Family.map
        (Judgement.slot (form_object (Judgement.boundary_slot jf i)))
        (Judgement.boundary_slot jf).
  Proof.
    apply Family.Build_map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct jf as [ cl | cl ].
      + (* original jf is object judgement *)
        exists (object_boundary_from_boundary_slots i j).
        apply (Family.map_commutes _ j).
      + (* original jf is equality judgement *)
        destruct i as [ i' |  | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists
            (the_equality_boundary_slot _ (object_boundary_from_boundary_slots i' j)).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (the_equality_boundary_slot _ j). apply idpath.
        * (* i is LHS *)
          exists (the_equality_boundary_slot _ j). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.

  Definition slot_from_presupposition
    {jf : form} (i : Judgement.boundary_slot jf)
    : Family.map
        (Judgement.slot (form_object (Judgement.boundary_slot _ i)))
        (Judgement.slot jf).
  Proof.
    eapply Family.compose.
    - apply the_boundary_slot.
    - apply boundary_slot_from_presupposition.
  Defined.

End PresuppositionsCombinatorics.

Section Presuppositions.
(** TODO: the naming in this section seems a bit ugly. *)

  Context {σ : shape_system}.

  (** The presuppositions of a judgment boundary [jb] *)
  Definition presupposition_of_boundary
      {Σ : signature σ} (B : boundary Σ)
    : family (judgement Σ).
  Proof.
    simple refine (Build_family _ _ _).
    - exact (Judgement.boundary_slot (form_of_boundary B)).
    - intros i. exists (context_of_boundary B).
      exists (form_object (Judgement.boundary_slot _ i)).
      intros j.
      refine (transport (fun cl => raw_expression _ cl _) _ _).
      + exact (Family.map_commutes (boundary_slot_from_presupposition i) j).
      + exact (B (boundary_slot_from_presupposition i j)).
  Defined.

  (** The presuppositions of judgement [j]. *)
  Definition presupposition
      {Σ : signature σ} (j : judgement Σ)
    : family (judgement Σ)
  := presupposition_of_boundary (boundary_of_judgement j).

  (** Interactions between functoriality under signature maps,
   and taking presuppositions. *)

  Definition fmap_presupposition_of_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ) (p : presupposition_of_boundary B)
    : Judgement.fmap f (presupposition_of_boundary B p)
    = presupposition_of_boundary (Judgement.fmap_boundary f B) p.
  Proof.
    destruct B as [Γ [jf B]].
    recursive_destruct jf; recursive_destruct p; try apply idpath;
      refine (Judgement.eq_by_expressions _ _);
      intros j; recursive_destruct j; apply idpath.
  Defined.

  (* TODO: this should be an iso! *)
  Definition presupposition_fmap_boundary `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (B : boundary Σ)
    : Family.map
        (presupposition_of_boundary (Judgement.fmap_boundary f B))
        (Family.fmap (Judgement.fmap f) (presupposition_of_boundary B)).
  Proof.
    exists idmap.
    intros i; apply fmap_presupposition_of_boundary.
  Defined.

  Definition fmap_presupposition `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
      (p : presupposition J)
    : Judgement.fmap f (presupposition J p)
    = presupposition (Judgement.fmap f J) p.
  Proof.
    destruct J as [Γ [jf J]].
      recursive_destruct jf; recursive_destruct p; try apply idpath;
        refine (Judgement.eq_by_expressions _ _);
        intros j; recursive_destruct j; apply idpath.    
  Defined.

  (* TODO: this should be an iso!  And consistentise with [presupposition_fmap_boundary]. *)
  Definition fmap_presupposition_family `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (J : judgement Σ)
    : Family.map
        (Family.fmap (Judgement.fmap f) (presupposition J))
        (presupposition (Judgement.fmap f J)).
  Proof.
    exists (fun p => p).
    intros p; apply inverse, fmap_presupposition.
  Defined.

  (** The instantiation under [I] of any presupposition of a judgement [j]
      is equal to the corresponding presupposition of the instantiation of [j]
      itself under [I]. *)
  Definition instantiate_presupposition `{Funext}
      {Σ : signature σ}
      {Γ : raw_context Σ} {a} (I : Metavariable.instantiation a Σ Γ)
      (j : judgement _)
      (i : presupposition (Judgement.instantiate Γ I j))
    : Judgement.instantiate Γ I (presupposition j i)
      = presupposition (Judgement.instantiate Γ I j) i.
  Proof.
    apply (ap (Build_judgement _)). (* context of presup unchanged *)
    apply (ap (Build_hypothetical_judgement _)). (* form of presup unchanged *)
    destruct j as [Δ [jf J]].
    (* hypothetical presupposition *)
    apply path_forall; intros k.
    recursive_destruct jf;
      recursive_destruct i;
      recursive_destruct k;
      apply idpath.
  Defined.

End Presuppositions.

