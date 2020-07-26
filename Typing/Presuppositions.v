Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ScopeSystem.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.
Require Import Syntax.Metavariable.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.

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

  Context {σ : scope_system}.

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
    destruct j as [Δ [jf J]];
      recursive_destruct jf; recursive_destruct i;
      apply Judgement.eq_by_eta, idpath.
  Defined.

End Presuppositions.

Section Presuppositive_Flat_Rules.

  Context {σ : scope_system}.

  (** A flat rule [r] (in ambient signature [Σ], with metavariables [a])
      is presuppositive over a flat type theory [T] if all presuppositions of
      the conclusion are derivable from the premises plus their presuppositions,
      over the translation of [T] to [Σ + a].
   *)
  Definition weakly_presuppositive_flat_rule {Σ : signature σ}
      (T : flat_type_theory Σ) (r : flat_rule Σ)
    : Type
  := forall c_presup : presupposition (flat_rule_conclusion r),
      (FlatTypeTheory.derivation
         (FlatTypeTheory.fmap include_symbol T)
         (let H := flat_rule_premise r in H + Family.bind H presupposition)
         (presupposition _ c_presup)).

  (** Note: we could give (as we have for closure rules) a stronger notion of
  presuppositivity, where we derive the presuppositions of premises as well
  as of the conclusion, and (in all these derivations) we assume just the
  premises as hypotheses, not also their presuppositions.
  *)

  Context `{Funext}.

  Definition fmap_weakly_presuppositive_flat_rule
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T} {T'} (ff : FlatTypeTheory.map_over f T T')
      (r : flat_rule Σ) (r_wt : weakly_presuppositive_flat_rule T r)
    : weakly_presuppositive_flat_rule T' (FlatRule.fmap f r).
  Proof.
    intros p.
    refine (transport _ _ _).
    - apply fmap_presupposition.
    - simple refine (Closure.derivation_fmap2 _
        (FlatTypeTheory.derivation_fmap1_over _ (r_wt p))).
      + cbn.
        (* TODO: rewrite [Family.fmap_sum] as an iso, for better behaviour? *)
        refine (transport (fun K => Family.map K _) _ _).
        { apply inverse, Family.fmap_sum. }
        apply (Family.sum_fmap (Family.idmap _)).
        refine (Family.compose (Family.bind_fmap_mid _ _ _) _).
        apply Family.bind_fmap2. intros a.
        apply fmap_presupposition_family.
      + (* TODO: the following could possibly be better abstracted in terms of the fibrational properties of flat type theory maps? *)
        intros R.
        refine (transport _ _
          (FlatTypeTheory.flat_rule_derivation_fmap _ (ff R))).
        refine (_ @ FlatRule.fmap_compose _ _ _).
        refine ((FlatRule.fmap_compose _ _ _)^ @ _).
        apply ap10, ap. apply Metavariable.include_symbol_after_map.
  Defined.

  (** If a flat rule [r] is presuppositive over a type theory [T],
      then each instantiation of [r] as a closure condition is presuppositive
      over the associated closure system of [T]. *)
  Lemma flat_rule_closure_system_weakly_presuppositive {Σ : signature σ}
       (T : flat_type_theory Σ)
       (r : flat_rule Σ) (D_r : weakly_presuppositive_flat_rule T r)
       {Γ : raw_context Σ}
       (I : Metavariable.instantiation (flat_rule_metas r) Σ Γ)
    : Closure.weakly_presuppositive_rule presupposition
        (FlatTypeTheory.closure_system T)
        (FlatRule.closure_system r (Γ;I)).
  Proof.
    (* Rough idea: derivations translate along the instantiation of syntax,
    so the derivations provided by presuppositivity of [r] translate into
    the derivations required for presuppositivity of its instantiations. *)
      unfold Closure.weakly_presuppositive_rule.
      intros p.
      eapply transport.
      { apply instantiate_presupposition. }
      refine (Closure.graft _ _ _).
      + refine (FlatTypeTheory.instantiate_derivation _ _ _ _).
        apply D_r.
      + intros [ i | [ i i_presup]].
        * simple refine (Closure.hypothesis' _ _).
          -- exact (inl i).
          -- apply idpath.
        * simple refine (Closure.hypothesis' _ _).
          -- refine (inr (i;_)). exact i_presup.
          -- apply inverse. refine (instantiate_presupposition _ _ _).
  Defined.

End Presuppositive_Flat_Rules.
