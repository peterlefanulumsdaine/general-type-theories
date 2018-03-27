Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.Theory.
Require Import WellFormed.Rule.
Require Import WellFormed.TypeTheory.

(** In this file: definition of well-typedness of a rule, and of a type-theory. *)

Section Welltypedness.

  Context {σ : shape_system}.

  (* TODO: move upstream! *)
  Definition Build_Family_Map' {X} {K L : family X}
    : (forall i:K, {j:L & L j = K i})
      -> Family.map K L.
  Proof.
    intros f.
    exists (fun i => pr1 (f i)).
    intros i; exact (pr2 (f i)).
  Defined.

  Arguments Judgement.hypothetical_boundary : simpl nomatch.
  Arguments Judgement.hypothetical_boundary : simpl nomatch.

  (* TODO: move upstream; consider name! *)
  (* This is the special case of [presup_slots_from_boundary] for object judgements.
    It is abstracted out because it’s used twice: directly for object judgements, and as part of the case for equality judgements.
    In fact it’s almost trivial, so could easily be inlined; but conceptually it is the same thing both times, and in type theory with more judgements, it could be less trivial, so we keep it factored out. *)
  Definition obj_presup_slots_from_boundary
    {cl : syntactic_class} (i : Judgement.hypothetical_boundary cl)
    : Family.map
        (Judgement.hypothetical_boundary (Judgement.hypothetical_boundary cl i))
        (Judgement.hypothetical_boundary cl).
  Proof.
    apply Build_Family_Map'. intros j.
    destruct cl as [ | ]; cbn in i.
    (* Ty: nothing to do, no objects in boundary *)
    - destruct i.
    (* Tm: i must be type, so again nothing left, no j in its boundary *)
    - destruct i as [[] |]; destruct j.
  Defined.

  (* TODO: move upstream; consider name! *)
  Definition presup_slots_from_boundary
    {hjf : judgement_form} (i : Judgement.hypothetical_boundary hjf)
    : Family.map
        (judgement_form_Slots (form_object (Judgement.hypothetical_boundary hjf i)))
        (Judgement.hypothetical_boundary hjf).
  Proof.
    apply Build_Family_Map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct hjf as [ cl | cl ].
      + (* original hjf is object judgement *)
        exists (obj_presup_slots_from_boundary i j).
        apply (Family.map_commutes _ j).
      + (* original hjf is equality judgement *)
        destruct i as [ [i' | ] | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists (Some (Some (obj_presup_slots_from_boundary i' j))).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (Some (Some j)). apply idpath.
        * (* i is LHS *)
          exists (Some (Some j)). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.
  
  (* TODO: move upstream, right to [Syntax] even? *)
  Definition Presup_of_Judgt_Bdry_Instance
      {Σ : signature σ} {jf} (jbi : Judgt_Bdry_Instance Σ jf)
    : family (judgement_total Σ).
  Proof.
    destruct jf as [ | hjf].
    - (* context judgement: no boundary *)
      apply Family.empty.
    - (* hyp judgement: presups are the context,
                        plus the slots of the hyp boundary *)
      apply Family.adjoin.
      + exists (Judgement.hypothetical_boundary hjf).
        intros i.
        exists (HJF (form_object ((Judgement.hypothetical_boundary hjf) i))).
        exists (pr1 jbi).
        intros j.
        set (p := Family.map_commutes (presup_slots_from_boundary i) j).
        set (j' := presup_slots_from_boundary i j) in *.
        destruct p.
        exact (pr2 jbi j').
      + exists (form_context).
        exact (pr1 jbi).
  Defined.

  (* TODO: move upstream to [TypingJudgements] *)
  (* TODO: consider making Signature_of_Type_Theory a coercion? *)
  (* TODO: consider naming conventions for types of the form “derivation of X from Y” *)
  (* TODO: think about use of “derivation” vs. “derivability”. *)
  (* TODO: should only depend on a *flat* type theory. *)
  Definition Derivation_Judgt_Bdry_Instance
      {Σ : Signature σ} (T : Raw_Type_Theory Σ)
      {jf} (jbi : Judgt_Bdry_Instance Σ jf)
      H
    : Type
  :=
    forall (i : Presup_of_Judgt_Bdry_Instance jbi),
      Derivation_from_Raw_TT T H (Presup_of_Judgt_Bdry_Instance _ i).

  (* TODO: upstream *)
  Definition extend {Σ : Signature σ} {a : Arity σ}
      (T : Raw_Type_Theory Σ) (A : algebraic_extension Σ a)
    : Raw_Type_Theory Σ.
  Proof.
  Admitted.
  
  (* TODO: upstream, maybe even into def of algebraic extension? *)
  (* TODO: rename [ae_arity_of_rule] to [ae_arity_for_rule] ? *)
  Definition ae_signature_for_rule {Σ : Signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
  := (Metavariable_Extension Σ (ae_arity_of_rule _ r)).

  (* TODO: upstream *)
  Definition ae_judgt_bdry_of_rule {Σ : Signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
    : Judgt_Bdry_Instance (ae_signature_for_rule r) (HJF (ae_hjf_of_rule _ r)).
  Proof.
    exists (ae_raw_context_of_rule _ r).
    apply (ae_hyp_bdry_of_rule).
  Defined.

  Definition is_well_typed_algebraic_extension
      {Σ : Signature σ} (T : Raw_Type_Theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    refine (Derivation_Judgt_Bdry_Instance _ (ae_judgt_bdry_of_rule r) _).
    + (* ambient type theory to typecheck premise [p] in *)
      admit.
    + (* open hypotheses to allow in the derivation *)
      admit.
  (* Roughly, we want to add the earlier rules of [A] to [T], and typecheck [r] over that.  There are (at least) three ways to do this:
    (1) take earlier rules just as judgements, and allow them as hypotheses in the derivation;
    (2) take earlier rules as judgements, then add rules to [T] giving these judgements as axioms;
    (3) actually give the extension of [T] by the preceding part of [A] as a type theory, i.e. turn rules of [A] into actual *rules*, with the variables of their contexts turned into term premises.  This option avoids extra use of the “cut” rule in derivations.

    In any case we must first translate [T] up to the extended signature of [R].

  (1) would nicely fit into the monadic view of derivations.
  (3) would nicely factorise into “take initial segment of an alg ext”, and “extend TT by an alg ext”.
  *)
  Admitted.

  Definition Is_Well_Typed_Rule
      {Σ : Signature σ} (T : Raw_Type_Theory Σ)
      {a} {hjf_concl}
      (R : rule Σ a hjf_concl)
    : Type.
  Proof.
    refine (is_well_typed_algebraic_extension T (premise R) * _).
    (* well-typedness of conclusion *)
    refine (Derivation_Judgt_Bdry_Instance _ (judgt_bdry_of_conclusion R) _).
    - admit.
    - admit.
    (* This should parallel [is_well_typed_algebraic_extension] above. *)
  Admitted.

End Welltypedness.<