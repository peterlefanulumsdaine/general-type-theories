Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.Theory.
Require Import WellFormed.Rule.
Require Import WellFormed.TypeTheory.

(** In this file: definition of well-typedness of a rule-spec, and a type-theory spec. *)

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
      {Σ : Signature σ} {jf} (jbi : Judgt_Bdry_Instance Σ jf)
    : family (Judgt_Instance Σ).
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
  (* TODO: consider making Signature_of_TT_Spec a coercion *)
  (* TODO: consider naming conventions for types of the form “derivation of X from Y” *)
  (* TODO: think about use of “derivation” vs. “derivability”. *)
  Definition Derivation_Judgt_Bdry_Instance
      (T : Type_Theory_Spec σ)
      {jf} (jbi : Judgt_Bdry_Instance (Signature_of_TT_Spec T) jf)
      H
    : Type
  :=
    forall (i : Presup_of_Judgt_Bdry_Instance jbi),
      Derivation_from_TT_Spec T H (Presup_of_Judgt_Bdry_Instance _ i).

  Definition Is_Well_Typed_Rule_Spec
      (T : Type_Theory_Spec σ)
      {a} {γ_concl} {hjf_concl}
      (R : Rule_Spec (Signature_of_TT_Spec T) a γ_concl hjf_concl)
    : Type.
  Proof.
     refine (_ * _).
    - (* well-typedness of premise boundaries *)
      admit.
      (* type-check each premise over the extension of [T] by rules for the earlier premises *)
    - (* well-typedness of conclusion boundaries *)
      (* simple refine (Derivation_Judgt_Bdry_Instance _ _). *)
      (* TODO: refactor type theories to have explicit signature component, so we can reuse metavariable extensions etc. *)
      admit.
      (* type-check conclusion over extension by rules for all premises *)
  Admitted.

End Welltypedness.