Require Import HoTT.
Require Import ShapeSystems.
Require Import Family.
Require Import RawSyntax.
Require Import RawTypeTheories.
Require Import TypingJudgements.

(** In this file: definition of well-typedness of a rule-spec, and a type-theory spec. *)

Section Welltypedness.

  Context {σ : Shape_System}.

  (* TODO: move upstream! *)
  Definition Build_Family_Map' {X} {K L : Family X}
    : (forall i:K, {j:L & L j = K i})
      -> Family_Map K L.
  Proof.
    intros f.
    exists (fun i => pr1 (f i)).
    intros i; exact (pr2 (f i)).
  Defined.

  Arguments Hyp_Obj_Judgt_Bdry_Slots : simpl nomatch.
  Arguments Hyp_Judgt_Bdry_Slots : simpl nomatch.

  (* TODO: move upstream; consider name! *)
  (* This is the special case of [presup_slots_from_boundary] for object judgements.
    It is abstracted out because it’s used twice: directly for object judgements, and as part of the case for equality judgements.
    In fact it’s almost trivial, so could easily be inlined; but conceptually it is the same thing both times, and in type theory with more judgements, it could be less trivial, so we keep it factored out. *)
  Definition obj_presup_slots_from_boundary
    {cl : Syn_Class} (i : Hyp_Obj_Judgt_Bdry_Slots cl)
    : Family_Map
        (Hyp_Obj_Judgt_Bdry_Slots (Hyp_Obj_Judgt_Bdry_Slots cl i))
        (Hyp_Obj_Judgt_Bdry_Slots cl).
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
    {hjf : Hyp_Judgt_Form} (i : Hyp_Judgt_Bdry_Slots hjf)
    : Family_Map
        (Hyp_Judgt_Form_Slots (obj_HJF (Hyp_Judgt_Bdry_Slots hjf i)))
        (Hyp_Judgt_Bdry_Slots hjf).
  Proof.
    apply Build_Family_Map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct hjf as [ cl | cl ].
      + (* original hjf is object judgement *)
        exists (obj_presup_slots_from_boundary i j).
        apply (commutes_Family_Map _ j).
      + (* original hjf is equality judgement *)
        destruct i as [ [i' | ] | ].
        * (* i is in shared bdry of LHS/RHS *)   
          cbn in j.
          exists (Some (Some (obj_presup_slots_from_boundary i' j))).
          apply (commutes_Family_Map _ j).
        * (* i is RHS *)
          exists (Some (Some j)). apply idpath.
        * (* i is LHS *)
          exists (Some (Some j)). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.
  
  (* TODO: move upstream, right to [RawSyntax] even? *)
  Definition presups_of_judgt_bdry_instance
      {Σ : Signature σ} {jf} (jbi : Judgt_Bdry_Instance Σ jf)
    : Family (Judgt_Instance Σ).
  Proof.
    destruct jf as [ | hjf].
    - (* context judgement: no boundary *)
      apply Empty_family.
    - (* hyp judgement: presups are the context,
                        plus the slots of the hyp boundary *)
      apply Snoc.
      + exists (Hyp_Judgt_Bdry_Slots hjf).
        intros i.
        exists (HJF (obj_HJF ((Hyp_Judgt_Bdry_Slots hjf) i))).
        exists (pr1 jbi).
        intros j.
        set (p := commutes_Family_Map (presup_slots_from_boundary i) j).
        set (j' := presup_slots_from_boundary i j) in *.
        destruct p.
        exact (pr2 jbi j').
      + exists (Cxt_JF).
        exact (pr1 jbi).
  Defined.

  (* TODO: move upstream to [TypingJudgements] *)
  (* TODO: consider making Signature_of_TT_Spec a coercion *)
  Definition Derivation_Judgt_Bdry_Instance
      (T : Type_Theory_Spec σ)
      {jf} (jbi : Judgt_Bdry_Instance (Signature_of_TT_Spec T) jf)
    : Type.
  Proof.
    (* go from a judgement boundary instance to a family of judgements (the actual presuppositions) and then ask these all to be derivable over T *)
  Admitted.

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
      admit.
      (* type-check conclusion over extension by rules for all premises *)
  Admitted.

End Welltypedness.