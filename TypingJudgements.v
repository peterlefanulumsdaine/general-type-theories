Require Import HoTT.
Require Import ShapeSystems.
Require Import DeductiveClosure.
Require Import Family.
Require Import RawSyntax.
Require Import RawTypeTheories.
Require Import StandardRawRules.

Section Derivability_from_Raw_TT.
(* TODO: this section could be moved into RawTypeTheories.v, if only the context cc’s were also upstreamed so this didn’t depend on StandardRawRules.v.  Consider this? *)

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  Definition CCs_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Family (closure_condition (Judgt_Instance Σ)).
  Proof.
    refine (Family.Sum (context_ccs Σ) _).
    exact (Family.Bind T CCs_of_RR).
  Defined.

  Definition Derivation_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Judgt_Instance Σ -> Type
  := Derivation (CCs_from_Raw_TT T).
  
End Derivability_from_Raw_TT.

Section Derivability_from_TT_Spec.

  Context {σ : Shape_System}.

  Definition Signature_of_TT_Spec (T : Type_Theory_Spec σ)
    : Signature σ.
  Proof.
    (* symbols are given by the object-judgement rules of T *)
    exists {r : TTS_Rule _ T & is_obj_HJF (TTS_hjf_of_rule _ _ r)}.
    intros [r Hr].
    set (hjf := TTS_hjf_of_rule _ _ r) in *; clearbody hjf.
    destruct hjf as [ cl | cl ].
    - (* when r is an object rule, the class and arity of its symbol are those of r itself: *)
      exact (cl, TTS_arity_of_rule _ _ r).
    - destruct Hr. (* by assumption, r cannot be an equality rule *)
  Defined.

  Definition Raw_TT_of_TT_Spec (T : Type_Theory_Spec σ)
    : Raw_Type_Theory (Signature_of_TT_Spec T).
  (* TODO: downstream, since this needs to add in the standard raw rules.  Possibly also downstream [Signature_of_TT_Spec]. *)
  Admitted.

End Derivability_from_TT_Spec.

(*
a judgement is well-typed: relative to a collection of raw rules in its signature [add context extension, & translate raw rules into cc’s]  
a rule is well-typed: relative to a collection of raw rules in its signature


tt_spec
-> raw_tt
-> derivability relations
*)

