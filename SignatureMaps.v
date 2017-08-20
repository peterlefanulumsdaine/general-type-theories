Require Import HoTT.
Require Import Family.
Require Import ShapeSystems.
Require Import Coproduct.
Require Import RawSyntax.

Section Signature_Maps.

  Context {σ : Shape_System}.
 
  Definition Signature_Map (Σ Σ' : Signature σ) : Type.
  Admitted.

  Definition Fmap_Raw_Syntax {Σ Σ'} (f : Signature_Map Σ Σ')
      {cl} {γ}
    : Raw_Syntax Σ cl γ -> Raw_Syntax Σ' cl γ.
  Admitted.

  Definition Fmap_Raw_Context {Σ Σ'} (f : Signature_Map Σ Σ')
    : Raw_Context Σ -> Raw_Context Σ'.
  Proof.
    intros Γ.
    exists (Proto_Context_of_Raw_Context Γ).
    intros i. refine (_ (var_type_of_Raw_Context Γ i)).
    apply (Fmap_Raw_Syntax f).
  Defined.

  Definition Fmap_Hyp_Judgt_Bdry_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Hyp_Judgt_Bdry_Instance Σ hjf γ -> Hyp_Judgt_Bdry_Instance Σ' hjf γ.
  Proof.
  Admitted.

  Definition Fmap_Hyp_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Hyp_Judgt_Form_Instance Σ hjf γ -> Hyp_Judgt_Form_Instance Σ' hjf γ.
  Proof.
  Admitted.

End Signature_Maps.
