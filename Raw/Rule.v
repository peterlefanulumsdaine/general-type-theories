Section Raw_Rules.

  Context {σ : shape_system}.
  Context (Σ : Signature σ).

  Record Raw_Rule
  :=
    { RR_metas : Arity _
    ; RR_prem : family (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    ; RR_concln : (Judgt_Instance (Metavariable_Extension Σ RR_metas))
    }.

  Definition CCs_of_RR (R : Raw_Rule)
    : Closure.system (Judgt_Instance Σ).
  Proof.
    exists { Γ : Raw_Context Σ & Instantiation (RR_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Family.fmap _ (RR_prem R)).
      apply (instantiate_ji I).
    - apply (instantiate_ji I).
      apply (RR_concln R).
  Defined.

  Definition Raw_Type_Theory := family Raw_Rule.

End Raw_Rules.

Arguments CCs_of_RR {_ _} _.

