Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.

(* TODO: Might it make more sense to fold these in through [Syntax], so that each construction’s functoriality lemmas can be given with the construction itself? *)

Section Signature_Maps.

  Context {σ : shape_system}.
 
  Definition Signature_Map (Σ Σ' : signature σ) : Type
    := Family.map Σ Σ'.

  Definition Family_Map_of_Signature_Map {Σ Σ'}
    : Signature_Map Σ Σ' -> Family.map Σ Σ'
  := idmap.
  Coercion Family_Map_of_Signature_Map : Signature_Map >-> Family.map.

  Definition Fmap_Raw_Syntax {Σ Σ'} (f : Signature_Map Σ Σ')
      {cl} {γ}
    : raw_expression Σ cl γ -> raw_expression Σ' cl γ.
  Proof.
    intros t. induction t as [ γ i | γ S ts fts].
    - exact (raw_variable i).
    - refine (transport (fun cl => raw_expression _ cl _) _ (raw_symbol (f S) _)).
      + exact (ap fst (Family.map_commutes _ _)).
      + refine (transport
          (fun a : arity σ => forall i : a,
               raw_expression Σ' (argument_class i) (shape_sum γ (argument_shape i)))
          _
          fts).
        exact ((ap snd (Family.map_commutes _ _))^).
  Defined.

  Definition Fmap_Raw_Context {Σ Σ'} (f : Signature_Map Σ Σ')
    : raw_context Σ -> raw_context Σ'.
  Proof.
    intros Γ.
    exists (raw_context_carrier Γ).
    intros i. refine (_ (raw_context_type Γ i)).
    apply (Fmap_Raw_Syntax f).
  Defined.

  Definition Fmap_Hyp_Judgt_Bdry_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Judgement.hypothetical_boundary Σ hjf γ -> Judgement.hypothetical_boundary Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Fmap_Raw_Syntax f), hjbi.
  Defined.

  Definition Fmap_Hyp_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : hypothetical_judgement Σ hjf γ -> hypothetical_judgement Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Fmap_Raw_Syntax f), hjbi.
  Defined.

  Definition Fmap_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {jf}
    : judgement Σ jf -> judgement Σ' jf.
  Proof.
    destruct jf as [ | hjf].
    - apply Fmap_Raw_Context, f.
    - cbn. intros Γ_hjfi.
      exists (Fmap_Raw_Context f Γ_hjfi.1).
      exact (Fmap_Hyp_Judgt_Form_Instance f Γ_hjfi.2).
  Defined.

  Definition Fmap_Judgt_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
    : judgement_total Σ -> judgement_total Σ'.
  Proof.
    intros jf_jfi.
    exists jf_jfi.1.
    exact (Fmap_Judgt_Form_Instance f jf_jfi.2).
  Defined.

  (* Metavariable extensions are bifunctorial in their two arguments.

   We give the general bifunctoriality action as [Fmap_Family], and the special cases in each argument individually as [Fmap1], [Fmap2]. *)
  Definition Fmap_Metavariable_Extension
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      {a a' : arity σ} (g : Family.map a a')
    : Signature_Map (Metavariable.extend Σ a)
                    (Metavariable.extend Σ' a').
  Proof.
    apply Family.map_sum.
    - apply f.
    - apply Family.map_fmap, g.
  Defined.

  Definition Fmap1_Metavariable_Extension
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      (a : arity σ)
    : Signature_Map (Metavariable.extend Σ a)
                    (Metavariable.extend Σ' a)
  := Fmap_Metavariable_Extension f (Family.idmap _).

  Definition Fmap2_Metavariable_Extension
      (Σ : signature σ)
      {a a' : arity σ} (f : Family.map a a')
    : Signature_Map (Metavariable.extend Σ a)
                    (Metavariable.extend Σ a')
  := Fmap_Metavariable_Extension (Family.idmap _) f.

  Definition Fmap_Raw_Rule {Σ Σ'} (f : Signature_Map Σ Σ')
    : flat_rule Σ -> flat_rule Σ'.
  Proof.
    intros R.
    exists (flat_rule_metas _ R).
    - refine (Family.fmap _ (flat_rule_premises _ R)).
      apply Fmap_Judgt_Instance.
      apply Fmap1_Metavariable_Extension, f.
    - refine (Fmap_Judgt_Instance _ (flat_rule_conclusion _ R)).
      apply Fmap1_Metavariable_Extension, f.
  Defined.

  Definition fmap_flat_type_theory {Σ Σ'} (f : Signature_Map Σ Σ')
    : flat_type_theory Σ -> flat_type_theory Σ'.
  Proof.
    apply Family.fmap, Fmap_Raw_Rule, f.
  Defined.

End Signature_Maps.

