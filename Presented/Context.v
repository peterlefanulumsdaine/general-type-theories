(** The aim of this module: 

- develop and export a definition of _sequential context_;
- compare it with some alternate definitions

The treatment of alternative definitions roughly follows that given in the (draft) appendix to the paper, considering a subset of the definitions considered there.

*)

(* NOTE: probably the two goals — developing one definition for use in the main development, and comparing alternative definitions — should eventually be separated into different files. *)

Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.

Section Fix_Shape_System.

Context {σ : shape_system}.

Section Inductive_Predicate.
(** One approach: sequential well-formed contexts are defined directly, by a proof-relevant inductive predicate on flat raw contexts, looking like the standard well-formed context judgement *)

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Inductive wf_context_derivation : raw_context Σ -> Type
  :=
    | wf_context_empty
      : wf_context_derivation Context.empty
    | wf_context_extend
        {Γ} (d_Γ : wf_context_derivation Γ)
        {A} (d_A : FlatTypeTheory.derivation T [<>]
                    [! Γ |- A !])
     : wf_context_derivation (Context.extend Γ A).

  Local Definition length_of_wf_derivation
    {Γ} (d_Γ : wf_context_derivation Γ)
    : nat.
  Proof.
    induction d_Γ as [ | ? ? n].
    - exact O.
    - exact (S n).
  Defined.

End Inductive_Predicate.

Section Inductive_By_Length.

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Definition wf_context_of_length_with_flattening (n : nat)
    : { X : Type & X -> raw_context Σ }.
  Proof.
    induction n as [ | n' X_f].
    - exists Unit.
      intros _; exact Context.empty.
    - set (X := pr1 X_f); set (f := pr2 X_f).
      exists { Γ : X & {A : _
        & FlatTypeTheory.derivation T [<>] [! f Γ |- A !] }}.
      intros Γ_A_dA.
      exact (Context.extend (f (pr1 Γ_A_dA)) (pr1 (pr2 Γ_A_dA))).
  Defined.

  Definition wf_context_of_length (n : nat) : Type
  := pr1 (wf_context_of_length_with_flattening n).

  Local Definition flatten {n : nat}
    : wf_context_of_length n -> raw_context Σ
  := pr2 (wf_context_of_length_with_flattening n).

  Local Definition wf_context_of_length_empty
    : wf_context_of_length 0
  := tt.

  Local Definition wf_context_of_length_extend
      {n} (Γ : wf_context_of_length n)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [! flatten Γ |- A !])
    : wf_context_of_length (S n)
  := (Γ;(A;d_A)).

End Inductive_By_Length.

Arguments wf_context_of_length_with_flattening : simpl nomatch.
Arguments wf_context_of_length : simpl nomatch.
Arguments flatten {Σ T n} Γ : simpl nomatch.

Section Inductive_By_Length_vs_Inductive_Predicate.

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Definition wf_context_of_length_is_wf {n : nat}
      (Γ : wf_context_of_length T n)
    : wf_context_derivation T (flatten Γ).
  Proof.
    revert Γ. induction n as [ | n' IH].
    - intros ?; apply wf_context_empty.
    - intros [Γ [A d_A]].
      apply wf_context_extend.
      + apply IH.
      + apply d_A.
  Defined.

  Definition wf_context_of_length_from_wf_derivation
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : { Γ_wf : wf_context_of_length T (length_of_wf_derivation _ d_Γ)
      & flatten Γ_wf = Γ }.
  Proof.
    induction d_Γ as [ | Δ d_Δ [Δ_wf e_Δ] A d_A].
    - exists (wf_context_of_length_empty _).
      apply idpath.
    - simple refine (_;_). 
      + srapply wf_context_of_length_extend.
        * exact Δ_wf.
        * exact (transport
            (fun (Θ : raw_context _) => raw_type Σ Θ) (e_Δ^) A).
        * exact (transportD _
            (fun Θ B => FlatTypeTheory.derivation _ _ [! Θ |- B !])
            (e_Δ^) _ d_A).
      + rapply (ap011D _ e_Δ). exact (transport_pV _ e_Δ _).
  Defined.

  Local Theorem weq_inductive_by_length_by_inductive_predicate
    : { n : nat & wf_context_of_length T n}
    <~> { Γ : raw_context Σ & wf_context_derivation T Γ }.
  Proof.
    srapply equiv_adjointify.
    - intros [n Γ].
      exists (flatten Γ).
      apply wf_context_of_length_is_wf.
    - intros [Γ d_Γ].
      exists (length_of_wf_derivation _ d_Γ).
      apply wf_context_of_length_from_wf_derivation.
    - intros [Γ d_Γ].
      induction d_Γ as [ | Δ d_Δ IH A d_A].
      { apply idpath. }
      simpl in IH.
      srapply path_sigma.
      + admit.
      + admit.
    - intros [n Γ].
      induction n as [ | n IH].
      { destruct Γ. apply idpath. }
      destruct Γ as [Γ' [A d_A]].
      specialize (IH Γ'). simpl in IH.
      srapply path_sigma.
      { apply (ap S), (ap pr1 IH). }
      simpl.
      (* TODO: lemma [transport_wf_context_of_length_extend] *)
      admit.
  Admitted.

End Inductive_By_Length_vs_Inductive_Predicate.

End Fix_Shape_System.
