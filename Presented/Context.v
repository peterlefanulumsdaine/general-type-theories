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

(* for based on inductive scheme A:

- look at both maps as maps of A-structures;
- f(g(EXT_A(x)) = f(EXT_B(g(x)) = EXT_A(f(g(x))) = EXT_A(x);
- so want lemmas about commutation of f, g with EXT_A, EXT_B
- for each of f, g: one of the lemmas will be a computation rule, the other will need to be given
- specifically:
   for wf_context_of_length_from_wf_derivation,
   lemma should say how it acts on a conrtext-of-length style extension;
  OH!  But that one isn’t quite hte same induction-principle style.  Hmm!
- well, other direction:
   for wf_context_of_length_is_wf,
   lemma should say how it acts on a wf_contet_of_length_extend?
  but that IS automatic!  Peculiar…
*)

  Local Lemma wf_deriv_of_col_of_deriv
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : wf_context_derivation T Γ.
  Proof.
    rapply transport.
    2: { rapply wf_context_of_length_is_wf.
         refine (pr1 (wf_context_of_length_from_wf_derivation _)).
         eassumption.
    }
    refine (pr2 (wf_context_of_length_from_wf_derivation _)).
  Defined.

  Local Lemma transport_wf_derivation
        {Γ} (d_Γ : wf_context_derivation T Γ)
        {Γ'} (e_Γ : Γ = Γ')
        {A} (d_A : FlatTypeTheory.derivation T [<>] [! Γ |- A !])
        {A'} (e_A : transport (fun (Θ : raw_context _) => raw_type _ Θ) e_Γ A = A') 
    : 
    transport (wf_context_derivation T)
        (ap011D Context.extend e_Γ e_A)
        (wf_context_extend T d_Γ d_A)
    = wf_context_extend T
        (transport (wf_context_derivation T) e_Γ d_Γ)
        (transport _ e_A
          (transportD (fun Θ : raw_context Σ => raw_type Σ Θ)
                    (fun (Θ : raw_context Σ) (B : raw_type Σ Θ) =>
           FlatTypeTheory.derivation T [<>] [!Θ |- B!])
                    e_Γ _ d_A)).
  Proof.
    destruct e_Γ; destruct e_A; cbn. apply idpath.
  Qed.

  (* TODO: upstream *)
  Lemma transportD_pV
     {A} {B} (C : forall a : A, B a -> Type)
     {x1 x2 : A} (e_x : x1 = x2)
     (y : B x2) (z  : C x2 y)
   : transportD B C e_x _ (transportD B C (e_x^) y z)
     = transport _ (transport_pV _ _ _)^ z.
  Proof.
    destruct e_x; apply idpath.
  Defined.

  Local Lemma wf_deriv_of_col_of_deriv_eq
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : wf_deriv_of_col_of_deriv d_Γ = d_Γ.
  Proof.
    induction d_Γ as [ | Δ d_Δ IH A d_A].
    - apply idpath.
    - unfold wf_deriv_of_col_of_deriv.
      simpl.
      eapply concat. { apply transport_wf_derivation. }
      apply (ap2 (fun d_Θ d_B => wf_context_extend T d_Θ d_B)).
      { apply IH. }
      set (e := wf_context_of_length_from_wf_derivation d_Δ).
      clearbody e.
      destruct e as [Γ_wf e_ΓΔ].
      eapply concat. { apply ap. rapply transportD_pV. }
      apply (transport_pV (fun B : raw_type Σ Δ =>
     FlatTypeTheory.derivation T [<>] [!Δ |- B!])).
  Defined.

  (* TODO:consider naming *)
  Local Lemma nat_wf_eta_expand
    (nΓ : { n : nat & wf_context_of_length T n})
    :  { n : nat & wf_context_of_length T n}.
  Proof.
    destruct nΓ as [[ | n'] Γ].
    - exists O; exact tt.
    - destruct Γ as [Γ' [A d_A]].
      exists (S n'). 
      exact (wf_context_of_length_extend _ Γ' d_A).
  Defined.

  (* TODO:consider naming *)
  Local Lemma nat_wf_eta_eq
    (nΓ : { n : nat & wf_context_of_length T n})
    : nat_wf_eta_expand nΓ = nΓ.
  Proof.
    destruct nΓ as [[ | n'] Γ]; destruct Γ; apply idpath.
  Defined.

  (* TODO:consider naming *)
  Local Lemma nat_wf_extend_eq
      {n} (Γ : wf_context_of_length T n)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [! flatten Γ |- A !])
      {n'} (Γ' : wf_context_of_length T n')
      {A'} (d_A' : FlatTypeTheory.derivation T [<>] [! flatten Γ' |- A' !])
      (e_n : (n;Γ) = (n';Γ'))
    : (S n; wf_context_of_length_extend _ Γ d_A)
    = (S n'; wf_context_of_length_extend _ Γ' d_A').
  Proof.
  Admitted.

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
      srapply path_sigma.
      + refine ((wf_context_of_length_from_wf_derivation _).2).
      + apply wf_deriv_of_col_of_deriv_eq.
    - intros [n Γ].
      induction n as [ | n IH].
      { destruct Γ. apply idpath. }
      destruct Γ as [Γ' [A d_A]].
      specialize (IH Γ'). simpl in IH.
      simpl.
      srapply path_sigma.
      { apply (ap S), (ap pr1 IH). }
      simpl.
      eapply concat. { apply inverse, transport_compose. }
      simpl.
      eapply concat.
      { refine (@transport_sigma _ _
           (fun n (Γ : wf_context_of_length T n) => _) _ _ _ _). }
      
      (* TODO: lemma [transport_wf_context_of_length_extend] *)
      admit.
  Admitted.

End Inductive_By_Length_vs_Inductive_Predicate.

End Fix_Shape_System.
