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

Section Auxiliary.

  Lemma transportD_pV
     {A} {B} (C : forall a : A, B a -> Type)
     {x1 x2 : A} (e_x : x1 = x2)
     (y : B x2) (z  : C x2 y)
   : transportD B C e_x _ (transportD B C (e_x^) y z)
     = transport _ (transport_pV _ _ _)^ z.
  Proof.
    destruct e_x; apply idpath.
  Defined.

End Auxiliary.

Section Fix_Shape_System.

Context {σ : shape_system}.

Section Inductive_Predicate.
(** One approach: sequential well-formed contexts are defined directly, by a proof-relevant inductive predicate on flat raw contexts, looking like the standard well-formed context judgement *)
(* Code: [indpred].
TODO: systematically use this code in definitions to disambiguate from other approaches *)

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

Arguments wf_context_extend {Σ T Γ} d_Γ {A} d_A.
Arguments length_of_wf_derivation {Σ T Γ} d_Γ.

Section Induction_By_Length.
(* code: "ibl" *)

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Local Definition ibl_zero_step : { X : Type & X -> raw_context Σ }.
  Proof.
    exists Unit.
    intros _; exact Context.empty.
  Defined.

  Local Definition ibl_succ_step (X_f : { X : Type & X -> raw_context Σ })
    : { X : Type & X -> raw_context Σ }.
  Proof.
    set (X := pr1 X_f); set (f := pr2 X_f).
    exists { Γ : X & {A : _
        & FlatTypeTheory.derivation T [<>] [! f Γ |- A !] }}.
    intros Γ_A_dA.
    exact (Context.extend (f (pr1 Γ_A_dA)) (pr1 (pr2 Γ_A_dA))).
  Defined.

  Definition ibl_extend_internal (X_f : { X : Type & X -> raw_context Σ })
      (Γ : X_f.1)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [! X_f.2 Γ |- A !])
    : (ibl_succ_step X_f).1
  := (Γ;(A;d_A)).

  Definition wf_context_ibl_with_flattening (n : nat)
    : { X : Type & X -> raw_context Σ }.
  Proof.
    induction n as [ | n' X_f].
    - exact ibl_zero_step.
    - exact (ibl_succ_step X_f).
  Defined.

  Definition wf_context_ibl (n : nat) : Type
  := pr1 (wf_context_ibl_with_flattening n).

  Local Definition ibl_flatten {n : nat}
    : wf_context_ibl n -> raw_context Σ
  := pr2 (wf_context_ibl_with_flattening n).

  Definition wf_context_ibl_empty
    : wf_context_ibl 0
  := tt.

  Definition ibl_extend
      {n} (Γ : wf_context_ibl n)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [! ibl_flatten Γ |- A !])
    : wf_context_ibl (S n)
  := ibl_extend_internal _ Γ d_A.

End Induction_By_Length.

Arguments ibl_zero_step Σ : clear implicits.
Arguments wf_context_ibl_with_flattening : simpl nomatch.
Arguments wf_context_ibl : simpl nomatch.
Arguments ibl_flatten {Σ T n} Γ : simpl nomatch.

Section Induction_By_Length_vs_Inductive_Predicate.

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Local Definition wf_context_ibl_is_wf {n : nat}
      (Γ : wf_context_ibl T n)
    : wf_context_derivation T (ibl_flatten Γ).
  Proof.
    revert Γ. induction n as [ | n' IH].
    - intros ?; apply wf_context_empty.
    - intros [Γ [A d_A]].
      apply wf_context_extend.
      + apply IH.
      + apply d_A.
  Defined.

  Local Definition wf_context_ibl_from_wf_derivation
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : { Γ_wf : wf_context_ibl T (length_of_wf_derivation d_Γ)
      & ibl_flatten Γ_wf = Γ }.
  Proof.
    induction d_Γ as [ | Δ d_Δ [Δ_wf e_Δ] A d_A].
    - exists (wf_context_ibl_empty _).
      apply idpath.
    - simple refine (_;_). 
      + srapply ibl_extend.
        * exact Δ_wf.
        * exact (transport
            (fun (Θ : raw_context _) => raw_type Σ Θ) (e_Δ^) A).
        * exact (transportD _
            (fun Θ B => FlatTypeTheory.derivation _ _ [! Θ |- B !])
            (e_Δ^) _ d_A).
      + rapply (ap011D _ e_Δ). exact (transport_pV _ e_Δ _).
  Defined.

  Local Lemma transport_wf_context_extend
        {Γ} (d_Γ : wf_context_derivation T Γ)
        {Γ'} (e_Γ : Γ = Γ')
        {A} (d_A : FlatTypeTheory.derivation T [<>] [! Γ |- A !])
        {A'} (e_A : transport (fun (Θ : raw_context _) => raw_type _ Θ) e_Γ A = A') 
    : 
    transport (wf_context_derivation T)
        (ap011D Context.extend e_Γ e_A)
        (wf_context_extend d_Γ d_A)
    = wf_context_extend
        (transport (wf_context_derivation T) e_Γ d_Γ)
        (transport _ e_A
          (transportD (fun Θ : raw_context Σ => raw_type Σ Θ)
                    (fun (Θ : raw_context Σ) (B : raw_type Σ Θ) =>
           FlatTypeTheory.derivation T [<>] [!Θ |- B!])
                    e_Γ _ d_A)).
  Proof.
    destruct e_Γ; destruct e_A; cbn. apply idpath.
  Qed.

  Local Lemma wf_deriv_of_col_of_deriv_eq
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : transport (wf_context_derivation T)
        (wf_context_ibl_from_wf_derivation d_Γ).2
        (wf_context_ibl_is_wf
          (wf_context_ibl_from_wf_derivation d_Γ).1)
      = d_Γ.
  Proof.
    induction d_Γ as [ | Δ d_Δ IH A d_A].
    - apply idpath.
    - simpl.
      eapply concat. { apply transport_wf_context_extend. }
      apply (ap2 (fun d_Θ d_B => wf_context_extend d_Θ d_B)).
      { apply IH. }
      set (e := wf_context_ibl_from_wf_derivation d_Δ).
      clearbody e.
      destruct e as [Γ_wf e_ΓΔ].
      eapply concat. { apply ap. rapply transportD_pV. }
      apply (transport_pV (fun B : raw_type Σ Δ =>
     FlatTypeTheory.derivation T [<>] [!Δ |- B!])).
  Defined.

  Local Fixpoint length_of_wf_deriv_of_col
      {n} (Γ_wf : wf_context_ibl T n)
      {struct n}
    : length_of_wf_derivation (wf_context_ibl_is_wf Γ_wf)
    = n.
  Proof.
    destruct n as [ | n].
    { apply idpath. }
    simpl. apply (ap S). apply length_of_wf_deriv_of_col.
  Defined.

  Local Lemma ibl_flatten_transport
      {n n'} (e_n : n = n')
      (Γ : wf_context_ibl T n)
    : ibl_flatten (transport _ e_n Γ) = ibl_flatten Γ.
  Proof.
    destruct e_n; apply idpath.
  Defined.

  Local Lemma transport_ibl_extend_aux
      {n n'} (e_n : n = n')
      {Γ : wf_context_ibl T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (ibl_flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!ibl_flatten Γ |- A!])
      (e_aux := (ap011D Context.extend ((ibl_flatten_transport e_n Γ)^ @ ap ibl_flatten e_Γ)
                        1%path)
                 : ibl_flatten (ibl_extend T Γ d_A)
                = ibl_flatten (ibl_extend T _ _))
    : { e : transport (wf_context_ibl T) (ap S e_n)
                (ibl_extend _ Γ d_A)
          = ibl_extend _ Γ'
              (transportD _ (fun Θ B => FlatTypeTheory.derivation T [<>] [! Θ |- B !])
                          ((ibl_flatten_transport e_n Γ)^ @ ap ibl_flatten e_Γ) _ d_A)
      & ap ibl_flatten e = ibl_flatten_transport _ _ @ e_aux }.
  Proof.
    destruct e_n; destruct e_Γ; simpl in *.
    exists 1%path. apply 1%path.
  Qed.

  Local Definition transport_ibl_extend
      {n n'} (e_n : n = n')
      {Γ : wf_context_ibl T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (ibl_flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!ibl_flatten Γ |- A!])
    : _ = _
  := (transport_ibl_extend_aux e_n e_Γ d_A).1.

  Local Definition flatten_transport_ibl_extend
      {n n'} (e_n : n = n')
      {Γ : wf_context_ibl T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (ibl_flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!ibl_flatten Γ |- A!])
    : ap ibl_flatten (transport_ibl_extend e_n e_Γ d_A) = _
  := (transport_ibl_extend_aux e_n e_Γ d_A).2.

  Local Lemma col_of_deriv_of_col_eq
      {n} (Γ_wf : wf_context_ibl T n)
    : { e : transport (wf_context_ibl T)
         (length_of_wf_deriv_of_col Γ_wf)
         (wf_context_ibl_from_wf_derivation
                      (wf_context_ibl_is_wf Γ_wf)).1
            = Γ_wf
      & ap ibl_flatten e
        = (ibl_flatten_transport _ _)
        @ (wf_context_ibl_from_wf_derivation _).2 }.
  Proof.
    induction n as [ | n IH].
    { destruct Γ_wf. srapply exist; apply idpath. }
    destruct Γ_wf as [Δ_wf [A d_A]].
    specialize (IH Δ_wf). simpl length_of_wf_deriv_of_col in *.
    set (e := length_of_wf_deriv_of_col Δ_wf) in *; clearbody e.
    destruct IH as [e_Γ flatten_e_Γ].
    srapply exist.
    - simpl.
      eapply concat.
      { rapply transport_ibl_extend. apply e_Γ. }
      apply (ap (fun AdA => (Δ_wf ; AdA))).
      eapply concat.
      { refine (transport_sigma ((ibl_flatten_transport _ _)^ @ _) (_;_))^. }
      eapply concat.
      { refine (ap _ (transport_sigma 
                   ((wf_context_ibl_from_wf_derivation _).2)^ (_;_))^). }
      eapply concat. { apply inverse. rapply transport_pp. }
      refine (@ap _ _ (fun p => transport _ p (A;d_A)) _ 1%path _).
      eapply concat. { apply ap, ap, flatten_e_Γ. }
      eapply concat. { apply ap, concat_V_pp. }
      apply concat_Vp.
    - eapply concat. { apply ap_pp. }
      eapply concat.
      { eapply (ap_1back concat),
               flatten_transport_ibl_extend.
      }
      admit.
  Admitted.

  Local Theorem weq_induction_by_length_vs_by_inductive_predicate
    : { n : nat & wf_context_ibl T n}
    <~> { Γ : raw_context Σ & wf_context_derivation T Γ }.
  Proof.
    srapply equiv_adjointify.
    - intros [n Γ].
      exists (ibl_flatten Γ).
      apply wf_context_ibl_is_wf.
    - intros [Γ d_Γ].
      exists (length_of_wf_derivation d_Γ).
      apply wf_context_ibl_from_wf_derivation.
    - intros [Γ d_Γ].
      srapply path_sigma.
      + refine ((wf_context_ibl_from_wf_derivation _).2).
      + apply wf_deriv_of_col_of_deriv_eq.
    - intros [n Γ].
      rapply path_sigma.
      { apply col_of_deriv_of_col_eq.
      }
  Defined.

End Induction_By_Length_vs_Inductive_Predicate.

Section Inductive_Family_By_Length.
(** A slightly unnatural definition, introduced in hope it may facilitate the equivalence between the by-induction-on-length definition and the definitions as inductive types/families. *)
(* Code: “ifbl”, to be used consistently in definitions/comparisons. *)
 
  Context {Σ : signature σ} (T : flat_type_theory Σ).


  Inductive wf_context_ifbl_zero_step : raw_context Σ -> Type
  := wf_context_ifbl_empty : wf_context_ifbl_zero_step Context.empty.

  Inductive wf_context_ifbl_succ_step (X : raw_context Σ -> Type)
    : raw_context Σ -> Type
  := | wf_context_ifbl_extend_internal {Γ} (Γ_wf : X Γ)
       {A} (d_A : FlatTypeTheory.derivation T [<>] [! Γ |- A !])
     : wf_context_ifbl_succ_step X (Context.extend Γ A).

  Fixpoint wf_context_ifbl (n : nat) : raw_context Σ -> Type.
  Proof.
    destruct n as [ | n'].
    - exact wf_context_ifbl_zero_step.
    - exact (wf_context_ifbl_succ_step (wf_context_ifbl n')).
  Defined.

  Local Definition ifbl_extend {n} {Γ}
      (Γ_wf : wf_context_ifbl n Γ)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [!Γ |- A!])
    : wf_context_ifbl (S n) (Context.extend Γ A)
  := wf_context_ifbl_extend_internal _ Γ_wf d_A.

  Arguments ifbl_extend : simpl never.

  Local Definition transport_ifbl_extend
      {n n'} (e_n : n = n')
      {Γ} (Γ_wf : wf_context_ifbl n Γ)
      {A} (d_A : FlatTypeTheory.derivation T [<>] [!Γ |- A!])
    : transport (fun n => wf_context_ifbl n _)
                (ap S e_n) (ifbl_extend Γ_wf d_A)
      = ifbl_extend (transport (fun n => wf_context_ifbl n _) e_n Γ_wf) d_A.
  Proof.
    destruct e_n; apply idpath.
  Defined.

End Inductive_Family_By_Length.

Arguments wf_context_ifbl_zero_step Σ : clear implicits.

Section Inductive_Predicate_vs_Inductive_Family_By_Length.
(* "indpred" vs "ifbl" *)
  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Local Definition indpred_from_ifbl {n} {Γ}
      (Γ_wf : wf_context_ifbl T n Γ)
    : wf_context_derivation T Γ.
  Proof.
    revert Γ Γ_wf. induction n as [ | n' IH].
    - intros Γ Γ_wf; destruct Γ_wf.
      apply wf_context_empty.
    - intros Γ Γ_wf; destruct Γ_wf as [Γ' Γ'_wf A d_A].
      apply wf_context_extend; auto.
  Defined.

  Local Definition ifbl_from_indpred
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : wf_context_ifbl T (length_of_wf_derivation d_Γ) Γ.
  Proof.
    induction d_Γ as [ | Δ d_Δ Δ_wf A d_A].
    - apply wf_context_ifbl_empty.
    - srapply ifbl_extend; assumption.
  Defined.

  Local Lemma indpred_from_ifbl_from_indpred
      {Γ} (d_Γ : wf_context_derivation T Γ)
    : indpred_from_ifbl (ifbl_from_indpred d_Γ)
      = d_Γ.
  Proof.
    induction d_Γ as [ | Δ d_Δ IH A d_A].
    - apply idpath.
    - simpl.
      apply (ap (fun d_Θ => wf_context_extend d_Θ _)).
      apply IH.
  Defined.

  Local Lemma length_indpred_from_ifbl {n} {Γ}
      (Γ_wf : wf_context_ifbl T n Γ)
    : length_of_wf_derivation (indpred_from_ifbl Γ_wf) = n.
  Proof.
    revert Γ Γ_wf. induction n as [ | n' IH].
    - intros Γ Γ_wf; destruct Γ_wf.
      apply idpath.
    - intros Γ Γ_wf; destruct Γ_wf as [Γ' Γ'_wf A d_A].
      simpl. apply ap, IH.
  Defined.

  Local Lemma ifbl_from_indpred_from_ifbl {n} {Γ}
      (Γ_wf : wf_context_ifbl T n Γ)
    : transport (fun n => wf_context_ifbl _ n _) 
                (length_indpred_from_ifbl Γ_wf)
                (ifbl_from_indpred (indpred_from_ifbl Γ_wf))
      = Γ_wf.
  Proof.
    revert Γ Γ_wf. induction n as [ | n' IH].
    - intros Γ Γ_wf; destruct Γ_wf.
      apply idpath.
    - intros Γ Γ_wf; destruct Γ_wf as [Γ' Γ'_wf A d_A]. simpl.
      eapply concat. { apply transport_ifbl_extend. }
      apply (ap (fun Θ_wf => ifbl_extend _ Θ_wf _)).
      apply IH.
  Defined.

  Local Theorem weq_ifbl_indpred { Γ }
    : { n : nat & wf_context_ifbl T n Γ }
    <~> wf_context_derivation T Γ.
  Proof.
    srapply equiv_adjointify.
    - intros [n Γ_wf].
      eapply indpred_from_ifbl; eassumption.
    - intros d_Γ.
      exists (length_of_wf_derivation d_Γ).
      apply ifbl_from_indpred.
    - intros d_Γ.
      apply indpred_from_ifbl_from_indpred.
    - intros [n Γ_wf].
      eapply path_sigma.
      apply ifbl_from_indpred_from_ifbl.
  Defined.

End Inductive_Predicate_vs_Inductive_Family_By_Length.

Section Induction_By_Length_vs_Inductive_Family_By_Length.
(* "ibl" vs "ifbl" *)

  Context {Σ : signature σ} (T : flat_type_theory Σ).

  Definition weq_ibl_ifbl_zero
    : (ibl_zero_step Σ).1 <~> { Γ : _ & wf_context_ifbl_zero_step Σ Γ }.
  Proof.
    srapply equiv_adjointify.
    - intros _.
      exists Context.empty.
      constructor.
    - intros [Γ Γ_wf]; destruct Γ_wf.
      apply (wf_context_ibl_empty T).
    - intros [Γ Γ_wf]; destruct Γ_wf.
      apply idpath.
    - intros []; apply idpath.
  Defined.
  
  Section Ibl_Ifbl_Succ_Step.
  (*
   In this section, we give the successor step of the equivalence
   between [ibl] and [ifbl]:

   we assume that we have types/familes [X], [fl] and [Y] over [raw_context Σ],
   to be thought of as [ibl T n], [ibl_flatten], and [ifbl T n],
   and an equivalence between them (given in elementary, deconstructed form)
   we then construct a similar equivalence between [ibl_succ_step X fl] and
   [ifbl_succ_step Y].
   *)
  Context { X : Type } (fl : X -> raw_context Σ )
          ( Y : raw_context Σ -> Type)
          ( f : forall x:X, Y (fl x))
          ( g : forall Γ, Y Γ -> X)
          ( fl_g : forall Γ y, fl (g Γ y) = Γ)
          ( e_fg : forall Γ y, transport _ (fl_g _ _) (f (g Γ y)) = y)
          ( e_gf : forall x, g _ (f x) = x)
          ( fl_gf : forall x, ap fl (e_gf x) = fl_g _ _).

  Context ( X' := (ibl_succ_step T (X;fl)).1)
          ( fl' := (ibl_succ_step T (X;fl)).2 : X' -> _)
          ( Y' := wf_context_ifbl_succ_step T Y ).

  Local Definition ifbl_from_ibl_succ (ΓA_wf : X') : Y' (fl' ΓA_wf).
  Proof.
    destruct ΓA_wf as [Γ_wf [A d_A]].
    apply wf_context_ifbl_extend_internal.
    - apply f.
    - exact d_A.
  Defined.

  Local Definition ibl_from_ifbl_succ {ΓA} (ΓA_wf : Y' ΓA) : X'.
  Proof.
    destruct ΓA_wf as [Γ Γ_wf A d_A].
    srapply ibl_extend_internal.
    - exact (g _ Γ_wf).
    - exact (transport
            (fun (Θ : raw_context _) => raw_type Σ Θ) (fl_g _ _)^ A).
    - exact (transportD _
            (fun Θ B => FlatTypeTheory.derivation _ _ [! Θ |- B !])
            _ _ d_A).
  Defined.

  Local Definition flatten_ibl_from_ifbl_succ {ΓA} (ΓA_wf : Y' ΓA)
    : fl' (ibl_from_ifbl_succ ΓA_wf) = ΓA.
  Proof.
    destruct ΓA_wf as [Γ Γ_wf A d_A]. cbn.
    eapply (ap011D _ (fl_g _ _)). exact (transport_pV _ (fl_g _ _) A).
  Defined.

  (* TODO: upstream in file *)
  Local Lemma transport_ifbl_context_extend
      {Γ} (Γ_wf : Y Γ)
      {Γ'} (e_Γ : Γ = Γ')
      {A} (d_A : FlatTypeTheory.derivation T [<>] [! Γ |- A !])
      {A'} (e_A : transport (fun (Θ : raw_context _) => raw_type _ Θ) e_Γ A = A') 
    : transport Y' (ap011D Context.extend e_Γ e_A)
                (wf_context_ifbl_extend_internal T Y Γ_wf d_A)
      = wf_context_ifbl_extend_internal T _
          (transport Y e_Γ Γ_wf)
          (transport _ e_A
            (transportD (fun Θ : raw_context Σ => raw_type Σ Θ)
                        (fun (Θ : raw_context Σ) (B : raw_type Σ Θ) =>
                           FlatTypeTheory.derivation T [<>] [!Θ |- B!])
                        e_Γ _ d_A)).
  Proof.
    destruct e_Γ, e_A. apply idpath.
  Defined.

  Local Definition ibl_from_ifbl_from_ibl_succ
      {ΓA} (ΓA_wf : Y' ΓA)
    : transport _ (flatten_ibl_from_ifbl_succ ΓA_wf)
                (ifbl_from_ibl_succ (ibl_from_ifbl_succ ΓA_wf))
      = ΓA_wf.
  Proof.
    destruct ΓA_wf as [Γ Γ_wf A d_A].
    unfold ifbl_from_ibl_succ; cbn.
    eapply concat. { apply transport_ifbl_context_extend. }
    apply (ap2 (fun d_Θ d_B => wf_context_ifbl_extend_internal _ _ d_Θ d_B)).
    { apply e_fg. }
    eapply concat. { apply ap. rapply transportD_pV. }
    apply (transport_pV (fun B : raw_type Σ Γ =>
      FlatTypeTheory.derivation T [<>] [!Γ |- B!])).
  Defined.

(*
  Local Definition ibl_extend'
      (ΓA : { Γ : X & A : raw_type Σ (fl Γ)}) (d_A : _)
    : X'
  := 
*)
  Local Definition ifbl_from_ibl_from_ifbl_succ (ΓA_wf : X')
    : ibl_from_ifbl_succ (ifbl_from_ibl_succ ΓA_wf) = ΓA_wf.
  Proof.
    destruct ΓA_wf as [Γ_wf AdA]. simpl.
    srapply path_sigma. { apply e_gf. } simpl.
    eapply concat.
    { apply ap, inverse.
      refine (transport_sigma (fl_g (fl Γ_wf) (f Γ_wf))^ _). }
    eapply concat. { refine (transport_compose _ fl _ _). }
    eapply concat. { refine (ap (fun p => transport _ p _) (fl_gf _)). }
    rapply transport_pV.
  Defined.

  (* Several things seem to be instances of this lemma,
     as found by [Search (transport _ _ (?f ?a) = ?g (transport _ _ ?a)).]
   [transport_rename] 
   [transport_substitute]
   [transport_class_instantiate]
   [transport_shape_instantiate] 
   TODO: unify them in terms of this lemma, or [ap_transport] directly.
   *)
  (* TODO: upstream, and change F to f *)
  Lemma transport_Fx
    {A} {P P' : A-> Type} (F : forall x, P x -> P' x)
    {x x'} (e : x = x') (y :P x)
    : transport P' e (F _ y) = F _ (transport P e y).
  Proof.
    apply inverse, ap_transport.
  Defined.

  (* TODO: name! *)
  Local Lemma ap_flatten_path_sigma
      {Γ_wf Γ'_wf : X} (e_Γ : Γ_wf = Γ'_wf)
      {AdA} {AdA'} (e_A : transport _ e_Γ AdA = AdA')
      (e_aux : transport _ (ap fl e_Γ) AdA.1 = AdA'.1
        := (transport_Fx
             (fun Θ (BdB : {A : _ & FlatTypeTheory.derivation _ _ [! Θ |- A!]})
                => BdB.1)
           _ AdA
          @ ap pr1 (transport_compose
              (fun Θ => {A : _ & FlatTypeTheory.derivation _ _ [! Θ |- A!]})
              fl e_Γ AdA)^)
          @ ap pr1 e_A)
    : ap fl' (path_sigma _ (_;_) (_;_) e_Γ e_A)
    = ap011D Context.extend (ap fl e_Γ) e_aux.
  Proof.
    destruct e_Γ, e_A. cbn.
    apply idpath.
  Defined.

  Lemma ap_transport_pV
         {A} {P P'} (F : forall x, P x -> P' x)
         {x y : A} (p : x = y) (z : P y)
    : ap (F _) (transport_pV _ p z)
    = ap_transport _ _ _
      @ (ap (transport P' p) (ap_transport _ _ _))
      @ transport_pV _ p (F _ z).
  Proof.
    destruct p; apply idpath.
  Defined.

  Definition flatten_ifbl_from_ibl_from_ifbl_succ (ΓA_wf : X')
    : ap fl' (ifbl_from_ibl_from_ifbl_succ ΓA_wf) = flatten_ibl_from_ifbl_succ _.
  Proof.
    destruct ΓA_wf as [Γ AdA].
    unfold ifbl_from_ibl_from_ifbl_succ.
    eapply concat. { apply ap_flatten_path_sigma. }
    srapply (ap011D (fun p q => ap011D Context.extend p q)).
    { apply fl_gf. }
    cbn.
    eapply concat.
    { refine (transport_compose (fun q => q = AdA.1) _ (fl_gf Γ) _). }
    eapply concat. { apply transport_paths_l. }
    eapply concat.
    { apply ap, ap.
      eapply concat. { rapply ap_pp. } 
      eapply ap, concat. { rapply ap_pp. }
      eapply ap, concat. { rapply ap_pp. }
      eapply ap.
      refine (ap_transport_pV
        (fun Θ (BdB : {A : _ & FlatTypeTheory.derivation _ _ [! Θ |- A!]})
             => BdB.1)
        (fl_g (fl Γ) (f Γ)) AdA).
    }
    (* note: last component of LHS is now exactly RHS *)
    admit.
  Admitted.

  End Ibl_Ifbl_Succ_Step.

  (* TODO: the above lemmas should suffice to give the inductive step
  of an equivalence between [ibl] and [ifbl]. *)

End Induction_By_Length_vs_Inductive_Family_By_Length.

End Fix_Shape_System.
