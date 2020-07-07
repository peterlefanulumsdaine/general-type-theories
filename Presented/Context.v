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

  Local Lemma transport_wf_context_extend
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
    : transport (wf_context_derivation T)
        (wf_context_of_length_from_wf_derivation d_Γ).2
        (wf_context_of_length_is_wf
          (wf_context_of_length_from_wf_derivation d_Γ).1)
      = d_Γ.
  Proof.
    induction d_Γ as [ | Δ d_Δ IH A d_A].
    - apply idpath.
    - simpl.
      eapply concat. { apply transport_wf_context_extend. }
      apply (ap2 (fun d_Θ d_B => wf_context_extend T d_Θ d_B)).
      { apply IH. }
      set (e := wf_context_of_length_from_wf_derivation d_Δ).
      clearbody e.
      destruct e as [Γ_wf e_ΓΔ].
      eapply concat. { apply ap. rapply transportD_pV. }
      apply (transport_pV (fun B : raw_type Σ Δ =>
     FlatTypeTheory.derivation T [<>] [!Δ |- B!])).
  Defined.

  Local Fixpoint length_of_wf_deriv_of_col
      {n} (Γ_wf : wf_context_of_length T n)
      {struct n}
    : length_of_wf_derivation T (wf_context_of_length_is_wf Γ_wf)
    = n.
  Proof.
    destruct n as [ | n IH].
    { apply idpath. }
    simpl. apply (ap S). apply length_of_wf_deriv_of_col.
  Defined.

  Local Lemma flatten_transport
      {n n'} (e_n : n = n')
      (Γ : wf_context_of_length T n)
    : flatten (transport _ e_n Γ) = flatten Γ.
  Proof.
    destruct e_n; apply idpath.
  Defined.

  Local Lemma transport_wf_context_of_length_extend_aux
      {n n'} (e_n : n = n')
      {Γ : wf_context_of_length T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!flatten Γ |- A!])
      (e_aux := (ap011D Context.extend ((flatten_transport e_n Γ)^ @ ap flatten e_Γ)
                        1%path)
                 : flatten (wf_context_of_length_extend T Γ d_A)
                = flatten (wf_context_of_length_extend T _ _))
    : { e : transport (wf_context_of_length T) (ap S e_n)
                (wf_context_of_length_extend _ Γ d_A)
          = wf_context_of_length_extend _ Γ'
              (transportD _ (fun Θ B => FlatTypeTheory.derivation T [<>] [! Θ |- B !])
                          ((flatten_transport e_n Γ)^ @ ap flatten e_Γ) _ d_A)
      & ap flatten e = flatten_transport _ _ @ e_aux }.
  Proof.
    destruct e_n; destruct e_Γ; simpl in *.
    exists 1%path. apply 1%path.
  Qed.

  Local Definition transport_wf_context_of_length_extend
      {n n'} (e_n : n = n')
      {Γ : wf_context_of_length T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!flatten Γ |- A!])
    : _ = _
  := (transport_wf_context_of_length_extend_aux e_n e_Γ d_A).1.

  Local Definition flatten_transport_wf_context_of_length_extend
      {n n'} (e_n : n = n')
      {Γ : wf_context_of_length T n}
      {Γ'} (e_Γ : transport _ e_n Γ = Γ')
      {A : raw_type Σ (flatten Γ)}
      (d_A : FlatTypeTheory.derivation T [<>] [!flatten Γ |- A!])
    : ap flatten (transport_wf_context_of_length_extend e_n e_Γ d_A) = _
  := (transport_wf_context_of_length_extend_aux e_n e_Γ d_A).2.

  Local Lemma col_of_deriv_of_col_eq
      {n} (Γ_wf : wf_context_of_length T n)
    : { e : transport (wf_context_of_length T)
         (length_of_wf_deriv_of_col Γ_wf)
         (wf_context_of_length_from_wf_derivation
                      (wf_context_of_length_is_wf Γ_wf)).1
            = Γ_wf
      & ap flatten e
        = (flatten_transport _ _)
        @ (wf_context_of_length_from_wf_derivation _).2 }.
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
      { rapply transport_wf_context_of_length_extend. apply e_Γ. }
      apply (ap (fun AdA => (Δ_wf ; AdA))).
      eapply concat.
      { refine (transport_sigma ((flatten_transport _ _)^ @ _) (_;_))^. }
      eapply concat.
      { refine (ap _ (transport_sigma 
                   ((wf_context_of_length_from_wf_derivation _).2)^ (_;_))^). }
      eapply concat. { apply inverse. rapply transport_pp. }
      refine (@ap _ _ (fun p => transport _ p (A;d_A)) _ 1%path _).
      eapply concat. { apply ap, ap, flatten_e_Γ. }
      eapply concat. { apply ap, concat_V_pp. }
      apply concat_Vp.
    - eapply concat. { apply ap_pp. }
      eapply concat.
      { eapply (ap_1back concat),
               flatten_transport_wf_context_of_length_extend.
      }
      admit.
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
      rapply path_sigma.
      { apply col_of_deriv_of_col_eq.
      }
  Defined.

End Inductive_By_Length_vs_Inductive_Predicate.

End Fix_Shape_System.
