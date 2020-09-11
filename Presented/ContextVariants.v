(** The aim of this module is to compare various alternate definitions of sequential contexts

The treatment roughly follows that given in the (draft) appendix to the paper, considering a subset of the definitions considered there.

This file is for intrinsic interest: it is _not_ intended to be the main version of sequential contexts used in further development.

As such, and since the content of the file necessitates many parallel definitions, we break with our normal naming conventions and use abbreviations.  Each definition of sequential contexts is assigned a short identifying code, which should be consistently used in its associated constructions and lemmas.  [TODO: this convention is not quite consistently implemented yet.]

*)

Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.RawRule.
Require Import Typing.RawTypeTheory.

(* TODO: upstream within development *)
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

  (* Several things seem to be instances of this lemma,
     as found by [Search (transport _ _ (?f ?a) = ?g (transport _ _ ?a)).]
   [transport_rename]
   [transport_substitute]
   [transport_class_instantiate]
   [transport_scope_instantiate]
   TODO: unify them in terms of this lemma, and/or [ap_transport] directly.
   *)
  Lemma transport_fx
    {A} {P P' : A-> Type} (f : forall x, P x -> P' x)
    {x x'} (e : x = x') (y :P x)
    : transport P' e (f _ y) = f _ (transport P e y).
  Proof.
    apply inverse, ap_transport.
  Defined.

  Lemma transport_fx_ap
    {A} {P P' : A-> Type} (f : forall x, P x -> P' x)
    {x x'} (e_x : x = x') {y y' :P x} (e_y : y = y')
    : transport_fx f e_x y @ ap _ (ap _ e_y)
   = ap _ (ap _ e_y) @ transport_fx f e_x y'.
  Proof.
    destruct e_x, e_y. apply idpath.
  Defined.

  Lemma transport_fx_ap_path
    {A} {P P' : A-> Type} (f : forall x, P x -> P' x)
    {x x'} {e e' : x = x'} (α : e = e') (y :P x)
    : transport_fx f e y @ ap _ (ap (fun p => transport P p y) α)
    = ap (fun p => transport P' p _) α @ transport_fx f e' y.
  Proof.
    destruct α, e; apply idpath.
  Defined.

  Lemma ap_transport_ap_path
    {A} {P P' : A-> Type} (f : forall x, P x -> P' x)
    {x x'} {e e' : x = x'} (α : e = e') (y :P x)
    : ap_transport e f y @ ap (fun p => transport P' p _) α
      = ap _ (ap (fun p => transport P p y) α) @ ap_transport e' f y.
  Proof.
    destruct α, e; apply idpath.
  Defined.

  Lemma ap_transport_pV
         {A} {P P'} (f : forall x, P x -> P' x)
         {x y : A} (p : x = y) (z : P y)
    : ap (f _) (transport_pV _ p z)
    = ap_transport _ _ _
      @ (ap (transport P' p) (ap_transport _ _ _))
      @ transport_pV _ p (f _ z).
  Proof.
    destruct p; apply idpath.
  Defined.

  Lemma concat_transport_compose_ap
      {A A'} (f : A' -> A) (B : A -> Type)
      {x1 x2} (p : x1 = x2)
      {y y' : B (f x1)} (e : y = y')
    : transport_compose B f p y @ ap _ e
      = ap _ e @ transport_compose B f p y'.
  Proof.
    destruct p, e; apply idpath.
  Defined.

  Lemma ap_pr1_transport_sigma
        {A} {B} (C : forall a : A, B a -> Type)
        {x1 x2 : A} (p : x1 = x2)
        (yz : {y : B x1 & C x1 y})
    : ap pr1 (transport_sigma p yz) = ap_transport _ (fun x yz => yz.1) _.
  Proof.
    destruct p; apply idpath.
  Defined.

  (* Handy for showing path nodes and figuring out big path-computations:
   use [Local Open Scope verbose_path_scope] to turn it “on”. *)
  Declare Scope verbose_path_scope.
  Notation "p @[ x ] q" := (@concat _ _ x _ p q) (at level 25)
    : verbose_path_scope.
  (* TODO: search more carefully for if the library already provides a version of this *)

  (* consider naming *)
  Lemma concat_ap1_ap2 {X Y Z} (f : X -> Y -> Z)
      {x0 x1} (e_x : x0 = x1) {y0 y1} (e_y : y0 = y1)
    : ap _ e_y @ ap (fun x => f x _) e_x
    = ap (fun x => f x _) e_x @ ap _ e_y.
  Proof.
    destruct e_x, e_y; apply idpath.
  Defined.

End Auxiliary.

Section Fix_Scope_System.

Context {σ : scope_system}.

Section Inductive_Predicate.
(** One approach: sequential well-formed contexts are defined directly, by a proof-relevant inductive predicate on raw raw contexts, looking like the standard well-formed context judgement *)
(* Code: [indpred].
TODO: systematically use this code in definitions to disambiguate from other approaches *)

  Context {Σ : signature σ} (T : raw_type_theory Σ).

  Inductive wf_context_derivation : raw_context Σ -> Type
  :=
    | wf_context_empty
      : wf_context_derivation Context.empty
    | wf_context_extend
        {Γ} (d_Γ : wf_context_derivation Γ)
        {A} (d_A : RawTypeTheory.derivation T [<>]
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

  Context {Σ : signature σ} (T : raw_type_theory Σ).

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
        & RawTypeTheory.derivation T [<>] [! f Γ |- A !] }}.
    intros Γ_A_dA.
    exact (Context.extend (f (pr1 Γ_A_dA)) (pr1 (pr2 Γ_A_dA))).
  Defined.

  Definition ibl_extend_internal (X_f : { X : Type & X -> raw_context Σ })
      (Γ : X_f.1)
      {A} (d_A : RawTypeTheory.derivation T [<>] [! X_f.2 Γ |- A !])
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
      {A} (d_A : RawTypeTheory.derivation T [<>] [! ibl_flatten Γ |- A !])
    : wf_context_ibl (S n)
  := ibl_extend_internal _ Γ d_A.

End Induction_By_Length.

Arguments ibl_zero_step Σ : clear implicits.
Arguments wf_context_ibl_with_flattening : simpl nomatch.
Arguments wf_context_ibl : simpl nomatch.
Arguments ibl_flatten {Σ T n} Γ : simpl nomatch.

Section Inductive_Family_By_Length.
(** A slightly unnatural definition, introduced in hope it may facilitate the equivalence between the by-induction-on-length definition and the definitions as inductive types/families. *)
(* Code: “ifbl”, to be used consistently in definitions/comparisons. *)

  Context {Σ : signature σ} (T : raw_type_theory Σ).


  Inductive wf_context_ifbl_zero_step : raw_context Σ -> Type
  := wf_context_ifbl_empty : wf_context_ifbl_zero_step Context.empty.

  Inductive wf_context_ifbl_succ_step (X : raw_context Σ -> Type)
    : raw_context Σ -> Type
  := | wf_context_ifbl_extend_internal {Γ} (Γ_wf : X Γ)
       {A} (d_A : RawTypeTheory.derivation T [<>] [! Γ |- A !])
     : wf_context_ifbl_succ_step X (Context.extend Γ A).

  Local Lemma transport_ifbl_extend_internal (X : raw_context Σ -> Type)
      {Γ} (Γ_wf : X Γ)
      {Γ'} (e_Γ : Γ = Γ')
      {A} (d_A : RawTypeTheory.derivation T [<>] [! Γ |- A !])
      {A'} (e_A : transport (fun (Θ : raw_context _) => raw_type _ Θ) e_Γ A = A')
    : transport _ (ap011D Context.extend e_Γ e_A)
                (wf_context_ifbl_extend_internal X Γ_wf d_A)
      = wf_context_ifbl_extend_internal _
          (transport X e_Γ Γ_wf)
          (transport _ e_A
            (transportD (fun Θ : raw_context Σ => raw_type Σ Θ)
                        (fun (Θ : raw_context Σ) (B : raw_type Σ Θ) =>
                           RawTypeTheory.derivation T [<>] [!Θ |- B!])
                        e_Γ _ d_A)).
  Proof.
    destruct e_Γ, e_A. apply idpath.
  Defined.

  Fixpoint wf_context_ifbl (n : nat) : raw_context Σ -> Type.
  Proof.
    destruct n as [ | n'].
    - exact wf_context_ifbl_zero_step.
    - exact (wf_context_ifbl_succ_step (wf_context_ifbl n')).
  Defined.

  Local Definition ifbl_extend {n} {Γ}
      (Γ_wf : wf_context_ifbl n Γ)
      {A} (d_A : RawTypeTheory.derivation T [<>] [!Γ |- A!])
    : wf_context_ifbl (S n) (Context.extend Γ A)
  := wf_context_ifbl_extend_internal _ Γ_wf d_A.

  Arguments ifbl_extend : simpl never.

  (* TODO: consider naming; cf. [transport_ifbl_extend_internal]. *)
  Local Definition transport_ifbl_extend
      {n n'} (e_n : n = n')
      {Γ} (Γ_wf : wf_context_ifbl n Γ)
      {A} (d_A : RawTypeTheory.derivation T [<>] [!Γ |- A!])
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
  Context {Σ : signature σ} (T : raw_type_theory Σ).

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

  Context {Σ : signature σ} (T : raw_type_theory Σ).

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
            (fun Θ B => RawTypeTheory.derivation _ _ [! Θ |- B !])
            _ _ d_A).
  Defined.

  Local Definition flatten_ibl_from_ifbl_succ {ΓA} (ΓA_wf : Y' ΓA)
    : fl' (ibl_from_ifbl_succ ΓA_wf) = ΓA.
  Proof.
    destruct ΓA_wf as [Γ Γ_wf A d_A]. cbn.
    eapply (ap011D _ (fl_g _ _)). exact (transport_pV _ (fl_g _ _) A).
  Defined.

  Local Definition ibl_from_ifbl_from_ibl_succ
      {ΓA} (ΓA_wf : Y' ΓA)
    : transport _ (flatten_ibl_from_ifbl_succ ΓA_wf)
                (ifbl_from_ibl_succ (ibl_from_ifbl_succ ΓA_wf))
      = ΓA_wf.
  Proof.
    destruct ΓA_wf as [Γ Γ_wf A d_A].
    unfold ifbl_from_ibl_succ; cbn.
    eapply concat. { apply transport_ifbl_extend_internal. }
    apply (ap2 (fun d_Θ d_B => wf_context_ifbl_extend_internal _ _ d_Θ d_B)).
    { apply e_fg. }
    eapply concat. { apply ap. rapply transportD_pV. }
    apply (transport_pV (fun B : raw_type Σ Γ =>
      RawTypeTheory.derivation T [<>] [!Γ |- B!])).
  Defined.

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

  (* TODO: name! *)
  Local Lemma ap_flatten_path_sigma
      {Γ_wf Γ'_wf : X} (e_Γ : Γ_wf = Γ'_wf)
      {AdA} {AdA'} (e_A : transport _ e_Γ AdA = AdA')
      (e_aux : transport _ (ap fl e_Γ) AdA.1 = AdA'.1
        := (transport_fx
             (fun Θ (BdB : {A : _ & RawTypeTheory.derivation _ _ [! Θ |- A!]})
                => BdB.1)
           _ AdA
          @ ap pr1 (transport_compose
              (fun Θ => {A : _ & RawTypeTheory.derivation _ _ [! Θ |- A!]})
              fl e_Γ AdA)^)
          @ ap pr1 e_A)
    : ap fl' (path_sigma _ (_;_) (_;_) e_Γ e_A)
    = ap011D Context.extend (ap fl e_Γ) e_aux.
  Proof.
    destruct e_Γ, e_A. cbn.
    apply idpath.
  Defined.

  Definition flatten_ifbl_from_ibl_from_ifbl_succ (ΓA_wf : X')
    : ap fl' (ifbl_from_ibl_from_ifbl_succ ΓA_wf) = flatten_ibl_from_ifbl_succ _.
  Proof.
    destruct ΓA_wf as [Γ AdA].
    eapply concat. { apply ap_flatten_path_sigma. }
    srapply (ap011D (fun p q => ap011D Context.extend p q)).
    { apply fl_gf. }
    (* If we assumed that the signature (and hence syntax in a given scope) was a set, we would be done here by the set-property. *)
    cbn. Optimize Proof.
    eapply concat.
    { refine (transport_compose (fun q => q = _) _ (fl_gf Γ) _). }
    eapply concat. { apply transport_paths_l. }
    eapply concat.
    { eapply ap, concat. { apply concat_pp_p. }
      eapply ap, concat. { apply inverse, ap_pp. }
      eapply ap, concat.
      { eapply ap, concat. { apply concat_p_pp. }
        eapply (ap_1back concat), inverse.
        rapply concat_transport_compose_ap. (* commutation *)
      }
      eapply concat. { apply ap, concat_pp_p. }
      apply concat_V_pp. (* cancellation! *)
    }
    eapply concat.
    { apply ap, ap.
      eapply concat. { apply ap, concat_p_pp. }
      eapply concat. { apply ap_pp. }
      apply ap. refine (ap_transport_pV
        (fun Θ (BdB : {A : _ & RawTypeTheory.derivation _ _ [! Θ |- A!]})
             => BdB.1)
        _ (_;_)).
    }
    (* last component of LHS is now exactly RHS *)
    cbn.
    eapply concat.
    { eapply ap, concat. { eapply ap, (ap_1back concat). rapply ap_pp. }
      eapply concat. { eapply ap, concat_pp_p. }
      eapply concat. { apply concat_p_pp. }
      eapply (ap_1back concat).
      refine (transport_fx_ap _ (ap fl (e_gf Γ)) _).
    }
    simpl.
    eapply concat.
    { eapply ap, concat. { apply concat_pp_p. }
      eapply (ap_1back concat), ap.
      eapply concat. { refine (ap_V _ (transport_sigma _ _)). }
      eapply ap. refine (ap_pr1_transport_sigma _ (fl_g _ _)^ _).
    }
    eapply concat.
    { apply ap, ap, ap.
      eapply concat. { apply concat_p_pp. }
      eapply (ap_1back concat).
      eapply concat. { apply concat_p_pp. }
      eapply (ap_1back concat), inverse.
      refine (ap_transport_ap_path (fun Θ : raw_context Σ => pr1) _ _).
    }
    eapply concat.
    { apply ap, ap.
      eapply concat. { apply ap, concat_pp_p. }
      eapply concat. { apply ap, concat_pp_p. }
      refine (concat_V_pp (ap_transport _
        (fun Θ (BdB : {A : _ & RawTypeTheory.derivation _ _ [! Θ |- A!]})
             => BdB.1)
        _) _).
    }
    eapply concat. { eapply concat_p_pp. }
    eapply concat.
    { eapply ap, concat. { apply concat_p_pp. }
      eapply (ap_1back concat), inverse, concat_ap1_ap2.
    }
    eapply concat. { apply concat_p_pp. }
    eapply concat. 2: { apply concat_1p. }
    apply (ap_1back concat).
    eapply concat. { apply concat_pp_p. }
    eapply concat.
    { eapply ap, concat. { apply concat_p_pp. }
      eapply concat.
      { eapply (ap_1back concat), concat. { apply inverse, ap_pp. }
        apply ap, concat_Vp.
      }
      apply concat_1p.
    }
    apply concat_Vp.
    Optimize Proof.
  Time Qed.
  (* NOTE: if this slow compilation step later becomes too much annoyance slowing down the build, it could harmlessly be switched to [Admitted.] *)

  End Ibl_Ifbl_Succ_Step.

  Record slice_to_family_equiv { B : Type }
         { X : Type } {f : X -> B}
         { Y : B -> Type}
  := { slice_to_family : forall x:X, Y (f x)
      ; family_to_slice : forall b, Y b -> X
      ; proj_family_to_slice
        : forall b y, f (family_to_slice b y) = b
      ; slice_to_family_to_slice
        : forall b y, transport _ (proj_family_to_slice _ _)
                     (slice_to_family (family_to_slice b y))
           = y
      ; family_to_slice_to_family
        : forall x, family_to_slice _ (slice_to_family x) = x
      ; proj_family_to_slice_to_family
        : forall x, ap f (family_to_slice_to_family x)
                    = proj_family_to_slice _ _
     }.
  Arguments slice_to_family_equiv {_} _ _ _.

  Definition weq_ibl_ifbl_zero'
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

  Definition slice_to_family_equiv_ibl_ifbl (n:nat)
    : slice_to_family_equiv
        (wf_context_ibl T n) (ibl_flatten) (wf_context_ifbl T n).
  Proof.
    induction n as [ | n' IH].
    - srapply Build_slice_to_family_equiv.
      + intros ?. constructor.
      + intros ? ?. apply (wf_context_ibl_empty T).
      + intros Γ Γ_wf; destruct Γ_wf. apply idpath.
      + intros Γ Γ_wf; destruct Γ_wf. apply idpath.
      + intros []. apply idpath.
      + intros []. apply idpath.
   - destruct IH as [f g fl_g e_fg e_gf fl_e_gf].
     srapply Build_slice_to_family_equiv.
     + apply ifbl_from_ibl_succ; assumption.
     + eapply ibl_from_ifbl_succ; eassumption.
     + apply flatten_ibl_from_ifbl_succ.
     + apply ibl_from_ifbl_from_ibl_succ; assumption.
     + eapply ifbl_from_ibl_from_ifbl_succ; eassumption.
     + apply flatten_ifbl_from_ibl_from_ifbl_succ.
  Defined.

  Definition weq_ibl_ifbl {n:nat}
    : (wf_context_ibl T n) <~> {Γ : _ & wf_context_ifbl T n Γ }.
  Proof.
    set (stfe := slice_to_family_equiv_ibl_ifbl n).
    srapply equiv_adjointify.
    - intros Γ_wf.
      exists (ibl_flatten Γ_wf). apply stfe.
    - intros [Γ d_Γ]. eapply stfe; eassumption.
    - intros [Γ d_Γ]. srapply path_sigma; apply stfe.
    - intro; apply stfe.
  Defined.

End Induction_By_Length_vs_Inductive_Family_By_Length.


Section Induction_By_Length_vs_Inductive_Predicate.

  Context {Σ : signature σ} (T : raw_type_theory Σ).

  Local Theorem weq_ibl_indpred
    : { n : nat & wf_context_ibl T n}
    <~> { Γ : raw_context Σ & wf_context_derivation T Γ }.
  Proof.
    eapply equiv_compose'.
    { eapply equiv_functor_sigma_id, weq_ifbl_indpred. }
    eapply equiv_compose'.
    { apply equiv_sigma_symm. }
    apply equiv_functor_sigma_id, weq_ibl_ifbl.
  Defined.

End Induction_By_Length_vs_Inductive_Predicate.


End Fix_Scope_System.
