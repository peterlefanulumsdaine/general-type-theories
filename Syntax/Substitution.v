Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.Expression.


Section RawSubstitution.

  Context {σ : shape_system} {Σ : signature σ}.

  (* A raw substitution is the input data for a simultaneous substitution:
  for each variable of one shape, a raw term over another shape.

  NOTE: naming-wise, it would be nicer if this was called [Context.map] or
  similar.  However, in terms of depedency requirements, it fits much more
  naturally here: this and its lemmas do not depend on anything about raw
  contexts, whereas most constructions on them depend on this file. *)
  Definition raw_context_map (γ δ : σ)
    := δ -> raw_term Σ γ.

  (* Not required now, but required so that later things that coerce to
  raw context maps can be used as functions. *)
  Identity Coercion map_of_raw_context_map : raw_context_map >-> Funclass.

  (* A substitution from [γ] to [γ'] may be extended to one from [γ + δ] to
  [γ' + δ], by variable-renaming.

  This is needed for going under binders during substitution. *)
  Local Definition extend (γ γ' δ : σ)
    : raw_context_map γ' γ -> raw_context_map (shape_sum γ' δ) (shape_sum γ δ).
  Proof.
    intros f.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn.
    - intros i.
      refine (Expression.rename _ (f i)).
      apply (coproduct_inj1 (shape_is_sum)).
    - intros i.
      apply raw_variable.
      apply (coproduct_inj2 (shape_is_sum)), i.
  Defined.

  (* Apply a raw substitution to a raw expression. *)
  Fixpoint substitute
      {γ δ : σ} (f : raw_context_map δ γ)
      {cl : syntactic_class}
      (e : raw_expression Σ cl γ)
    : raw_expression Σ cl δ.
  Proof.
    destruct e as [ γ i | γ S args ].
    - exact (f i).
    - refine (raw_symbol S _). intros i.
      refine (substitute _ _ _ _ (args i)).
      apply extend. exact f.
  Defined.

  (** Interaction of substitution with transport *)

  (* TODO: consistentise naming of this and the following *)
  Local Definition transport_substitute {γ γ' : σ} (g : _)
      {cl cl' : syntactic_class} (p : cl = cl') (e : raw_expression Σ cl γ)
    : transport (fun cl => raw_expression Σ cl γ') p (substitute g e)
      = substitute g (transport (fun cl => raw_expression Σ cl γ) p e).
  Proof.
    destruct p. apply idpath.
  Defined.

  Lemma substitute_transport_shape
      {γ γ'} (e_γ : γ = γ') {δ}
      (f : raw_context_map δ γ')
      {cl} (e : raw_expression Σ cl γ)
    : substitute f (transport (raw_expression _ _) e_γ e)
      = substitute (transport (raw_context_map _) e_γ^ f) e.
  Proof.
    destruct e_γ; apply idpath.
  Defined.

End RawSubstitution.

Arguments raw_context_map [_] _ _ _.

(* Here we show that raw context maps form a category (modulo truncation assumptions).

  Note: we assume functional extensionality throughout.  That shouldn’t be essentially necessary — it should be possible to show that e.g. [Substitution.rename] respects “recursive extensional equality” of terms, and so on, and hence to show that raw context maps form a category modulo this equality — but using funext makes life a lot simpler. *)

Section Raw_Context_Category_Structure.
(* Identity and composition of raw context maps. *)

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition id_raw_context (γ : σ) : raw_context_map Σ γ γ.
  Proof.
    exact (@raw_variable _ _ _).
  Defined.

  Local Definition comp_raw_context {γ γ' γ'': σ}
      (f : raw_context_map Σ γ' γ)
      (f' : raw_context_map Σ γ'' γ')
    : raw_context_map Σ γ'' γ
  := fun x => substitute f' (f x).

End Raw_Context_Category_Structure.

(* Just as the definition of substitution resembles the “lift” operation of a Kleisli-style monad, similarly, its “functoriality” is naturally proved in a form similar to the laws of a Kleisli-style monad.  That is, in terms of
  [ return := raw_variable : γ -> Raw_Syntax γ ]
  [ lift := substitute : (γ' -> Raw_Syntax γ) -> (Raw_Syntax γ' -> Raw_Syntax γ) ]
  we show roughly:
  [ id_left_substitute : forall (f : γ' -> Raw_Syntax γ) , (fun a => lift f (return a)) = f ]
  [ id_right_substitute : lift return = idfun : Raw_Syntax γ -> Raw_Syntax γ]
  [ associativity : (lift g) o (lift f) = lift ((lift g) o f) ]

  These then suffice to show that raw context maps (roughly, the Kleisli category of this not-exactly-monad) form a category (modulo h-levels).

  TODO: see if this “looks like a monad” can be made more precise: does our approach fit into e.g. relative or indexed monads?
*)
Section Substitute_Laws.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition id_left_substitute
      {γ γ' : σ} (f : raw_context_map Σ γ' γ) (x : _)
    : substitute f (raw_variable x) = f x.
  Proof.
    apply idpath.
  Defined.

  Lemma substitute_idmap {γ} {cl} (e : raw_expression Σ cl γ)
    : substitute (id_raw_context γ) e = e.
  Proof.
    induction e as [ γ i | γ s es IH_es ].
    - apply idpath.
    - cbn. apply ap.
      apply path_forall; intros i.
      eapply concat.
      2: { apply IH_es. }
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros j. refine (coproduct_comp_inj1 _).
      + intros j. refine (coproduct_comp_inj2 _).
  (* Note: original proof literally identical to that of [rename_idmap]! *)
  Defined.

  (* We provide this under two names: [substitute_idmap] follows general
     naming conventions for recognising it when it arises in derivations;
     [id_right_substitute] fits the monad-law structure, for when it’s being
     used in those terms. *)
  Local Fixpoint id_right_substitute
      {γ : σ} {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute (id_raw_context γ) e = e
  := substitute_idmap e.

  Lemma substitute_raw_variable
    {γ γ' : σ} (r : γ -> γ')
    {cl} (e : raw_expression Σ cl γ)
    : substitute (fun i => raw_variable (r i)) e = rename r e.
  Proof.
    revert γ' r; induction e as [ γ i | γ s es IH_es ]; intros γ' r.
    - apply idpath.
    - cbn. apply ap.
      apply path_forall; intros i.
      eapply concat.
      2: { apply IH_es. }
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intro; unfold extend.
      + repeat rewrite coproduct_comp_inj1; apply idpath.
      + repeat rewrite coproduct_comp_inj2; apply idpath.
  Defined.

  Local Fixpoint rename_substitute {γ γ' γ'' : σ}
      (f : raw_context_map Σ γ' γ) (g : γ' -> γ'')
      {cl} (e : raw_expression Σ cl γ)
    : Expression.rename g (substitute f e)
      = substitute ((Expression.rename g) o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply rename_substitute. }
    apply (ap_2back substitute), path_forall.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_ @ _^). { apply rename_rename. }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine (_ @ _). { apply rename_rename. }
      apply (ap_2back rename), path_forall; intros y.
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      cbn. refine (_^).
      eapply concat. { refine (coproduct_comp_inj2 _). }
      apply ap. refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Fixpoint substitute_rename
      {γ γ' γ'' : σ} (f : γ -> γ') (g : raw_context_map Σ γ'' γ')
      {cl} (e : raw_expression Σ cl γ)
    : substitute g (Expression.rename f e)
    = substitute (g o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply substitute_rename. }
    apply (ap_2back substitute), path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Local Fixpoint assoc_substitute {γ γ' γ'': σ}
      (f : raw_context_map Σ γ' γ)
      (f' : raw_context_map Σ γ'' γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute f' (substitute f e)
    = substitute (fun i => substitute f' (f i)) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply assoc_substitute. }
    apply (ap_2back substitute), path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_ @ _^).
      2 : { refine (coproduct_comp_inj1 _). }
      + eapply concat. { apply substitute_rename. }
        eapply concat.
        2: { eapply inverse, rename_substitute. }
        * apply (ap_2back substitute), path_arrow. intros ?.
          refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      refine (_ @ _^).
      2: { refine (coproduct_comp_inj2 _). }
      + cbn. refine (coproduct_comp_inj2 _).
  Defined.

  (* Alias of [assoc_substitute], to fit general naming conventions for
     equational lemmas *)
  Definition substitute_substitute {γ γ' γ'': σ}
      (f : raw_context_map Σ γ' γ)
      (f' : raw_context_map Σ γ'' γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute f' (substitute f e)
    = substitute (fun i => substitute f' (f i)) e
  := assoc_substitute f f' e.

End Substitute_Laws.

(* Finally, the category laws for raw context maps. *)
Section Raw_Context_Category.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Lemma id_left_raw_context {γ} (f : raw_context_map Σ γ γ)
    : comp_raw_context (id_raw_context _) f = f.
  Proof.
    apply idpath.
    (* To understand this, uncomment the following: *)
    (* [unfold comp_raw_context, id_raw_context.] *)
  Defined.

  Lemma id_right_raw_context {γ} (f : raw_context_map Σ γ γ)
    : comp_raw_context f (id_raw_context _) = f.
  Proof.
    apply path_forall; intros x; cbn.
    apply id_right_substitute.
  Defined.

  Lemma assoc_raw_context {γ0 γ1 γ2 γ3: σ}
      (f0 : raw_context_map Σ γ0 γ1)
      (f1 : raw_context_map Σ γ1 γ2)
      (f2 : raw_context_map Σ γ2 γ3)
    : comp_raw_context f2 (comp_raw_context f1 f0)
    = comp_raw_context (comp_raw_context f2 f1) f0.
  Proof.
    apply path_forall; intros x; unfold comp_raw_context; cbn.
    refine _^. apply assoc_substitute.
  Defined.

End Raw_Context_Category.

(* Here we give naturality of substitution with respect to signature maps *)
Section Naturality.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.

  Definition raw_context_map_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {γ γ'} (g : raw_context_map Σ γ' γ)
    : raw_context_map Σ' γ' γ
  := fun i => (Expression.fmap f (g i)).

  Local Definition fmap_extend
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {γ γ' δ : σ} (g : raw_context_map Σ γ' γ)
    : raw_context_map_fmap f (extend _ _ δ g)
    = extend _ _ δ (raw_context_map_fmap f g).
  Proof.
    apply path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i. unfold raw_context_map_fmap.
      eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply Expression.fmap_rename. }
      apply inverse. refine (coproduct_comp_inj1 _).
    - intros i. unfold raw_context_map_fmap.
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      apply inverse. refine (coproduct_comp_inj2 _).
  Defined.
  
  Local Fixpoint fmap_substitute
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {γ γ'} (g : raw_context_map Σ γ' γ)
      {cl} (e : raw_expression Σ cl γ)
    : Expression.fmap f (substitute g e)
    = substitute (raw_context_map_fmap f g) (Expression.fmap f e).
  Proof.
    destruct e as [ γ i | γ S args ].
    - apply idpath.
    - simpl.
      eapply concat.
      { apply ap, ap, ap. apply path_forall; intros i. apply fmap_substitute. }
      eapply concat. 2: { apply transport_substitute. }
      + apply ap. cbn. apply ap.
        set (ΣfS := Σ' (f S)). change (symbol_arity (f S)) with (snd ΣfS).
        set (p := Family.map_commutes f S : ΣfS = _). clearbody p ΣfS.
        revert p; apply inverse_sufficient; intros q.
        destruct q. cbn.
        apply path_forall; intros i.
        apply (ap_2back substitute).
        apply fmap_extend.
  Defined.

End Naturality.

