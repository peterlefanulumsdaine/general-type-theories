Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystems.
Require Import Auxiliary.Coproduct.
Require Import Raw.RawSyntax.

(* Goal: functoriality of substitution,
  and the fact that raw context morphisms form a category. *)

(* Outline: first we show functoriality of [Raw_Weaken], directly (since it is defined like a functorial action).

  Next, since substitution is defined like the “lift” operation of a Kleisli-style monad, we show its “functoriality” in the form of the laws of a Kleisli-style monad.  That is, in terms of
  [ return := var_Raw : γ -> Raw_Syntax γ ]
  [ lift := Raw_Subst : (γ' -> Raw_Syntax γ) -> (Raw_Syntax γ' -> Raw_Syntax γ) ]
  we show
  [ id_left_Raw_Subst : forall (f : γ' -> Raw_Syntax γ) , (fun a => lift f (return a)) = f ] 
  [ id_right_Raw_Subst : lift return = idfun : Raw_Syntax γ -> Raw_Syntax γ]
  [ assoc_Raw_Subst : (lift g) o (lift f) = lift ((lift g) o f) ]
*)
 
(* TODO: upstream *)
Arguments Raw_Context_Map_Extending {_ _ _ _} _ _ _.

Section Raw_Subst_Assoc.

  Context `{H_Funext : Funext}.
  Context {σ : Shape_System}.
  Context {Σ : Signature σ}.

  (* For the proof of functoriality of substitution, we first  *)

  Fixpoint comp_Raw_Weaken {γ γ' γ'' : σ} (f : γ -> γ') (f' : γ' -> γ'')
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Weaken (f' o f) e = Raw_Weaken f' (Raw_Weaken f e).
  Proof.
    destruct e as [ γ i | γ S args ].
  - reflexivity.
  - cbn. apply ap. apply path_forall; intros i.
    refine (_ @ _). Focus 2.
    + apply comp_Raw_Weaken.
    + apply ap10. refine (apD10 _ _). apply ap.
      apply path_arrow.
      refine (coproduct_rect _ _ _ _); intros x. 
      * refine (_ @ _^). { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      * refine (_ @ _^). { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
  Defined.

  (* todo: id_Raw_Weaken *)

  (* TODO: move *)
  Definition id_Raw_Context (γ : σ) : Raw_Context_Map Σ γ γ.
  Proof.
    exact (@var_raw _ _ _).
  Defined.

  Lemma id_Raw_Context_Map_Extending {γ δ} 
    : Raw_Context_Map_Extending δ (id_Raw_Context γ)
    = id_Raw_Context _.
  Proof.
    apply path_arrow.
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn; intros i.
    - refine (coproduct_comp_inj1 _).
    - refine (coproduct_comp_inj2 _).
  Defined.

  Definition id_left_Raw_Subst {γ γ' : σ} (f : Raw_Context_Map Σ γ' γ) (x : _)
    : Raw_Subst f (var_raw x) = f x.
  Proof.
    apply idpath.
  Defined.

  Fixpoint id_right_Raw_Subst {γ : σ} {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Subst (id_Raw_Context γ) e = e.
  Proof.
    destruct e as [ γ i | γ S args ].
    - apply idpath.
    - cbn. apply ap.
      apply path_forall; intros i.
      eapply concat.
      { eapply ap10. refine (apD10 _ _). apply ap.
        apply id_Raw_Context_Map_Extending.
      }
      apply id_right_Raw_Subst.
  Defined.

  (* TODO: rename [Raw_Weaken] to something like [Raw_Reindex_Variables] ?? *)

  Fixpoint Raw_Weaken_Raw_Subst {γ γ' γ'' : σ} (f : Raw_Context_Map Σ γ' γ) (g : γ' -> γ'')
      {cl} (e : Raw_Syntax Σ cl γ)
    : Raw_Weaken g (Raw_Subst f e)
    = Raw_Subst ((Raw_Weaken g) o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply Raw_Weaken_Raw_Subst. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    (* TODO: extract as lemma about [Raw_Context_Map_Extending] ? *)
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_^ @ _^). { apply comp_Raw_Weaken. }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine (_^ @ _). { apply comp_Raw_Weaken. }
      apply ap10. refine (apD10 _ _). apply ap. apply path_arrow. intros y.
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      cbn. refine (_^).
      eapply concat. { refine (coproduct_comp_inj2 _). }
      apply ap. refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Fixpoint Raw_Subst_Raw_Weaken {γ γ' γ'' : σ} (f : γ -> γ') (g : Raw_Context_Map Σ γ'' γ')
      {cl} (e : Raw_Syntax Σ cl γ)
    : Raw_Subst g (Raw_Weaken f e)
    = Raw_Subst (g o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply Raw_Subst_Raw_Weaken. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Fixpoint assoc_Raw_Subst {γ γ' γ'': σ}
      (f : Raw_Context_Map Σ γ' γ)
      (f' : Raw_Context_Map Σ γ'' γ')
      {cl : Syn_Class} (e : Raw_Syntax Σ cl γ)
    : Raw_Subst f' (Raw_Subst f e) = Raw_Subst (fun i => Raw_Subst f' (f i)) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply assoc_Raw_Subst. }
    apply ap10. refine (apD10 _ _). apply ap.
    apply path_arrow.
    (* TODO: break out the following as a lemma about [Raw_Context_Map_Extending]? *)
    simple refine (coproduct_rect (shape_is_coproduct) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_ @ _^). Focus 2. refine (coproduct_comp_inj1 _).
      eapply concat. { apply Raw_Subst_Raw_Weaken. }
      eapply concat. Focus 2. { eapply inverse, Raw_Weaken_Raw_Subst. } Unfocus.
      apply ap10. refine (apD10 _ _). apply ap. apply path_arrow. intros ?.
      refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      refine (_ @ _^). Focus 2. refine (coproduct_comp_inj2 _).
      cbn. refine (coproduct_comp_inj2 _).
  Defined.

End Raw_Subst_Assoc.
