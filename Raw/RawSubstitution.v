Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.

(* Substitution on raw syntax [substitute] is defined in [Raw.Syntax].
  In this file we prove key properties of it; in particular, that raw context maps form a category (modulo truncation assumptions).

  Note: we assume functional extensionality throughout.  That shouldn’t be essentially necessary — it should be possible to show that e.g. [Substitution.rename] respects “recursive extensional equality” of terms, and so on, and hence to show that raw context maps form a category modulo this equality — but using funext makes life a lot simpler. *)

Section Auxiliary.

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition transport_rename {γ γ' : σ} (g : γ -> γ')
      {cl cl' : syntactic_class} (p : cl = cl') (e : raw_expression Σ cl γ)
    : transport (fun cl => raw_expression Σ cl γ') p (Substitution.rename g e)
      = Substitution.rename g (transport (fun cl => raw_expression Σ cl γ) p e).
  Proof.
    destruct p. apply idpath.
  Defined.

  Local Definition transport_substitute {γ γ' : σ} (g : _)
      {cl cl' : syntactic_class} (p : cl = cl') (e : raw_expression Σ cl γ)
    : transport (fun cl => raw_expression Σ cl γ') p (substitute g e)
      = substitute g (transport (fun cl => raw_expression Σ cl γ) p e).
  Proof.
    destruct p. apply idpath.
  Defined.

End Auxiliary.

(* Outline: first we show functoriality of [raw_variable_substitution]; this is completely direct. *)

Section RawWeakenFunctoriality.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Fixpoint comp_Raw_Weaken {γ γ' γ'' : σ} (f : γ -> γ') (f' : γ' -> γ'')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : Substitution.rename (f' o f) e = Substitution.rename f' (Substitution.rename f e).
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

End RawWeakenFunctoriality.


Section Raw_Context_Category_Structure.
(* Identity and composition of raw context maps. *)

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition id_Raw_Context (γ : σ) : Context.map Σ γ γ.
  Proof.
    exact (@raw_variable _ _ _).
  Defined.

  Local Definition comp_Raw_Context {γ γ' γ'': σ}
      (f : Context.map Σ γ' γ)
      (f' : Context.map Σ γ'' γ')
    : Context.map Σ γ'' γ
  := fun x => substitute f' (f x).

End Raw_Context_Category_Structure.

(* Just as the definition of substitution resembles the “lift” operation of a Kleisli-style monad, similarly, its “functoriality” is naturally proved in a form similar to the laws of a Kleisli-style monad.  That is, in terms of
  [ return := raw_variable : γ -> Raw_Syntax γ ]
  [ lift := substitute : (γ' -> Raw_Syntax γ) -> (Raw_Syntax γ' -> Raw_Syntax γ) ]
  we show roughly:
  [ id_left_Raw_Subst : forall (f : γ' -> Raw_Syntax γ) , (fun a => lift f (return a)) = f ]
  [ id_right_Raw_Subst : lift return = idfun : Raw_Syntax γ -> Raw_Syntax γ]
  [ assoc_Raw_Subst : (lift g) o (lift f) = lift ((lift g) o f) ]

  These then suffice to show that raw context maps (roughly, the Kleisli category of this not-exactly-monad) form a category (modulo h-levels).

  TODO: see if this “looks like a monad” can be made more precise: does our approach fit into e.g. relative monads?
*)
Section Raw_Subst_Assoc.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (* For the proof of functoriality of substitution, we first  *)

  Lemma id_Raw_Context_Map_Extending {γ δ : σ}
    : Substitution.extend _ _ δ (@id_Raw_Context _ Σ γ)
    = id_Raw_Context _.
  Proof.
    apply path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros i.
    - refine (coproduct_comp_inj1 _).
    - refine (coproduct_comp_inj2 _).
  Defined.

  Local Definition id_left_Raw_Subst {γ γ' : σ} (f : Context.map Σ γ' γ) (x : _)
    : substitute f (raw_variable x) = f x.
  Proof.
    apply idpath.
  Defined.

  Local Fixpoint id_right_Raw_Subst {γ : σ} {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute (id_Raw_Context γ) e = e.
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

  Local Fixpoint Raw_Weaken_Raw_Subst {γ γ' γ'' : σ}
      (f : Context.map Σ γ' γ) (g : γ' -> γ'')
      {cl} (e : raw_expression Σ cl γ)
    : Substitution.rename g (substitute f e)
      = substitute ((Substitution.rename g) o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply Raw_Weaken_Raw_Subst. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    (* TODO: extract as lemma about [Raw_Context_Map_Extending] ? *)
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
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

  Local Fixpoint Raw_Subst_Raw_Weaken {γ γ' γ'' : σ} (f : γ -> γ') (g : Context.map Σ γ'' γ')
      {cl} (e : raw_expression Σ cl γ)
    : substitute g (Substitution.rename f e)
    = substitute (g o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply Raw_Subst_Raw_Weaken. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Local Fixpoint assoc_Raw_Subst {γ γ' γ'': σ}
      (f : Context.map Σ γ' γ)
      (f' : Context.map Σ γ'' γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute f' (substitute f e) = substitute (fun i => substitute f' (f i)) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply assoc_Raw_Subst. }
    apply ap10. refine (apD10 _ _). apply ap.
    apply path_arrow.
    (* TODO: break out the following as a lemma about [Raw_Context_Map_Extending]? *)
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
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

(* Finally, the category laws for raw context maps. *)
Section Raw_Context_Category.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Lemma id_left_Raw_Context {γ} (f : Context.map Σ γ γ)
    : comp_Raw_Context (id_Raw_Context _) f = f.
  Proof.
    apply idpath.
    (* To understand this, uncomment the following: *)
    (* [unfold comp_Raw_Context, id_Raw_Context.] *)
  Defined.

  Lemma id_right_Raw_Context {γ} (f : Context.map Σ γ γ)
    : comp_Raw_Context f (id_Raw_Context _) = f.
  Proof.
    apply path_forall; intros x; cbn.
    apply id_right_Raw_Subst.
  Defined.

  Lemma assoc_Raw_Context {γ0 γ1 γ2 γ3: σ}
      (f0 : Context.map Σ γ0 γ1)
      (f1 : Context.map Σ γ1 γ2)
      (f2 : Context.map Σ γ2 γ3)
    : comp_Raw_Context f2 (comp_Raw_Context f1 f0)
    = comp_Raw_Context (comp_Raw_Context f2 f1) f0.
  Proof.
    apply path_forall; intros x; unfold comp_Raw_Context; cbn.
    refine _^. apply assoc_Raw_Subst.
  Defined.

End Raw_Context_Category.


(* Here we give naturality of weakening/substitution with respect to signature maps *)
Section Naturality.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ Σ' : signature σ} (f : Signature.map Σ Σ').

  Local Fixpoint fmap_rename {γ γ' : σ} (g : γ -> γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : Expression.fmap f (Substitution.rename g e)
      = Substitution.rename g (Expression.fmap f e).
  Proof.
    destruct e as [ γ i | γ S args ].
  - apply idpath.
  - simpl.
    eapply concat.
    { apply ap, ap, ap. apply path_forall; intros i. apply fmap_rename. }
    eapply concat. Focus 2. { apply transport_rename. } Unfocus.
    apply ap. cbn. apply ap.
    set (ΣfS := Σ' (f S)). change (symbol_arity (f S)) with (snd ΣfS).
    set (p := Family.map_commutes f S : ΣfS = _). clearbody p ΣfS.
    rewrite <- (inv_V p).
    set (p' := p^); clearbody p'; clear p.
    destruct p'; apply idpath.
  Defined.
  (* NOTE: this proof was surprisingly difficult to write; it shows the kind of headaches caused by the appearance of equality in maps of signatures. *)
  
  Local Definition fmap_extend
    {γ γ' δ : σ} (g : raw_substitution γ' γ)
    : fmap_raw_context_map f (Substitution.extend _ _ δ g)
    = Substitution.extend _ _ δ (fmap_raw_context_map f g).
  Proof.
    apply path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i. unfold fmap_raw_context_map.
      eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply fmap_rename. }
      apply inverse. refine (coproduct_comp_inj1 _).
    - intros i. unfold fmap_raw_context_map.
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      apply inverse. refine (coproduct_comp_inj2 _).
  Defined.
  
  Local Fixpoint fmap_substitute
      {γ γ'} (g : Context.map Σ γ' γ)
      {cl} (e : raw_expression Σ cl γ)
    : Expression.fmap f (substitute g e)
    = substitute (fmap_raw_context_map f g) (Expression.fmap f e).
  Proof.
    destruct e as [ γ i | γ S args ].
    - apply idpath.
    - simpl.
      eapply concat.
      { apply ap, ap, ap. apply path_forall; intros i. apply fmap_substitute. }
      eapply concat. Focus 2. { apply transport_substitute. } Unfocus.
      apply ap. cbn. apply ap.
      set (ΣfS := Σ' (f S)). change (symbol_arity (f S)) with (snd ΣfS).
      set (p := Family.map_commutes f S : ΣfS = _). clearbody p ΣfS.
      rewrite <- (inv_V p).
      set (p' := p^); clearbody p'; clear p.
      destruct p'. cbn.
      apply path_forall; intros i.
      apply ap10. refine (apD10 _ _). apply ap.
      apply fmap_extend.
  Defined.

End Naturality.
