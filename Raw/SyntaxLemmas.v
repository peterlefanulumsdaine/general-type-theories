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
    : transport (fun cl => raw_expression Σ cl γ') p (rename g e)
      = rename g (transport (fun cl => raw_expression Σ cl γ) p e).
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

(* Outline: first we show functoriality of [rename]; this is completely direct. *)

Section RawWeakenFunctoriality.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Fixpoint rename_comp {γ γ' γ'' : σ} (f : γ -> γ') (f' : γ' -> γ'')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : rename (f' o f) e = rename f' (rename f e).
  Proof.
    destruct e as [ γ i | γ S args ].
  - reflexivity.
  - cbn. apply ap. apply path_forall; intros i.
    refine (_ @ _).
    2: { apply rename_comp. }
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

  Lemma rename_idmap {γ} {cl} (e : raw_expression Σ cl γ)
    : rename idmap e = e.
  Proof.
    induction e as [ γ i | γ s es IH_es ].
    - apply idpath.
    - cbn. apply ap.
      apply path_forall; intros i.
      eapply concat.
      2: { apply IH_es. }
      apply ap10. refine (apD10 _ _). apply ap.
      apply path_forall. refine (coproduct_rect shape_is_sum _ _ _).
      + intros j. refine (coproduct_comp_inj1 _).
      + intros j. refine (coproduct_comp_inj2 _).
  Defined.

End RawWeakenFunctoriality.


Section Raw_Context_Category_Structure.
(* Identity and composition of raw context maps. *)

  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Local Definition id_raw_context (γ : σ) : Context.map Σ γ γ.
  Proof.
    exact (@raw_variable _ _ _).
  Defined.

  Local Definition comp_raw_context {γ γ' γ'': σ}
      (f : Context.map Σ γ' γ)
      (f' : Context.map Σ γ'' γ')
    : Context.map Σ γ'' γ
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

  Local Definition id_left_substitute {γ γ' : σ} (f : Context.map Σ γ' γ) (x : _)
    : substitute f (raw_variable x) = f x.
  Proof.
    apply idpath.
  Defined.

  (* Note: proof literally identical to that of [rename_idmap]! *)
  Lemma substitute_idmap {γ} {cl} (e : raw_expression Σ cl γ)
    : substitute (id_raw_context γ) e = e.
  Proof.
    induction e as [ γ i | γ s es IH_es ].
    - apply idpath.
    - cbn. apply ap.
      apply path_forall; intros i.
      eapply concat.
      2: { apply IH_es. }
      apply ap10. refine (apD10 _ _). apply ap.
      apply path_forall. refine (coproduct_rect shape_is_sum _ _ _).
      + intros j. refine (coproduct_comp_inj1 _).
      + intros j. refine (coproduct_comp_inj2 _).
  Defined.

  (* We provide this under two names: [substitute_idmap] follows general
     naming conventions for recognising it when it arises in derivations;
     [id_right_substitute] fits the monad-law structure, for when it’s being
     used in those terms. *)
  Local Fixpoint id_right_substitute {γ : σ} {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute (id_raw_context γ) e = e
  := substitute_idmap e.

  Local Fixpoint rename_substitute {γ γ' γ'' : σ}
      (f : Context.map Σ γ' γ) (g : γ' -> γ'')
      {cl} (e : raw_expression Σ cl γ)
    : rename g (substitute f e)
      = substitute ((rename g) o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply rename_substitute. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_^ @ _^). { apply rename_comp. }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine (_^ @ _). { apply rename_comp. }
      apply ap10. refine (apD10 _ _). apply ap. apply path_arrow. intros y.
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      cbn. refine (_^).
      eapply concat. { refine (coproduct_comp_inj2 _). }
      apply ap. refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Fixpoint substitute_rename {γ γ' γ'' : σ} (f : γ -> γ') (g : Context.map Σ γ'' γ')
      {cl} (e : raw_expression Σ cl γ)
    : substitute g (rename f e)
    = substitute (g o f) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply substitute_rename. }
    apply ap10. refine (apD10 _ _). apply ap. apply path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { refine (coproduct_comp_inj1 _). }
      refine _^. refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine _^. refine (coproduct_comp_inj2 _).
  Defined.

  Local Fixpoint assoc_substitute {γ γ' γ'': σ}
      (f : Context.map Σ γ' γ)
      (f' : Context.map Σ γ'' γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute f' (substitute f e) = substitute (fun i => substitute f' (f i)) e.
  Proof.
    destruct e as [ γ i | γ S args ].
    { apply idpath. }
    cbn. apply ap. apply path_forall; intros i.
    eapply concat. { apply assoc_substitute. }
    apply ap10. refine (apD10 _ _). apply ap.
    apply path_arrow.
    simple refine (coproduct_rect (shape_is_sum) _ _ _); cbn; intros x.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      refine (_ @ _^).
      2 : { refine (coproduct_comp_inj1 _). }
      + eapply concat. { apply substitute_rename. }
        eapply concat.
        2: { eapply inverse, rename_substitute. }
        * apply ap10. refine (apD10 _ _). apply ap. apply path_arrow. intros ?.
          refine (coproduct_comp_inj1 _).
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      refine (_ @ _^).
      2: { refine (coproduct_comp_inj2 _). }
      + cbn. refine (coproduct_comp_inj2 _).
  Defined.

  (* Alias of [assoc_substitute], to fit general naming conventions for
     equational lemmas *)
  Definition substitute_substitute {γ γ' γ'': σ}
      (f : Context.map Σ γ' γ)
      (f' : Context.map Σ γ'' γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : substitute f' (substitute f e) = substitute (fun i => substitute f' (f i)) e
  := assoc_substitute f f' e.

End Substitute_Laws.

(* Finally, the category laws for raw context maps. *)
Section Raw_Context_Category.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  Lemma id_left_raw_context {γ} (f : Context.map Σ γ γ)
    : comp_raw_context (id_raw_context _) f = f.
  Proof.
    apply idpath.
    (* To understand this, uncomment the following: *)
    (* [unfold comp_raw_context, id_raw_context.] *)
  Defined.

  Lemma id_right_raw_context {γ} (f : Context.map Σ γ γ)
    : comp_raw_context f (id_raw_context _) = f.
  Proof.
    apply path_forall; intros x; cbn.
    apply id_right_substitute.
  Defined.

  Lemma assoc_raw_context {γ0 γ1 γ2 γ3: σ}
      (f0 : Context.map Σ γ0 γ1)
      (f1 : Context.map Σ γ1 γ2)
      (f2 : Context.map Σ γ2 γ3)
    : comp_raw_context f2 (comp_raw_context f1 f0)
    = comp_raw_context (comp_raw_context f2 f1) f0.
  Proof.
    apply path_forall; intros x; unfold comp_raw_context; cbn.
    refine _^. apply assoc_substitute.
  Defined.

End Raw_Context_Category.

Section Derived_Lemmas.
(** In this section: lemmas on the derived forms of renaming and substitution (i.e. into boundaries, judgements, etc) that are easily derived formally from the main lemmas above. *)

  Context `{H_Funext : Funext}.
  Context {σ : shape_system} {Σ : signature σ}.

  Definition rename_rename_judgement
      (J : judgement_total Σ)
      {γ' : shape_carrier σ} (e : γ' <~> shape_of_judgement J)
      {γ'' : shape_carrier σ} (e' : γ'' <~> γ')
    : Judgement.rename (Judgement.rename J e) e'
      = Judgement.rename J (equiv_compose e e').
  Proof.
    destruct J as [ [ | hjf ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)),
            (ap make_context_judgement),
            (ap (Build_raw_context _)).
      apply path_forall; cbn; intros i.
      apply inverse, rename_comp.
    - (* hypothetical judgement *)
      apply Judgement.eq_by_expressions; cbn.
      + intros i. apply inverse, rename_comp.
      + intros i. unfold rename_hypothetical_judgement; cbn.
        apply inverse, rename_comp.
  Defined.

  Definition rename_judgement_idmap
      (J : judgement_total Σ)
    : Judgement.rename J (equiv_idmap _)
      = J.
  Proof.
    destruct J as [ [ | hjf ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)).
      eapply concat.
      { eapply (ap make_context_judgement),
               (ap (Build_raw_context _)).
        apply path_forall; cbn; intros i.
        apply rename_idmap. }
      apply (ap (Build_judgement _)), contr_unit.
    - (* hypothetical judgement *)
      apply Judgement.eq_by_expressions; cbn.
      + intros i. apply rename_idmap.
      + intros i. unfold rename_hypothetical_judgement; cbn.
        apply rename_idmap.
  Defined.

  Definition rename_judgement_inverse
      (J : judgement_total Σ)
      {γ' : shape_carrier σ} (e : shape_of_judgement J <~> γ')
    : Judgement.rename (Judgement.rename J (e^-1)) e = J.
  Proof.
    eapply concat. { apply rename_rename_judgement. }
    eapply concat. 2: { apply rename_judgement_idmap. }
    apply ap, ecompose_Ve.
  Defined.

  Lemma judgement_eq_rename_iff_eq_rename_inverse
      (J J' : judgement_total Σ)
      (e : shape_of_judgement J <~> shape_of_judgement J')
    : J' = Judgement.rename J (e^-1)
      <-> Judgement.rename J' e = J.
  Proof.
    (* surprisingly subtle *)
  Admitted.

  Lemma rename_hypothetical_boundary_idmap
      {Σ'} {γ : σ} {hjf} (B : Judgement.hypothetical_boundary Σ' hjf γ)
    : rename_hypothetical_boundary idmap B = B.
  Proof.
    apply path_forall; intros i.
    apply rename_idmap.
  Defined.

End Derived_Lemmas.

(* Here we give naturality of weakening/substitution with respect to signature maps *)
Section Naturality.

  Context `{H_Funext : Funext}.
  Context {σ : shape_system}.
  Context {Σ Σ' : signature σ} (f : Signature.map Σ Σ').

  (* ad hoc lemma, used for [fmap_rename], [fmap_substitute]. *)
  Local Lemma inverse_sufficient {X} {x y:X} (P : x = y -> Type)
    : (forall e, P (e^)^) -> (forall e, P e).
  Proof.
    intros H e.
    eapply transport.
    - eapply inv_V.
    - apply H.
  Defined.

  Local Fixpoint fmap_rename {γ γ' : σ} (g : γ -> γ')
      {cl : syntactic_class} (e : raw_expression Σ cl γ)
    : Expression.fmap f (rename g e)
      = rename g (Expression.fmap f e).
  Proof.
    destruct e as [ γ i | γ S args ].
  - apply idpath.
  - simpl.
    eapply concat.
    { apply ap, ap, ap. apply path_forall; intros i. apply fmap_rename. }
    eapply concat.
    2: { apply transport_rename. }
    + apply ap. cbn. apply ap.
      set (ΣfS := Σ' (f S)). change (symbol_arity (f S)) with (snd ΣfS).
      set (p := Family.map_commutes f S : ΣfS = _). clearbody p ΣfS.
      revert p; apply inverse_sufficient; intros p.
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
      eapply concat. 2: { apply transport_substitute. }
      + apply ap. cbn. apply ap.
        set (ΣfS := Σ' (f S)). change (symbol_arity (f S)) with (snd ΣfS).
        set (p := Family.map_commutes f S : ΣfS = _). clearbody p ΣfS.
        revert p; apply inverse_sufficient; intros p.
        set (p' := p^); clearbody p'; clear p.
        destruct p'. cbn.
        apply path_forall; intros i.
        apply ap10. refine (apD10 _ _). apply ap.
        apply fmap_extend.
  Defined.

End Naturality.


Section Fmap_Instantiation.
(** Interaction between instantiation of metavariables and translation along signature maps. *)

  Context {σ : shape_system} `{Funext}.

  Lemma fmap_instantiate_expression
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} {γ : σ}
      (I : Metavariable.instantiation a Σ γ)
      {cl} {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
    : Expression.fmap f (Metavariable.instantiate_expression I e)
    = Metavariable.instantiate_expression
        (fmap_instantiation f I)
        (Expression.fmap (Metavariable.fmap1 f a) e).
  Proof.
    induction e as [ δ i | δ [S | M] e_args IH_e_args ].
    - apply idpath.
    - simpl Metavariable.instantiate_expression. simpl Expression.fmap.
      assert (instantiate_expression_transport_cl
        : forall γ δ (I : Metavariable.instantiation a Σ' γ)
                 cl cl' (p : cl = cl') (e : raw_expression _ cl δ),
              Metavariable.instantiate_expression I
                 (transport (fun cl => raw_expression _ cl _) p e)
            = transport (fun cl => raw_expression _ cl _) p
                 (Metavariable.instantiate_expression I e)).
      { intros ? ? ? ? ? p ?. destruct p; apply idpath. }
      eapply concat.
      2: { apply inverse, instantiate_expression_transport_cl. }
      clear instantiate_expression_transport_cl.
      apply ap. simpl. apply ap.
      (* Now that we are under [raw_symbol S], we fold/abstract [Σ S], [Σ' (f S)], and then destruct [Family.map_commutes f S], to avoid having to deal explicitly with the transports. Making sure all instances are folded is a little fiddly. *)
      unfold symbol_arity in *. cbn in *.
      set (ΣS := Σ S) in *. set (ΣfS := Σ' (f S)) in *.
      change (Σ' (f.(proj1_sig) S)) with ΣfS.
      change (Family.map_over_commutes f) with (Family.map_commutes f).
      set (e_S := Family.map_commutes f S : ΣfS = ΣS).
      clearbody e_S ΣS ΣfS.
      destruct e_S. simpl transport.
      apply path_forall; intros i.
      eapply concat. { apply fmap_rename. }
      apply ap. apply IH_e_args.
    - simpl Metavariable.instantiate_expression.
      eapply concat. { apply fmap_substitute. }
      unfold fmap_raw_context_map, fmap_instantiation.
      apply ap10. refine (apD10 _ _). apply ap.
      apply path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. apply inverse. refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply fmap_rename. }
        eapply concat. { apply ap, IH_e_args. }
        eapply inverse. { refine (coproduct_comp_inj2 _). }
  Defined.

  
  Definition fmap_instantiate_context
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {Γ : raw_context Σ} (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context (Metavariable.extend Σ a))
    : Context.fmap f (Metavariable.instantiate_context Γ I Δ)
    = Metavariable.instantiate_context
        (Context.fmap f Γ)
        (fmap_instantiation f I)
        (Context.fmap (Metavariable.fmap1 f a) Δ).
  Proof.
    apply (ap (Build_raw_context _)), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _); intros i;
      unfold Metavariable.instantiate_context.
    - eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
      apply fmap_rename.
    - eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
      apply fmap_instantiate_expression.
  Defined.

  Lemma fmap_instantiate_judgement
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} (Γ : raw_context Σ)
      (I : Metavariable.instantiation a Σ Γ)
      (J : judgement_total (Metavariable.extend _ _))
    : fmap_judgement_total f (Metavariable.instantiate_judgement Γ I J)
    = Metavariable.instantiate_judgement
        (Context.fmap f Γ) 
        (fmap_instantiation f I)
        (fmap_judgement_total (Metavariable.fmap1 f a) J).
  Proof.
    destruct J as [[ | ] J].
    - (* context judgement *)
      apply (ap (Build_judgement_total _)), (ap (fun Γ => Build_judgement Γ _)).
      cbn. apply fmap_instantiate_context.
    - (* hypothetical judgement *)
      apply Judgement.eq_by_expressions. 
      + (* context part *)
        refine (coproduct_rect shape_is_sum _ _ _); intros i;
          unfold Metavariable.instantiate_context.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. 2: {apply inverse. refine (coproduct_comp_inj1 _). }
          apply fmap_rename.
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. 2: {apply inverse. refine (coproduct_comp_inj2 _). }
          apply fmap_instantiate_expression.
      + intros i; apply fmap_instantiate_expression.
  Defined.

End Fmap_Instantiation.

Section Subst_Instantiation.
(** Interaction between instantiation of metavariables and substitution/renaming. *)

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  Lemma instantiate_rename
      {cl} {a : @arity σ} {γ : σ}
      (I : Metavariable.instantiation a Σ γ)
      {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
      {δ' : σ} (f : δ -> δ')
    : Metavariable.instantiate_expression I (rename f e)
    = rename
        (coproduct_rect shape_is_sum _
          (coproduct_inj1 shape_is_sum)
          ((coproduct_inj2 shape_is_sum) o f))
        (Metavariable.instantiate_expression I e).
  Proof.
    revert δ' f.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ]; intros δ' f.
    - (* [e] is a variable *)
      cbn. apply ap, inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply inverse, rename_comp. }
      apply inverse.
      eapply concat. { apply inverse, rename_comp. }
      apply (ap (fun f => rename f _)).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - (* [e] is a metavariable from [a] *)
      simpl.
      eapply concat. 2: { apply inverse, rename_substitute. }
      apply (ap (fun f => substitute f _)).
      apply path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. apply ap. refine (coproduct_comp_inj1 _).
      + eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, IH_e_args. }
        eapply concat. { apply inverse, rename_comp. }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply inverse, rename_comp. }
        apply (ap (fun f => rename f _)). 
        apply path_forall.
        repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          apply ap. refine (coproduct_comp_inj1 _). 
        * revert j. apply empty_rect, shape_is_empty.
  Defined.

  Lemma instantiate_substitute
      {cl} {a : @arity σ} {γ : σ}
      (I : Metavariable.instantiation a Σ γ)
      {δ} (e : raw_expression (Metavariable.extend Σ a) cl δ)
      {δ' : σ} (f : raw_substitution δ' δ)
    : Metavariable.instantiate_expression I (substitute f e)
    = substitute
        (coproduct_rect shape_is_sum _
          (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
          (fun i => Metavariable.instantiate_expression I (f i)))
        (Metavariable.instantiate_expression I e).
  Proof.
    revert δ' f.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ]; intros δ' f.
    - (* [e] is a variable *)
      simpl. apply inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply rename_substitute. }
      apply inverse.
      eapply concat. { apply substitute_rename. }
      apply (ap (fun f => substitute f _)).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        simpl; apply ap. refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap, instantiate_rename. }
        eapply concat. { apply inverse, rename_comp. }
        apply (ap (fun f => rename f _)).
        apply path_forall. refine (coproduct_rect shape_is_sum _ _ _); intros k.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        simpl. apply ap. 
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - (* [e] is a metavariable from [a] *)
      simpl.
      eapply concat. 2: { apply inverse, substitute_substitute. }
      apply (ap (fun f => substitute f _)).
      apply path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. refine (coproduct_comp_inj1 _).
      + eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, IH_e_args. }
        eapply concat. { apply rename_substitute. }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply substitute_rename. }
        apply (ap (fun f => substitute f _)). 
        apply path_forall.
        repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          cbn. apply ap. refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { apply ap, instantiate_rename. }
          eapply concat. { apply inverse, rename_comp. }
          eapply concat. 2: { apply rename_idmap. }
          apply (ap (fun f => rename f _)).
          apply path_forall.
          refine (coproduct_rect shape_is_sum _ _ _); intros k.
          -- eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
           refine (coproduct_comp_inj1 _).
          -- eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
           eapply concat. { refine (coproduct_comp_inj2 _). }
           apply ap. refine (coproduct_comp_inj1 _).
        * revert j. apply empty_rect, shape_is_empty.
  Defined.

End Subst_Instantiation.


Section Instantiations.
(** Double instantiations. *)

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  (* TODO: upstream to [ShapeSystems], or [Coproduct]? *)
  Definition shape_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 shape_is_sum
               : γ -> shape_sum γ (shape_empty _)).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + intros i; exact i.
      + apply (empty_rect _ shape_is_empty).
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + intros i. apply ap.
        refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
    - intros i. refine (coproduct_comp_inj1 _).
  Defined.

  Definition shape_sum_empty_inl (γ : σ)
    : γ <~> shape_sum γ (shape_empty _)
  := BuildEquiv _ _ _ (shape_sum_empty_inl_is_equiv γ).

  (* TODO: upstream to [ShapeSystems], or [Coproduct]? *)
  Definition shape_sum_empty_inr_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj2 shape_is_sum
               : γ -> shape_sum (shape_empty _) γ).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + apply (empty_rect _ shape_is_empty).
      + intros i; exact i.
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + apply (empty_rect _ shape_is_empty).
      + intros i. apply ap.
        refine (coproduct_comp_inj2 _).
    - intros i. refine (coproduct_comp_inj2 _).
  Defined.

  Definition shape_sum_empty_inr (γ : σ)
    : γ <~> shape_sum (shape_empty _) γ
  := BuildEquiv _ _ _ (shape_sum_empty_inr_is_equiv γ).

  (* TODO: upstream to [ShapeSystems], or [Coproduct]? *)
  (* TODO: unify with [Coproduct.assoc] *)
  Definition shape_assoc (γ δ κ : shape_carrier σ)
    : shape_sum γ (shape_sum δ κ) <~> shape_sum (shape_sum γ δ) κ.
  Proof.
    simple refine (equiv_adjointify _ _ _ _); unfold Sect.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj1 shape_is_sum), (coproduct_inj2 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj2 shape_is_sum), (coproduct_inj1 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj2 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
  Defined.

  Instance shape_assoc_is_equiv {γ δ κ} : IsEquiv (shape_assoc γ δ κ)
    := equiv_isequiv (shape_assoc _ _ _).

  (* NOTE: it feels like there should be a more systematic way to present the following lemmas — some kind of monadic structure on extensions/instantiations. Contemplate this, and try to figure it out? *)

  (* TODO: upstream to [Raw.Syntax.Metavariable]? *)
  Definition unit_instantiation (a : arity σ)
    : Metavariable.instantiation a (Metavariable.extend Σ a) (shape_empty σ).
  Proof.
    intros A.
    refine (raw_symbol (include_metavariable A) _).
    intros i. apply raw_variable.
    refine (coproduct_inj1 shape_is_sum _).
    refine (coproduct_inj2 shape_is_sum _).
    exact i.
  Defined.

  Lemma unit_instantiate_expression {a}
      {cl} {γ} (e : raw_expression (Metavariable.extend Σ a) cl γ)
    : instantiate_expression (unit_instantiation a)
        (Expression.fmap (Metavariable.fmap1 include_symbol _) e)
      = rename (coproduct_inj2 shape_is_sum) e.
  Proof.
    induction e as [ γ i | γ [S | M] args IH ].
    - apply idpath.
    - simpl. 
      apply ap, path_forall; intros i.
      eapply concat. { apply ap, IH. }
      eapply concat. { apply inverse, rename_comp. }
      apply (ap (fun f => rename f _)), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse. refine (coproduct_comp_inj1 _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse. refine (coproduct_comp_inj2 _).
    - simpl.
      apply ap, path_forall; intros i.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      eapply concat. { apply ap, ap, IH. }
      apply inverse.
      eapply concat. 2: { apply rename_comp. }
      eapply concat. 2: { apply rename_comp. } 
      apply (ap (fun f => rename f _)), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros x.
        eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse. 
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply ap, ap. refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
  Defined.

  Lemma unit_instantiate_context
      {a} (Γ : raw_context (Metavariable.extend Σ a))
    : Metavariable.instantiate_context [::] (unit_instantiation a)
        (Context.fmap (Metavariable.fmap1 include_symbol _) Γ)
      = Context.rename Γ (shape_sum_empty_inr _)^-1.
  Proof.
    apply (ap (Build_raw_context _)), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - apply (empty_rect _ shape_is_empty).
    - intros x.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      eapply concat. { apply unit_instantiate_expression. }
      apply ap, ap, inverse. cbn.
      refine (coproduct_comp_inj2 _).
  Defined.

  Lemma unit_instantiate_judgement
      {a} (J : judgement_total (Metavariable.extend Σ a))
    : Metavariable.instantiate_judgement [::] (unit_instantiation a)
        (fmap_judgement_total (Metavariable.fmap1 include_symbol _) J)
      = Judgement.rename J (shape_sum_empty_inr _)^-1.
  Proof.
    destruct J as [ [ | hjf ] J ].
    - (* context judgement *)
      destruct J as [J []].
      simpl. unfold Metavariable.instantiate_judgement, Judgement.rename. 
      apply ap, ap10, ap.
      apply unit_instantiate_context.
    - (* hypothetical judgement *)
      apply Judgement.eq_by_expressions.
      + refine (coproduct_rect shape_is_sum _ _ _).
        * apply (empty_rect _ shape_is_empty).
        * intros x.
          eapply concat. { refine (coproduct_comp_inj2 _). }
          eapply concat. { apply unit_instantiate_expression. }
          apply ap, ap, inverse. cbn.
          refine (coproduct_comp_inj2 _).
      + intros i; apply unit_instantiate_expression.
  Defined.


  (* TODO: upstream to [Raw.Syntax.Metavariable]? *)
  Definition instantiate_instantiation
      {γ} {a} (I : Metavariable.instantiation a Σ γ)
      {δ} {b} (J : Metavariable.instantiation b (Metavariable.extend Σ a) δ)
    : Metavariable.instantiation b Σ (shape_sum γ δ).
  Proof.
    intros i.
    refine (rename _ (Metavariable.instantiate_expression I (J i))).
    apply shape_assoc.
  Defined.

  Lemma instantiate_instantiate_expression 
      {γ} {a} (I : Metavariable.instantiation a Σ γ)
      {δ} {b} (J : Metavariable.instantiation b (Metavariable.extend Σ a) δ)
      {cl} {θ} (e : raw_expression (Metavariable.extend Σ b) cl θ)
    : Metavariable.instantiate_expression
        (instantiate_instantiation I J) e
    = rename (shape_assoc _ _ _)
        (Metavariable.instantiate_expression I
          (Metavariable.instantiate_expression J
            (Expression.fmap (Metavariable.fmap1 include_symbol _) e))).
  Proof.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ].
    - (* [e] is a variable *)
      cbn. apply inverse, ap.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine (coproduct_comp_inj2 _).
    - (* [e] is a symbol of [Σ] *)
      simpl Expression.fmap.
      simpl Metavariable.instantiate_expression.
      simpl rename.
      apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply inverse, rename_comp. }
      apply inverse.
      eapply concat. { apply ap, ap. apply instantiate_rename. }
      eapply concat. { apply inverse, rename_comp. }
      eapply concat. { apply inverse, rename_comp. }
      apply (ap (fun f => rename f _)).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      (* NOTE: would be better to reduce all the following to a tactic.
       (Or, better still, to have it compute!) *)
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - (* [e] is a metavariable of [b] *)
      simpl Expression.fmap.
      simpl Metavariable.instantiate_expression.
      simpl rename.
      eapply concat.
      { refine (ap (fun f => substitute f _) _).
        refine (ap (fun f => coproduct_rect _ _ _ f) _).
        refine (@path_arrow _ _ _ _ (fun i => rename _ _) _); intros i.
        apply ap, IH_e_args.   
      } clear IH_e_args.
      unfold instantiate_instantiation.
      eapply concat. { apply substitute_rename. }
      eapply inverse.
      eapply concat. { apply ap, instantiate_substitute. }
      eapply concat. { apply rename_substitute. }
      refine (ap (fun f => substitute f _) _).
      apply path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        simpl rename. eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
        cbn. eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, instantiate_rename. }
        eapply concat. { apply inverse, rename_comp. }
        apply inverse. 
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply inverse, rename_comp. }
        apply (ap (fun f => rename f _)). clear e_args.
        apply path_forall.
        repeat refine (coproduct_rect shape_is_sum _ _ _); intros k.
        * eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). } cbn.
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          refine (coproduct_comp_inj1 _).
        * eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
          apply inverse.
          eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap. refine (coproduct_comp_inj2 _). }
          eapply concat. { apply ap, ap, ap. refine (coproduct_comp_inj1 _). }
          eapply concat. { refine (coproduct_comp_inj2 _). }
          refine (coproduct_comp_inj2 _).
        * revert k. apply empty_rect, shape_is_empty.
  Defined.

  (* TODO: If we refactored judgements to put the shape as separate component throughout (i.e. so that [shape_of_judgement] computes without destructing the judgement form), then this would be cleaner (i.e. could just be [shape_assoc] in general, so could be inlined). *)
  Lemma instantiate_instantiate_shape_of_judgement
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement_total (Metavariable.extend Σ b))
  : shape_of_judgement
      (Metavariable.instantiate_judgement
        (Metavariable.instantiate_context _ I Δ)
        (instantiate_instantiation I J) j)
  <~>
    shape_of_judgement
      (Metavariable.instantiate_judgement Γ I
        (Metavariable.instantiate_judgement Δ J
          (fmap_judgement_total (Metavariable.fmap1 include_symbol _) j))).
  Proof.
    apply equiv_inverse,shape_assoc.
  Defined.

  Lemma instantiate_instantiate_context_pointwise
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (K : raw_context (Metavariable.extend Σ b))
    : forall i,
      Metavariable.instantiate_context
        (Metavariable.instantiate_context _ I Δ)
        (instantiate_instantiation I J) K i
    = Context.rename
        (Metavariable.instantiate_context Γ I
          (Metavariable.instantiate_context Δ J
            (Context.fmap (Metavariable.fmap1 include_symbol _) K)))
        (shape_assoc _ _ _)^-1
        i.
  Proof.
  repeat refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; cbn.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply inverse, rename_comp. }
      apply inverse.
      eapply concat.
      { apply ap.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      }
      eapply concat. { apply inverse, rename_comp. }
      refine (ap (fun f => rename f _) _).
      clear i. apply path_forall; intros x.
      refine (coproduct_comp_inj1 _).
    - intros i; cbn.
      eapply concat. { refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
      apply inverse.
      eapply concat.
      { apply ap.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
      }
      eapply concat. { apply ap, ap. refine (coproduct_comp_inj1 _). }
      eapply concat. { apply ap, instantiate_rename. }
      eapply concat. { apply inverse, rename_comp. }
      refine (ap (fun f => rename f _) _).
      clear i. apply path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
    - intros i.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      eapply concat. { apply instantiate_instantiate_expression. }
      refine ((ap (fun f => rename f _) _) @ ap _ _).
      + apply ap, inverse, einv_V. 
      + apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply ap. refine (coproduct_comp_inj2 _).
  Defined.

  Lemma instantiate_instantiate_judgement
      {Γ : raw_context _} {a} (I : Metavariable.instantiation a Σ Γ)
      {Δ : raw_context _} {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
      (j : judgement_total (Metavariable.extend Σ b))
    : Metavariable.instantiate_judgement
        (Metavariable.instantiate_context _ I Δ)
        (instantiate_instantiation I J) j
    = Judgement.rename
        (Metavariable.instantiate_judgement Γ I
          (Metavariable.instantiate_judgement Δ J
            (fmap_judgement_total (Metavariable.fmap1 include_symbol _) j)))
         (shape_assoc _ _ _)^-1.
  Proof.
    destruct j as [[ | jf ] j].
    - apply (ap (Build_judgement_total _)),
            (ap (fun Γ => Build_judgement Γ _)),
            (ap (fun A => Build_raw_context _ A)).
      apply path_forall.
      intros i; apply instantiate_instantiate_context_pointwise.
    - apply Judgement.eq_by_expressions.
      + apply instantiate_instantiate_context_pointwise.
      + intros i. refine (instantiate_instantiate_expression _ _ _).
  Defined.

End Instantiations.