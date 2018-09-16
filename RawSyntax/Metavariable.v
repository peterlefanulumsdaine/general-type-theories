Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.SyntacticClass.
Require Import RawSyntax.Arity.
Require Import RawSyntax.Signature.
Require Import RawSyntax.Expression.
Require Import RawSyntax.Substitution.

Section AlgebraicExtension.

  (* The extension of a signature by symbols representing metavariables, as used
  to write each rule.

  The *arity* here would be the overall argument of the constructor that the
  rule introduces: the metavariable symbols introduced correspond to the
  arguments of the arity.

  E.g. lambda-abstraction has arity < (Ty,•), (Ty,{x}), (Tm,{x}) >. So in the
  metavariable extension by this arity, we add three symbols — call them A, B,
  and b — with arities as follows:

     Symbol Class Arity
     A      Ty    < >
     B      Ty    <(Tm,•)>
     b      Tm    <(Tm,•)>

  allowing us to write judgements like x:A |– b(x) : B(x).
  *)

  Context {σ : shape_system}.

  Local Definition extend (Σ : signature σ) (a : arity σ) : signature σ.
  Proof.
    refine (Family.sum Σ _).
    refine (Family.fmap _ a).
    intros cl_γ.
    exact (fst cl_γ, Arity.simple (snd cl_γ)).
  Defined.

  Definition include_metavariable {Σ : signature σ} {a : arity σ}
    : a -> extend Σ a
  := inr.

  Local Definition include_symbol_carrier {Σ : signature σ} {a : arity σ}
    : Σ -> extend Σ a
  := inl.

  Definition include_symbol {Σ : signature σ} {a : arity σ}
     : (Signature.map Σ (extend Σ a)).
  Proof.
    exists include_symbol_carrier.
    intros; apply idpath.
  Defined.

  (* To use rules, one *instantiates* their metavariables, as raw syntax of the
     ambient signature, over some context. *)
  Local Definition instantiation (a : @arity σ) (Σ : signature σ) (γ : σ)
    : Type
  := forall i : a,
         raw_expression Σ (argument_class i) (shape_sum γ (argument_shape i)).

  (* Given such an instantiation, one can translate syntax over the extended
     signature into syntax over the base signature. *)
  Local Fixpoint instantiate_expression
      {cl} {a : @arity σ} {Σ : signature σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
    : raw_expression Σ cl (shape_sum γ δ).
  Proof.
    destruct e as [ δ i | δ [S | M] args].
  - refine (raw_variable _).
    exact (coproduct_inj2 (shape_is_sum) i).
  - refine (raw_symbol S _). intros i.
    refine (Expression.rename _
             (instantiate_expression _ _ _ _ I _ (args i))).
    apply (Coproduct.assoc
             shape_is_sum shape_is_sum
             shape_is_sum shape_is_sum).
  - simpl in M. (* Substitute [args] into the expression [I M]. *)
    refine (substitute _ (I M)).
    refine (coproduct_rect shape_is_sum _ _ _).
    + intros i. apply raw_variable, (coproduct_inj1 shape_is_sum), i.
    + intros i.
      refine (Expression.rename _
             (instantiate_expression _ _ _ _ I _ (args i))).
      cbn.
      refine (Coproduct.fmap shape_is_sum shape_is_sum _ _).
      exact (fun j => j).
      exact (Coproduct.empty_right shape_is_sum shape_is_empty).
  Defined.

  Arguments instantiate_expression {_ _ _ _} _ [_] _.

End AlgebraicExtension.

Arguments instantiate_expression : simpl nomatch.


Section MetavariableNotations.

(* Arities of symbols will arise in two ways:

  1. Arities we write by hand.

    These will typically use [< … >] notation.

  2. Arities of metavariables, from [Metavariable.extend].

    These will have only (Ty, shape_empty) arguments, and be indexed by the positions of some proto-context, which will itself probably be built up by [shape_extend].

  So we give functions/notations for giving arguments for each of these forms.

  Eventually, one should be able to write e.g.

  [S/ A ; e1 , e2 , e3 /]

  [M/ A ; e1 , e2 , e3 /]

  for the expression consisting of a symbol S (resp. a metavariable symbol M) applied to expressions e1, e2, e3.

  For now we provide the [M/ … /] version, but not yet the general [S/ … /] version.
*)

Context {σ : shape_system}.
Context {Σ : signature σ}.

Local Definition empty_args {γ}
  : arguments Σ (Arity.simple (shape_empty _)) γ
  := empty_rect _ shape_is_empty _.

Local Definition extend_args {γ δ : σ}
  : arguments Σ (Arity.simple δ) γ
    -> raw_term Σ γ
    -> arguments Σ (Arity.simple (shape_extend _ δ)) γ.
Proof.
  intros ts t.
  simple refine (plusone_rect _ _ (shape_is_extend _ δ) _ _ _); cbn.
  - refine (Expression.rename _ t).
    exact (coproduct_inj1 shape_is_sum).
  - exact ts.
Defined.

End MetavariableNotations.

Notation " '[M/' A /] " := (raw_symbol (include_metavariable A) empty_args) : syntax_scope.

Notation " '[M/' A ; x , .. , z /] "
  := (raw_symbol (include_metavariable A) (extend_args .. (extend_args (empty_args) x) .. z)) : raw_syntax_scope.

Open Scope syntax_scope.


Section Renaming.
(** Interaction of metavariable-instantiation with renaming *)

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  Lemma instantiate_rename
      {cl} {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
      {δ' : σ} (f : δ -> δ')
    : instantiate_expression I (rename f e)
    = rename
        (coproduct_rect shape_is_sum _
          (coproduct_inj1 shape_is_sum)
          ((coproduct_inj2 shape_is_sum) o f))
        (instantiate_expression I e).
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

End Renaming.



Section Substitution.

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  Lemma instantiate_substitute
      {cl} {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
      {δ' : σ} (f : raw_context_map _ δ' δ)
    : instantiate_expression I (substitute f e)
    = substitute
        (coproduct_rect shape_is_sum _
          (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
          (fun i => instantiate_expression I (f i)))
        (instantiate_expression I e).
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

End Substitution.


Section Signature_Maps.
  (** Interaction of metavariable extensions, and instantiation of metavariables, with signature maps *)
  
  Context {σ : shape_system} `{Funext}.

  (* Metavariable extension is bifunctorial in both arguments (the signature and the arity).

  We give the general bifunctoriality action as [Fmap_Family], and the special cases in each argument individually as [Fmap1], [Fmap2]. *)
  Local Definition fmap
      {Σ Σ'  : signature σ} (f : Signature.map Σ Σ')
      {a a' : arity σ} (g : Family.map a a')
    : Signature.map (extend Σ a) (extend Σ' a').
  Proof.
    apply Family.fmap_of_sum.
    - apply f.
    - apply Family.map_fmap, g.
  Defined.

  Local Definition fmap1
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (a : arity σ)
    : Signature.map (extend Σ a) (extend Σ' a)
  := fmap f (Family.idmap _).

  Local Definition fmap2
      (Σ : signature σ)
      {a a' : arity σ} (f : Family.map a a')
    : Signature.map (extend Σ a) (extend Σ a')
  := fmap (Family.idmap _) f.

  Definition fmap_instantiation
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {γ} (I : instantiation a Σ γ)
    : instantiation a Σ' γ
  := fun i => Expression.fmap f (I i).

  Local Definition fmap_idmap {Σ} {a}
    : fmap (Signature.idmap Σ) (Family.idmap a)
    = Signature.idmap (extend Σ a).
  Proof.
    apply Family.map_eq'.
    intros [S | i]; exists (idpath _); apply idpath.
  Defined.

  Local Definition fmap1_idmap {Σ} {a}
    : fmap1 (Signature.idmap Σ) a
    = Signature.idmap (extend Σ a).
  Proof.
    apply fmap_idmap.
  Defined.

  Local Definition fmap2_idmap {Σ} {a}
    : fmap2 Σ (Family.idmap a)
    = Signature.idmap (extend Σ a).
  Proof.
    apply fmap_idmap.
  Defined.

  Local Definition fmap_compose
    {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ') 
    {a a' a''} (g' : Family.map a' a'') (g : Family.map a a')
    : fmap (Signature.compose f' f) (Family.compose g' g)
    = Signature.compose (fmap f' g') (fmap f g).
  Proof.
    apply Family.map_eq'.
    intros [S | i]; exists (idpath _).
    - apply inverse, concat_1p.
    - cbn. apply inverse.
      eapply concat. { apply concat_1p. }
      eapply concat. { apply ap, ap_idmap. }
      apply inverse.
      eapply concat. { apply ap, ap, ap_idmap. }
      refine (ap_pp _ _ _).
  Defined.

  Local Definition fmap1_compose
    {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ') 
    (a : _)
    : fmap1 (Signature.compose f' f) a
    = Signature.compose (fmap1 f' a) (fmap1 f a).
  Proof.
    refine (fmap_compose _ _ (Family.idmap _) (Family.idmap _)).
  Defined.

  Local Definition fmap2_compose
    (Σ : _) 
    {a a' a''} (g' : Family.map a' a'') (g : Family.map a a')
    : fmap2 Σ (Family.compose g' g)
    = Signature.compose (fmap2 Σ g') (fmap2 Σ g).
  Proof.
    refine (fmap_compose (Signature.idmap _) (Signature.idmap _) _ _).
  Defined.

  (** Naturality of [include_symbol] w.r.t. signature maps *)
  (* TODO: consider naming *)
  Local Lemma include_symbol_after_map
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (a : arity _)
    : Signature.compose include_symbol f
      = Signature.compose (fmap1 f a) include_symbol.
  Proof.
    apply Family.map_eq'; intros S.
    exists (idpath _); cbn.
    apply ap.
    eapply concat. { apply ap_idmap. }
    apply inverse, concat_p1.
  Defined.

  Lemma fmap_instantiate_expression
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {cl} {δ} (e : raw_expression (extend Σ a) cl δ)
    : Expression.fmap f (instantiate_expression I e)
    = instantiate_expression
        (fmap_instantiation f I)
        (Expression.fmap (fmap1 f a) e).
  Proof.
    induction e as [ δ i | δ [S | M] e_args IH_e_args ].
    - apply idpath.
    - simpl instantiate_expression. simpl Expression.fmap.
      assert (instantiate_expression_transport_cl
        : forall γ δ (I : instantiation a Σ' γ)
                 cl cl' (p : cl = cl') (e : raw_expression _ cl δ),
              instantiate_expression I
                 (transport (fun cl => raw_expression _ cl _) p e)
            = transport (fun cl => raw_expression _ cl _) p
                 (instantiate_expression I e)).
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
    - simpl instantiate_expression.
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

End Signature_Maps.


Section Composition.
(** Instantiations behave something like the Kleisli maps of a monad: there are unit instantiations and composite instantiations, though at the moment we do not quite systematically package them as a well-defined structure. *)

(* TODO: contemplate this, and try to work out what monad-like structure on extensions/instantiations we are really giving in the following. *)

  Context {σ : shape_system} {Σ : signature σ}.
  Context `{Funext}.

  Definition unit_instantiation (a : arity σ)
    : instantiation a (extend Σ a) (shape_empty σ).
  Proof.
    intros A.
    refine (raw_symbol (include_metavariable A) _).
    intros i. apply raw_variable.
    refine (coproduct_inj1 shape_is_sum _).
    refine (coproduct_inj2 shape_is_sum _).
    exact i.
  Defined.

  (* Can also be seen as a composition of instantiations. *)
  Definition instantiate_instantiation
      {γ} {a} (I : instantiation a Σ γ)
      {δ} {b} (J : instantiation b (extend Σ a) δ)
    : instantiation b Σ (shape_sum γ δ).
  Proof.
    intros i.
    refine (rename _ (instantiate_expression I (J i))).
    apply shape_assoc.
  Defined.

  Lemma unit_instantiate_expression {a}
      {cl} {γ} (e : raw_expression (extend Σ a) cl γ)
    : instantiate_expression (unit_instantiation a)
        (Expression.fmap (fmap1 include_symbol _) e)
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

  Lemma instantiate_instantiate_expression 
      {γ} {a} (I : instantiation a Σ γ)
      {δ} {b} (J : instantiation b (extend Σ a) δ)
      {cl} {θ} (e : raw_expression (extend Σ b) cl θ)
    : instantiate_expression
        (instantiate_instantiation I J) e
    = rename (shape_assoc _ _ _)
        (instantiate_expression I
          (instantiate_expression J
            (Expression.fmap (fmap1 include_symbol _) e))).
  Proof.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ].
    - (* [e] is a variable *)
      cbn. apply inverse, ap.
      eapply concat. { refine (coproduct_comp_inj2 _). }
      refine (coproduct_comp_inj2 _).
    - (* [e] is a symbol of [Σ] *)
      simpl Expression.fmap.
      simpl instantiate_expression.
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
      simpl instantiate_expression.
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

End Composition.