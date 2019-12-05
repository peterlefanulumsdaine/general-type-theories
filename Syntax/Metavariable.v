Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Arity.
Require Import Syntax.Signature.
Require Import Syntax.Expression.
Require Import Syntax.Substitution.

Section MetavariableExtension.

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

  (** Functoriality of metavariable extensions w.r.t. signature maps *)
  
  Context `{Funext}.

  (* Metavariable extension is bifunctorial in both arguments (the signature and the arity).

  We give the general bifunctoriality action as [Metavariable.fmap], and the special cases in each argument individually as [fmap1], [fmap2]. *)
  Local Definition fmap
      {Σ Σ'  : signature σ} (f : Signature.map Σ Σ')
      {a a' : arity σ} (g : Family.map a a')
    : Signature.map (extend Σ a) (extend Σ' a').
  Proof.
    apply Family.sum_fmap.
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
 
End MetavariableExtension.

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

(* Access functions for supplying arguments to arities specified as finite extensions of the empty shape. *)
Local Definition empty_args {ϵ : σ} (H_ϵ : is_empty ϵ) {γ}
  : arguments Σ (Arity.simple ϵ) γ
  := empty_rect _ H_ϵ _.

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

Notation " '[M/' A /] "
  := (raw_symbol (include_metavariable A) (empty_args shape_is_empty)) : syntax_scope.

Notation " '[M/' A ; x , .. , z /] "
  := (raw_symbol (include_metavariable A)
       (extend_args .. (extend_args (empty_args shape_is_empty) x) .. z))
    : raw_syntax_scope.

Open Scope syntax_scope.


Section Instantiations.

  Context {σ : shape_system}.

  (* To use rules, one *instantiates* their metavariables, as raw syntax of the
     ambient signature, over some context. *)
  Local Definition instantiation (a : @arity σ) (Σ : signature σ) (γ : σ)
    : Type
  := forall i : a,
         raw_expression Σ (argument_class i) (shape_sum γ (argument_shape i)).

  (* TODO: check naming conventions *)
  Definition rename_instantiation {a} {Σ}
    {γ γ' : σ} (f : γ -> γ')
    (I : instantiation a Σ γ)
    : instantiation a Σ γ'.
  Proof.
    intros i. refine (rename _ (I i)).
    exact (Coproduct.fmap shape_is_sum shape_is_sum f idmap).
  Defined.

  (* TODO: check naming conventions *)
  Definition substitute_instantiation {a} {Σ}
    {γ γ' : σ} (f : raw_context_map Σ γ' γ)
    (I : instantiation a Σ γ)
    : instantiation a Σ γ'.
  Proof.
    intros i. refine (substitute _ (I i)).
    exact (Substitution.extend _ _ (argument_shape i) f).
  Defined.

  Definition instantiation_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {γ} (I : instantiation a Σ γ)
    : instantiation a Σ' γ
  := fun i => Expression.fmap f (I i).

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
    apply shape_assoc_rtol.
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

  Arguments instantiate_expression {_ _ _ _} _ [_] _ : simpl nomatch.

  Definition instantiate_raw_context_map {Σ : signature σ}
      {a : arity σ} {γ : σ} (I : instantiation a Σ γ)
      {δ δ' : σ} (f : raw_context_map (extend Σ a) δ' δ)
    : raw_context_map Σ (shape_sum γ δ') (shape_sum γ δ)
  := (coproduct_rect shape_is_sum _
        (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
        (fun i => instantiate_expression I (f i))).

  (** Interaction of metavariable-instantiation with renaming, substitution. *)

  Context `{Funext}.

  Lemma instantiate_rename {Σ : signature σ}
      {cl} {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
      {δ' : σ} (f : δ -> δ')
    : instantiate_expression I (Expression.rename f e)
    = Expression.rename
        (Coproduct.fmap shape_is_sum shape_is_sum idmap f)
        (instantiate_expression I e).
  Proof.
    revert δ' f.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ]; intros δ' f.
    - (* [e] is a variable *)
      cbn. apply ap, inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply inverse, rename_rename. }
      apply (ap_2back rename), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j;
        cbn; unfold Coproduct.fmap, shape_assoc_rtol, Coproduct.assoc_rtol;
        repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2;
        apply idpath.
    - (* [e] is a metavariable from [a] *)
      simpl.
      eapply concat. 2: { apply inverse, Substitution.rename_substitute. }
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. apply ap. refine (coproduct_comp_inj1 _).
      + eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, IH_e_args. }
        eapply concat. { apply rename_rename. }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply rename_rename. }
        apply (ap_2back rename), path_forall.
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

  Lemma instantiate_substitute {Σ : signature σ}
      {cl} {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
      {δ' : σ} (f : raw_context_map _ δ' δ)
    : instantiate_expression I (substitute f e)
    = substitute
        (instantiate_raw_context_map I f)
        (instantiate_expression I e).
  Proof.
    revert δ' f.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ]; intros δ' f.
    - (* [e] is a variable *)
      simpl. apply inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply Substitution.rename_substitute. }
      apply inverse.
      eapply concat. { apply substitute_rename. }
      apply (ap_2back substitute), path_forall.
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
        eapply concat. { apply rename_rename. }
        apply (ap_2back rename), path_forall.
        refine (coproduct_rect shape_is_sum _ _ _); intros k.
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
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { refine (coproduct_comp_inj1 _). }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. refine (coproduct_comp_inj1 _).
      + eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, IH_e_args. }
        eapply concat. { apply Substitution.rename_substitute. }
        apply inverse.
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply substitute_rename. }
        apply (ap_2back substitute), path_forall.
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
          eapply concat. { apply rename_rename. }
          eapply concat. 2: { apply rename_idmap. }
          apply (ap_2back rename), path_forall.
          refine (coproduct_rect shape_is_sum _ _ _); intros k.
          -- eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
           refine (coproduct_comp_inj1 _).
          -- eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
           eapply concat. { refine (coproduct_comp_inj2 _). }
           apply ap. refine (coproduct_comp_inj1 _).
        * revert j. apply empty_rect, shape_is_empty.
  Defined.

  (* TODO: consider naming of this vs. preceding lemmas about commutation of instantiations with renaming/substitution in the expressions, currently [instantiate_rename] and [instantiate_substitute]. *)
  Lemma instantiate_rename_instantiation {Σ : signature σ}
      {cl} {a : @arity σ} {γ γ': σ}
      (f : γ -> γ')
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
    : instantiate_expression (rename_instantiation f I) e
    = rename
        (Coproduct.fmap shape_is_sum shape_is_sum f idmap) 
        (instantiate_expression I e).
  Proof.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ].
    - (* [e] is a variable *)
      simpl. apply ap, inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply inverse, rename_rename. }
      apply (ap_2back rename), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j;
        cbn; unfold Coproduct.fmap, shape_assoc_rtol, Coproduct.assoc_rtol;
        repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2;
        apply idpath.
    - (* [e] is a metavariable from [a] *)
      simpl. unfold rename_instantiation.
      eapply concat. { apply substitute_rename. }
      eapply concat. 2: { apply inverse, rename_substitute. }      
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros j;
        unfold Coproduct.fmap.
      { repeat rewrite coproduct_comp_inj1; cbn.
        apply ap, inverse. refine (coproduct_comp_inj1 _). }
      repeat rewrite coproduct_comp_inj2.
      rewrite IH_e_args.
      eapply concat. { apply rename_rename. }
      eapply concat. 2: { apply inverse, rename_rename. }
      apply (ap_2back rename), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros k;
        unfold Coproduct.fmap;
        repeat rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2;
        apply idpath.
  Qed.

  (* TODO: consider naming of this vs. preceding lemmas about commutation of instantiations with renaming/substitution in the expressions, currently [instantiate_rename] and  instantiate_substitute]. *)
  Lemma instantiate_substitute_instantiation {Σ : signature σ}
      {cl} {a : @arity σ} {γ γ': σ}
      (f : raw_context_map Σ γ' γ)
      (I : instantiation a Σ γ)
      {δ} (e : raw_expression (extend Σ a) cl δ)
    : instantiate_expression (substitute_instantiation f I) e
    = substitute
        (Substitution.extend _ _ _ f)
        (instantiate_expression I e).
  Proof.
    induction e as [ θ i | θ [S | M] e_args IH_e_args ].
    - (* [e] is a variable *)
      simpl. apply inverse. refine (coproduct_comp_inj2 _). 
    - (* [e] is a symbol of [Σ] *)
      simpl. apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply rename_substitute. }
      apply inverse.
      eapply concat. { apply substitute_rename. }
      apply (ap_2back substitute), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intro;
        cbn; unfold Substitution.extend, shape_assoc_rtol, Coproduct.assoc_rtol;
        repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2.
      + eapply concat. { apply rename_rename. }
        eapply concat. 2: { apply inverse, rename_rename. }
        apply (ap_2back rename), inverse, path_forall; intro.
        refine (coproduct_comp_inj1 _).
      + cbn. apply ap.
        rewrite coproduct_comp_inj2, coproduct_comp_inj1; apply idpath.
      + cbn. apply ap.
        repeat rewrite coproduct_comp_inj2; apply idpath.
    - (* [e] is a metavariable from [a] *)
      simpl. unfold substitute_instantiation.
      eapply concat. { apply substitute_substitute. }
      eapply concat. 2: { apply inverse, substitute_substitute. }      
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros j;
        unfold Substitution.extend.
      { repeat rewrite coproduct_comp_inj1; cbn;
        rewrite coproduct_comp_inj1; cbn.
        eapply concat. { apply substitute_rename. }
        eapply concat. 2: { apply substitute_raw_variable. }
        apply (ap_2back substitute), path_forall; intros k.
        refine (coproduct_comp_inj1 _). }
      repeat rewrite coproduct_comp_inj2; cbn; rewrite coproduct_comp_inj2.
      rewrite IH_e_args.
      eapply concat. { apply rename_substitute. }
      eapply concat. 2: { apply inverse, substitute_rename. }
      apply (ap_2back substitute), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros k;
        unfold Substitution.extend, Coproduct.fmap;
        repeat rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2.
      + eapply concat. { apply rename_rename. }
        apply (ap_2back rename), path_forall; intro.
        refine (coproduct_comp_inj1 _).
      + cbn. apply ap.
        rewrite coproduct_comp_inj2; apply idpath.
      + cbn. apply ap.
        repeat rewrite coproduct_comp_inj2; apply idpath.
  Qed.

  Lemma fmap_instantiate_expression
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a : @arity σ} {γ : σ}
      (I : instantiation a Σ γ)
      {cl} {δ} (e : raw_expression (extend Σ a) cl δ)
    : Expression.fmap f (instantiate_expression I e)
    = instantiate_expression
        (instantiation_fmap f I)
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
      eapply concat. { apply Expression.fmap_rename. }
      apply ap. apply IH_e_args.
    - simpl instantiate_expression.
      eapply concat. { apply Substitution.fmap_substitute. }
      unfold raw_context_map_fmap, instantiation_fmap.
      apply (ap_2back substitute), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        cbn. apply inverse. refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply Expression.fmap_rename. }
        eapply concat. { apply ap, IH_e_args. }
        eapply inverse. { refine (coproduct_comp_inj2 _). }
  Defined.

End Instantiations.


Section Instantiation_Composition.
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
    refine (Expression.rename _ (instantiate_expression I (J i))).
    apply shape_assoc.
  Defined.

  Lemma unit_instantiate_expression {a}
      {cl} {γ} (e : raw_expression (extend Σ a) cl γ)
    : instantiate_expression (unit_instantiation a)
        (Expression.fmap (fmap1 include_symbol _) e)
      = Expression.rename (coproduct_inj2 shape_is_sum) e.
  Proof.
    induction e as [ γ i | γ [S | M] args IH ].
    - apply idpath.
    - simpl. 
      apply ap, path_forall; intros i.
      eapply concat. { apply ap, IH. }
      eapply concat. { apply rename_rename. }
      apply (ap_2back rename), path_forall.
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
      eapply concat. { apply rename_rename. }
      eapply concat. { apply rename_rename. } 
      apply (ap_2back rename), path_forall.
      refine (coproduct_rect shape_is_sum _ _ _).
      + intros x.
        unfold Coproduct.fmap, Coproduct.empty_right;
        repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2.
        apply idpath.
      + apply (empty_rect _ shape_is_empty).
  Defined.

  Lemma instantiate_instantiate_expression 
      {γ} {a} (I : instantiation a Σ γ)
      {δ} {b} (J : instantiation b (extend Σ a) δ)
      {cl} {θ} (e : raw_expression (extend Σ b) cl θ)
    : instantiate_expression
        (instantiate_instantiation I J) e
    = Expression.rename (shape_assoc _ _ _)
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
      simpl Expression.rename.
      apply ap. apply path_forall; intros i.
      eapply concat. { apply ap, IH_e_args. }
      eapply concat. { apply rename_rename. }
      apply inverse.
      eapply concat. { apply ap, ap. apply instantiate_rename. }
      eapply concat. { apply rename_rename. }
      eapply concat. { apply rename_rename. }
      apply (ap_2back rename), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j;
        cbn; unfold Coproduct.fmap, shape_assoc_rtol, Coproduct.assoc_rtol;
        repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2;
        apply idpath.
    - (* [e] is a metavariable of [b] *)
      simpl Expression.fmap.
      simpl instantiate_expression.
      simpl Expression.rename.
      eapply concat.
      { rapply @ap_2back. 
        apply ap, path_forall; intros i.
        refine (ap (rename _) _).
        apply IH_e_args.   
      } clear IH_e_args.
      unfold instantiate_instantiation.
      eapply concat. { apply substitute_rename. }
      eapply inverse.
      eapply concat. { apply ap, instantiate_substitute. }
      eapply concat. { apply Substitution.rename_substitute. }
      apply (ap_2back substitute), path_forall.
      repeat refine (coproduct_rect shape_is_sum _ _ _); intros j.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        simpl Expression.rename. eapply concat. { refine (ap _ (coproduct_comp_inj1 _)). }
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
        eapply concat. { apply rename_rename. }
        apply inverse. 
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply rename_rename. }
        apply (ap_2back rename), path_forall; clear e_args.
        repeat refine (coproduct_rect shape_is_sum _ _ _); intros k;
          cbn; unfold shape_assoc_rtol, Coproduct.assoc_rtol, Coproduct.fmap;
          repeat progress rewrite ? coproduct_comp_inj1, ? coproduct_comp_inj2;
          apply idpath.
  Defined.

  (** A somewhat technical lemma, useful under [Judgement.eq_by_expressions]
      for instantiations of a metavariable with empty binder. *)
  Lemma instantiate_binderless_metavariable
      {γ : σ} {cl}
      (E : raw_expression Σ cl (shape_sum γ (shape_empty _)))
      {f}
    : substitute
        (coproduct_rect shape_is_sum _
                        (fun i => raw_variable (coproduct_inj1 shape_is_sum i))
                        f)
        E
      = E.
  Proof.
    eapply concat. 2: { apply rename_idmap. }
    eapply concat. 2: { apply substitute_raw_variable. }
    apply (ap_2back substitute), path_forall.
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i; refine (coproduct_comp_inj1 _).
    - apply (empty_rect _ shape_is_empty).
  Defined.

End Instantiation_Composition.
