Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import RawSyntax.SyntacticClass.
Require Import RawSyntax.Arity.
Require Import RawSyntax.Signature.

Section RawSyntax.

  Context {σ : shape_system}.

  Context {Σ : signature σ}.

  (* A raw syntactic expression of a syntactic class, relative to a shape *)
  Inductive raw_expression
    : syntactic_class -> σ -> Type
    :=
    (* a variable is a position in the context *)
    | raw_variable (γ : σ) (i : γ)
        : raw_expression class_term γ
    (* relative to a context [γ], given a symbol [S], if for each of its
       arguments we have a raw syntactic expression relative to [γ] extended by
       the argument's arity, [S args] is a raw syntactic expression over [γ] *)
    | raw_symbol (γ : σ) (S : Σ)
                 (args : forall (i : symbol_arity S),
                   raw_expression (argument_class i)
                                  (shape_sum γ (argument_shape i)))
      : raw_expression (symbol_class S) γ.

  Global Arguments raw_variable [_] _.
  Global Arguments raw_symbol [_] _ _.

  (** Convenient abbreviations, to improve readability of code. *)
  Definition raw_type := raw_expression class_type.
  Definition raw_term := raw_expression class_term.

  (* Supose [S] is a symbol whose arity is [a] and we would like to use [S]
     to form a raw expresssion. Then we have to provide arguments so that
     we can apply [S] to them. The following type describes these arguments. *)
  Definition arguments (a : arity σ) γ : Type
  := forall (i : a),
      raw_expression (argument_class i) (shape_sum γ (argument_shape i)).

  (* Useful, with [idpath] as the equality argument, when want wants to construct the
  smybol argument interactively — this is difficult with original [symb_raw] due to [class
  S] appearing in the conclusion. *)
  Definition raw_symbol'
      {γ} {cl} (S : Σ) (e : symbol_class S = cl)
      (args : arguments (symbol_arity S) γ)
    : raw_expression cl γ.
  Proof.
    refine (transport (fun cl => raw_expression cl _) e _).
    now apply raw_symbol.
  Defined.

End RawSyntax.

Global Arguments raw_expression {_} _ _ _.
Global Arguments raw_type {_} _ _.
Global Arguments raw_term {_} _ _.
Global Arguments arguments {_} _ _ _.

Section Signature_Maps.

  Context {σ : shape_system}.
  
  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {cl} {γ}
    : raw_expression Σ cl γ -> raw_expression Σ' cl γ.
  Proof.
    intros t. induction t as [ γ i | γ S ts fts].
    - exact (raw_variable i).
    - refine (transport (fun cl => raw_expression _ cl _) _ (raw_symbol (f S) _)).
      + exact (ap fst (Family.map_commutes _ _)).
      + refine (transport
          (fun a : arity σ => forall i : a,
               raw_expression Σ' (argument_class i) (shape_sum γ (argument_shape i)))
          _
          fts).
        exact ((ap snd (Family.map_commutes _ _))^).
  Defined.

  Global Arguments fmap : simpl nomatch.

  Context `{Funext}.

  Local Definition fmap_idmap {Σ} {cl} {γ} (e : raw_expression Σ cl γ)
    : fmap (Signature.idmap Σ) e = e.
  Proof.
    induction e as [ γ i | γ S e_args IH_e_args ].
    - apply idpath.
    - simpl. apply ap.
      apply path_forall; intros i.
      apply IH_e_args.
  Defined.

  Local Lemma fmap_transport 
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {cl cl'} (p : cl = cl') {γ} (e : raw_expression Σ cl γ)
    : fmap f (transport (fun cl => raw_expression _ cl _) p e)
      = transport (fun cl => raw_expression _ cl _) p (fmap f e).
  Proof.
    destruct p; apply idpath.
  Defined.

  Local Definition fmap_fmap
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {cl} {γ} (e : raw_expression Σ cl γ)
    : fmap f' (fmap f e) = fmap (Signature.compose f' f) e.
  Proof.
    induction e as [ γ i | γ S e_args IH ]; simpl.
    - apply idpath.
    - eapply concat. { apply fmap_transport. }
      simpl. eapply concat. { refine (transport_pp _ _ _ _)^. }
      eapply concat. { refine (ap (fun p => transport _ p _) _).
                       refine (ap_pp fst _ _)^. }
      eapply concat.
      2: { refine (ap (fun p => transport _ p _) _).
           apply ap, ap, inverse, ap_idmap. }
      apply ap, ap.
      (* Now that we are under the [raw_symbol], we can abstract and destruct
      the [map_commutes] equalities, and so eliminate the transports. *)
      set (ΣS := Σ S); set (ΣfS := Σ' (f S)); set (ΣffS := Σ'' (f' (f S))). 
      change (Family.map_over_commutes f') with (Family.map_commutes f').
      change (Family.map_over_commutes f) with (Family.map_commutes f).
      set (p' := Family.map_commutes f' (f S) : ΣffS = ΣfS).
      set (p := Family.map_commutes f S : ΣfS = ΣS).
      (* unfold some functions that occur within implicit subterms,
      blocking folding: *)
      unfold Family.map_over_of_map, symbol_arity in *.
      fold p p' ΣffS ΣfS ΣS. fold ΣS in e_args, IH.
      clearbody p' p ΣS ΣfS ΣffS.
      destruct p, p'; simpl.
      apply path_forall; intros i. apply IH.
  Defined.

  Local Definition fmap_compose
      {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
      {cl} {γ} (e : raw_expression Σ cl γ)
    : fmap (Signature.compose f' f) e = fmap f' (fmap f e).
  Proof.
    apply inverse, fmap_fmap.
  Defined.

End Signature_Maps.

