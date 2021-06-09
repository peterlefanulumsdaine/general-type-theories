Require Import HoTT.HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.

Section Algebraic_Extensions.

Context {σ : scope_system}.

Record algebraic_extension
  {Σ : signature σ} (* ambient signature of the extension *)
  {a : arity σ} (* arity listing the _object_ premises of the extension *)
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    ae_equality_premise : arity σ
  (* family indexing the premises of the extension, and giving for each… *)
  ; ae_premise :> family (Judgement.form * σ)
    := Family.sum
         (Family.fmap (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)) a)
         (Family.fmap (fun cl_γ => (form_equality (fst cl_γ), snd cl_γ))
                      ae_equality_premise)
  (* - the judgement form of each premise, e.g. “term” or “type equality” *)
  ; ae_form : ae_premise -> Judgement.form
    := fun i => fst (ae_premise i)
  (* - the proto-context of each premise *)
  ; ae_scope : ae_premise -> σ
    := fun i => snd (ae_premise i)
  (* the ordering relation on the premises *)
  ; ae_lt : well_founded_order ae_premise
  (* for each premise, the arity specifying what metavariables are available
  in the syntax for this premise; i.e., the type/term arguments already
  introduced by earlier premises *)
  ; ae_metavariables_of_premise : ae_premise -> arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  ; ae_signature_of_premise : ae_premise -> signature _
    := fun i => Metavariable.extend Σ (ae_metavariables_of_premise i)
  (* syntactic part of context of premise *)
  (* NOTE: should never be used directly, always through [ae_raw_context] *)
  ; ae_raw_context_type
    : forall (i : ae_premise) (v : ae_scope i),
        raw_type
          (ae_signature_of_premise i)
          (ae_scope i)
  (* raw context of each premise *)
  ; ae_raw_context
    : forall i : ae_premise,
        raw_context (ae_signature_of_premise i)
    := fun i => Build_raw_context _ (ae_raw_context_type i)
  (* hypothetical judgement boundary instance for each premise *)
  ; ae_hypothetical_boundary_expressions
    : forall i : ae_premise,
        Judgement.hypothetical_boundary_expressions
          (ae_signature_of_premise i)
          (ae_form i)
          (ae_scope i)
  }.

Global Arguments algebraic_extension _ _ : clear implicits.

Global Arguments ae_signature_of_premise {_ _ _} _.
Global Arguments ae_form {_ _ _} _.
Global Arguments ae_scope {_ _ _} _.
Global Arguments ae_lt {_ _ _}.
Global Arguments ae_metavariables_of_premise {_ _ _} _.
Global Arguments ae_raw_context_type {_ _ _} _.
Global Arguments ae_raw_context {_ _ _} _.

(** Access functions *)
Local Definition premise_boundary
    {Σ} {a} {A : algebraic_extension Σ a} (r : A)
  : Judgement.boundary (ae_signature_of_premise r).
Proof.
  exists (ae_raw_context r), (ae_form r).
  apply (ae_hypothetical_boundary_expressions).
Defined.

Local Definition eq_premise {a : arity σ}
    {A_eqp A'_eqp : arity σ} (e : A_eqp = A'_eqp)
    (f_ob : (_ -> _) := (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)))
    (f_eq : (_ -> _) := (fun cl_γ => (form_equality (fst cl_γ), snd cl_γ)))
  : Family.map (Family.fmap f_ob a + Family.fmap f_eq A_eqp)
               (Family.fmap f_ob a + Family.fmap f_eq A'_eqp).
Proof.
  destruct e. apply Family.idmap.
Defined.

Local Definition eq_metas {a : arity _}
    {A_eqp A'_eqp : arity σ} (e_eqp : A_eqp = A'_eqp)
    {A_lt : well_founded_order (a + A_eqp)}
    {A'_lt : well_founded_order (a + A'_eqp)}
    (e_lt : transport (fun K => well_founded_order (Family.sum _ K))
                      e_eqp A_lt = A'_lt)
  : forall i : (a + A_eqp),
    Family.map (Family.subfamily a (fun j => A_lt (inl j) i))
      (Family.subfamily a (fun j => A'_lt (inl j)
        (eq_premise e_eqp i))).
Proof.
  destruct e_eqp, e_lt. intros; apply Family.idmap.
Defined.

Local Definition eq `{Funext} {Σ} {a}
    {A A' : algebraic_extension Σ a}
    (e_premises : ae_equality_premise A = ae_equality_premise A')
    (e_lt : transport
              (fun K => well_founded_order (_ + Family.fmap _ K))
              e_premises
              (@ae_lt _ _ A)
            = @ae_lt _ _ A')
    (equiv_premise : ae_premise A -> ae_premise A' := eq_premise e_premises)
    (fe_signature : forall i : ae_premise A,
      Signature.map (ae_signature_of_premise i)
                    (ae_signature_of_premise (equiv_premise i))
      := fun i => Metavariable.fmap2 _ (eq_metas e_premises e_lt i))
    (fe_scope : forall i : ae_premise A,
        (ae_scope i <~> ae_scope (equiv_premise i))
      := fun i => equiv_path _ _ (ap _ (ap _ (Family.map_commutes _ i)^)))
    (e_raw_context : forall (i : ae_premise A) (j : _),
        Expression.fmap (fe_signature i) (ae_raw_context i j)
        = rename (equiv_inverse (fe_scope i))
                 (ae_raw_context _ (fe_scope i j)))
    (e_hypothetical_boundary
       : forall i : ae_premise A,
        rename_hypothetical_boundary_expressions (fe_scope i)
        (fmap_hypothetical_boundary_expressions (fe_signature i)
        (transport (fun jf => Judgement.hypothetical_boundary_expressions _ jf _)
                   (ap fst (Family.map_commutes (eq_premise e_premises) i)^)
        (ae_hypothetical_boundary_expressions A i)))
        = ae_hypothetical_boundary_expressions A' (equiv_premise i))
  : A = A'.
Proof.
  destruct A, A'; cbn in e_premises, e_lt.
  destruct e_premises, e_lt; simpl in *.
  refine
    (ap (Build_algebraic_extension _ _ _ _ _) _
    @ ap_1back (Build_algebraic_extension _ _ _ _) _ _).
  - clear ae_raw_context0 ae_raw_context1 e_raw_context.
    apply path_forall; intros i.
    refine (_ @ e_hypothetical_boundary i). apply inverse.
    eapply concat.
    { unfold transport.
      apply rename_hypothetical_boundary_expressions_idmap. }
    unfold fe_signature.
    eapply concat.
    { eapply (ap_3back fmap_hypothetical_boundary_expressions).
      apply Metavariable.fmap2_idmap. }
    apply fmap_hypothetical_boundary_expressions_idmap.
  - clear e_hypothetical_boundary.
    apply path_forall; intros i.
    apply path_forall; intros j.
    refine (_ @ e_raw_context i j @ _).
    + unfold fe_signature.
    eapply inverse, concat.
    { eapply (ap_3back Expression.fmap).
      apply Metavariable.fmap2_idmap. }
    apply Expression.fmap_idmap.
    + unfold equiv_premise, transport.
      apply rename_idmap.
Defined.

Local Definition fmap
    {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    {a} (A : algebraic_extension Σ a)
  : algebraic_extension Σ' a.
Proof.
  simple refine {| ae_equality_premise := ae_equality_premise A ;
                   ae_lt := @ae_lt _ _ A |}.
  - (* ae_raw_context_type *)
    intros i v.
    refine (_ (ae_raw_context_type i v)).
    apply Expression.fmap, Metavariable.fmap1, f.
  - (* ae_hypothetical_boundary *)
    intros i.
    simple refine
      (fmap_hypothetical_boundary_expressions
        _ (ae_hypothetical_boundary_expressions _ i)).
    apply Metavariable.fmap1, f.
Defined.

Context `{Funext}.

Local Definition fmap_idmap
    {Σ} {a} (A : algebraic_extension Σ a)
  : fmap (Signature.idmap _) A = A.
Proof.
  destruct A as [A_premises A_lt ? ?].
  simple refine (eq _ _ _ _).
  - apply idpath.
  - apply idpath.
  - unfold transport; simpl. intros i j.
    eapply concat.
    { eapply (ap_3back Expression.fmap).
      apply Metavariable.fmap2_idmap. }
    eapply concat. { apply Expression.fmap_idmap. }
    eapply concat.
    { eapply (ap_3back Expression.fmap).
      apply Metavariable.fmap1_idmap. }
    eapply concat. { apply Expression.fmap_idmap. }
    apply inverse, rename_idmap.
  - unfold transport; simpl. intros i.
    eapply concat.
    { apply rename_hypothetical_boundary_expressions_idmap. }
    eapply concat.
    { eapply (ap_3back fmap_hypothetical_boundary_expressions).
      apply Metavariable.fmap2_idmap. }
    eapply concat. { apply fmap_hypothetical_boundary_expressions_idmap. }
    eapply concat.
    { eapply (ap_3back fmap_hypothetical_boundary_expressions).
      apply Metavariable.fmap1_idmap. }
    apply fmap_hypothetical_boundary_expressions_idmap.
Defined.

Local Definition fmap_compose
    {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
    {a} (A : algebraic_extension Σ a)
  : fmap (Signature.compose f' f) A = fmap f' (fmap f A).
Proof.
  destruct A as [A_premises A_lt ? ?].
  simple refine (eq _ _ _ _).
  - apply idpath.
  - apply idpath.
  - unfold transport; simpl. intros i j.
    eapply concat.
    { eapply (ap_3back Expression.fmap).
      apply Metavariable.fmap2_idmap. }
    eapply concat. { apply Expression.fmap_idmap. }
    eapply concat.
    { eapply (ap_3back Expression.fmap).
      apply Metavariable.fmap1_compose. }
    eapply concat. { apply Expression.fmap_compose. }
    apply inverse, rename_idmap.
  - unfold transport; simpl. intros i.
    eapply concat.
    { apply rename_hypothetical_boundary_expressions_idmap. }
    eapply concat.
    { eapply (ap_3back fmap_hypothetical_boundary_expressions).
      apply Metavariable.fmap2_idmap. }
    eapply concat. { apply fmap_hypothetical_boundary_expressions_idmap. }
    eapply concat.
    { eapply (ap_3back fmap_hypothetical_boundary_expressions).
      apply Metavariable.fmap1_compose. }
    apply fmap_hypothetical_boundary_expressions_compose.
Defined.

Local Definition fmap_fmap
    {Σ Σ' Σ''} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
    {a} (A : algebraic_extension Σ a)
  : fmap f' (fmap f A) = fmap (Signature.compose f' f) A.
Proof.
  apply inverse, fmap_compose.
Defined.

Local Lemma premise_boundary_fmap
    {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    {a} {A : algebraic_extension Σ a} (p : A)
  : @premise_boundary _ _ (fmap f A) p
  = Judgement.fmap_boundary
      (Metavariable.fmap1 f (ae_metavariables_of_premise p))
      (premise_boundary p).
Proof.
  apply idpath.
Defined.

End Algebraic_Extensions.

(** In setting up a category of algebraic extensions, we will have both:

-  _simple_ maps of algebraic extensions, which are roughly just like family maps between their flattenings, and so interpret each symbol/premise of the source elg. ext. by a corresponding symbol/premise of the target alg. ext.;

- _(general) maps_, i.e. more general Kleisli-like maps (not given yet), which will be like maps of type theories between their flattenings, and so may interpret each symbol/premise of the source by a suitable _derivable expression_ of the target.  *)
Section Simple_Maps.

  Context {σ : scope_system}.

  Record simple_map_aux
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
    : Type
  :=
    { arity_map_of_simple_map : Family.map a a'
    ; equality_premise_map_of_simple_map
        : Family.map (ae_equality_premise A) (ae_equality_premise A')
    ; premise_map_of_simple_map
        :> Family.map A A'
        := Family.sum_fmap
             (Family.map_fmap _ arity_map_of_simple_map)
             (Family.map_fmap _ equality_premise_map_of_simple_map)
    ; well_order_map_of_simple_map
      : forall p p' : A, (ae_lt p p'
      <~> ae_lt (premise_map_of_simple_map p) (premise_map_of_simple_map p'))
  }.

  Arguments simple_map_aux {_ _ _} _ _.

  Local Definition simple_map_form_commutes
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map_aux A A')
      (p : A)
    : ae_form p = ae_form (f p).
  Proof.
    apply (ap fst), inverse, Family.map_commutes.
  Defined.

  Local Definition simple_map_scope_commutes
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map_aux A A')
      (p : A)
    : ae_scope p = ae_scope (f p).
  Proof.
    apply (ap snd), inverse, Family.map_commutes.
  Defined.

  Local Definition simple_map_premise_scope
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map_aux A A')
      {p : A}
    : ae_scope p <~> ae_scope (f p).
  Proof.
    refine (equiv_transport _ _ _ _).
    apply simple_map_scope_commutes.
  Defined.

  Local Definition simple_map_metavariables_of_premise
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map_aux A A')
      {p : A}
    : Family.map (ae_metavariables_of_premise p)
                 (ae_metavariables_of_premise (f p)).
  Proof.
    (* NOTE: could be abstracted using functoriality of “subfamily”? *)
    apply Family.Build_map'.
    intros [i lt_i_p].
    simple refine ((arity_map_of_simple_map f i;_);_).
    { apply (well_order_map_of_simple_map f (inl i) p), lt_i_p. }
    cbn. apply Family.map_commutes.
  Defined.

  Local Definition simple_map_signature_of_premise
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map_aux A A')
      {p : A}
    : Signature.map (ae_signature_of_premise p)
                    (ae_signature_of_premise (f p)).
  Proof.
    apply Metavariable.fmap2, simple_map_metavariables_of_premise.
  Defined.

  (** See note at beginning of section for explanation of this definition. *)
  (* Perhaps we will need [simple_map_over] involving signature maps, at some
  point. For now we just give [simple_map].
   (Or we could break out the dependency over arity maps?  But that seems unlikely to be needed.) *)
  Record simple_map
      {Σ : signature σ} {a a'}
      (A : algebraic_extension Σ a) (A' : algebraic_extension Σ a')
    : Type
  :=
  { simple_map_aux_part :> simple_map_aux A A'
  ; simple_map_context_commutes
    : forall (p : A) (i : _),
      ae_raw_context_type
       (simple_map_aux_part p) (simple_map_premise_scope _ i)
      = rename (simple_map_premise_scope _)
       (Expression.fmap (simple_map_signature_of_premise _)
         (ae_raw_context_type p i))
  ; simple_map_hypothetical_boundary_commutes
    : forall (p : A),
      ae_hypothetical_boundary_expressions A' (simple_map_aux_part p)
      = transport (fun jf => Judgement.hypothetical_boundary_expressions _ jf _)
                  (simple_map_form_commutes _ _)
       (rename_hypothetical_boundary_expressions (simple_map_premise_scope _)
       (fmap_hypothetical_boundary_expressions
           (simple_map_signature_of_premise _)
         (ae_hypothetical_boundary_expressions A p)))
  }.

End Simple_Maps.

Section Judgement_of_Premise.
(** In flattening an algebraic extension (or rule), and in other settings (e.g. type-checking the premises), we often want to extract premises as judgements.

   We need to do this into several different signatures, so in this construction, we isolate exactly what is required: a map from the signature of this premise, plus (in case the premise is an object premise) a symbol to use as the head of the judgement, i.e. the metavariable introduced by the premise. *)

  Context {σ : scope_system}.

  (* TODO: consider whether the flattening of the conclusion of rules can also be unified with this. *)
  Local Definition judgement_of_premise {Σ : signature σ}
      {a} {A : algebraic_extension Σ a} (i : A)
      {Σ'} (f : Signature.map (ae_signature_of_premise i) Σ')
      (Sr : Judgement.is_object (ae_form i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_scope i))
             * (symbol_class S = class_of (ae_form i))})
   : judgement Σ'.
  Proof.
    exists (Context.fmap f (ae_raw_context i)).
    exists (ae_form i).
    apply hypothetical_judgement_expressions_from_boundary_and_head.
    - refine (Judgement.fmap_hypothetical_boundary_expressions f _).
      apply ae_hypothetical_boundary_expressions.
    - intro H_obj.
      destruct i as [ i_obj | i_eq ]; simpl in *.
      + (* case: i an object rule *)
        simple refine (raw_symbol' _ _ _).
        * refine (Sr _).1. constructor.
        * refine (snd (Sr _).2).
        * set (e := (fst (Sr tt).2)^). destruct e.
           intro v. apply raw_variable.
           exact (coproduct_inj1 scope_is_sum v).
      + (* case: i an equality rule *)
        destruct H_obj. (* ruled out by assumption *)
  Defined.

  (* TODO: reorganise and reconsider the functoriality lemmas for [judgement_of_premise] *)

  Local Definition judgement_of_premise_fmap1 `{Funext}
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {a} {A : algebraic_extension Σ a} {i : A}
      {Σ''} {f' : Signature.map (ae_signature_of_premise i) Σ''}
      {f'' : Signature.map (@ae_signature_of_premise _ _ _ (fmap f A) i) Σ''}
      (e_f : f' = Signature.compose f'' (Metavariable.fmap1 f _))
      {Sr : Judgement.is_object (ae_form i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (ae_scope i))
             * (symbol_class S = class_of (ae_form i))}}
      {Sr' : Judgement.is_object (@ae_form _ _ _ (fmap f A) i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (@ae_scope _ _ _ (fmap f A) i))
             * (symbol_class S
                 = class_of (@ae_form _ _ _ (fmap f A) i))}}
      (e_Sr : Sr = Sr')
   : judgement_of_premise i f' Sr
     = @judgement_of_premise _ _ (fmap f A) i _ f'' Sr'.
  Proof.
    destruct e_f^, e_Sr. clear e_f.
    refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _
           @ ap (Build_judgement _) _).
    - (* context part *)
      apply path_forall; intros x.
      apply Expression.fmap_compose.
    - (* hypothetical part *)
      apply ap.
      apply ap2.
      + apply fmap_hypothetical_boundary_expressions_compose.
      + apply path_forall; intros i_is_ob.
        destruct i as [i_ob | i_eq]; apply idpath.
  Defined.

  Definition fmap_judgement_of_premise `{Funext}
      {Σ} {a} {A : algebraic_extension Σ a} {i : A}
      {Σ' Σ''} (f' : Signature.map Σ' Σ'')
      (f : Signature.map (ae_signature_of_premise i) Σ')
      (Sr : Judgement.is_object (ae_form i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_scope i))
             * (symbol_class S = class_of (ae_form i))})
      (Sr' := (fun i_ob =>
           (f' (Sr i_ob).1;
              (ap snd (Family.map_commutes _ _) @ fst (Sr i_ob).2
              , ap fst (Family.map_commutes _ _) @ snd (Sr i_ob).2)))
         : Judgement.is_object (ae_form i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (ae_scope i))
             * (symbol_class S = class_of (ae_form i))})
   : Judgement.fmap f' (judgement_of_premise i f Sr)
     = @judgement_of_premise _ _ A i _ (Signature.compose f' f) Sr'.
  Proof.
    refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _
           @ ap (Build_judgement _) _).
    - (* context part *)
      apply path_forall; intros x.
      apply inverse, Expression.fmap_compose.
    - (* hypothetical part *)
      apply (ap (Build_hypothetical_judgement _)).
      eapply concat.
      { apply fmap_hypothetical_judgement_expressions_from_boundary_and_head. }
      apply ap2.
      + apply inverse, fmap_hypothetical_boundary_expressions_compose.
      + apply path_forall; intros i_is_ob.
        destruct i as [i_ob | i_eq]; destruct i_is_ob.
        unfold Sr', raw_symbol'.
        eapply concat. { apply Expression.fmap_transport. }
        eapply concat. 2: { refine (transport_pp _ _ _ _)^. }
        apply ap. cbn. apply ap, ap.
        set (Srtt := Sr tt) in *. clearbody Srtt; clear Sr Sr'.
        destruct Srtt as [S [e_aS e_cS]].
        unfold symbol_arity, symbol_class in *. cbn in *.
        set (ΣS := Σ' S) in *.
        set (ΣfS := Σ'' (f' S)) in *.
        change (Σ'' (f'.(proj1_sig) _)) with ΣfS in *.
        change (Family.map_over_commutes f') with (Family.map_commutes f') in *.
        set (e_S := Family.map_commutes f' _ : ΣfS = ΣS).
        clearbody e_S ΣfS ΣS; destruct e_S.
        destruct ΣfS as [cS aS] in *; cbn in *.
        revert e_cS; apply inverse_sufficient;
          intro e; destruct e.
        revert e_aS; apply inverse_sufficient;
          intro e; destruct e.
        apply idpath.
  Defined.

  (* TODO: rename [simple_map_signature_of_premise]
   to [fmap_signature_of_premise_simple_map], etc. *)
  Definition fmap_judgement_of_premise_simple_map `{Funext}
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (g : simple_map A A') (i : A)
      {Σ'}
      {f : Signature.map (ae_signature_of_premise i) Σ'}
      {f' : Signature.map (ae_signature_of_premise (g i)) Σ'}
      (e_f : f = Signature.compose f'
                    (simple_map_signature_of_premise g))
      {Sr : Judgement.is_object (ae_form i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_scope i))
             * (symbol_class S = class_of (ae_form i))}}
      {Sr' : Judgement.is_object (ae_form  (g i))
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_scope (g i)))
             * (symbol_class S = class_of (ae_form (g i)))}}
      (e_Sr : forall i_is_ob,
         let Sr_i := Sr i_is_ob
      in let Sr_gi := Sr' (transport _ (simple_map_form_commutes _ _) i_is_ob)
      in { e_S : Sr_i.1 = Sr_gi.1
         & (fst Sr_i.2 = (ap _ e_S) @ (fst Sr_gi.2)
                                   @ ap _ (simple_map_scope_commutes _ _)^)
         * (snd Sr_i.2 =  (ap _ e_S) @ (snd Sr_gi.2)
                                   @ ap _ (simple_map_form_commutes _ _)^)})
    : judgement_of_premise i f Sr
    = judgement_of_premise (g i) f' Sr'.
  Proof.
    destruct e_f^.
    assert (e : Sr = fun i_is_ob =>
         let Sr_i := Sr i_is_ob
      in let Sr_gi := Sr' (transport _ (simple_map_form_commutes _ _) i_is_ob)
      in (Sr_gi.1 ; ( (fst Sr_gi.2) @ ap _ (simple_map_scope_commutes _ _)^
                    , (snd Sr_gi.2) @ ap _ (simple_map_form_commutes _ _)^))).
    { apply path_forall; intros i_is_ob.
      admit.
      (* previously this worked, but gets odd errors with recent Coq versions:
      specialize e_Sr with i_is_ob.
      set (Sr_i := Sr i_is_ob) in *. clearbody Sr_i; clear Sr.
      destruct Sr_i as [S e_aS_cS]; cbn in e_Sr.
      destruct e_Sr as [e_S [e_e_aS e_e_cS]].
      revert e_S e_e_aS e_e_cS. refine (inverse_sufficient _ _).
      intros e_S e_e_aS e_e_cS.
      destruct e_S; cbn in *.
      apply ap, path_prod; cbn.
      - eapply concat. { apply e_e_aS. }
        eapply concat. { apply concat_pp_p. }
        apply concat_1p.
      - eapply concat. { apply e_e_cS. }
        eapply concat. { apply concat_pp_p. }
        apply concat_1p.
        *)
    }
    (* why doesn’t [destruct e^] work here? *)
    apply inverse in e. clear e_Sr. revert Sr e.
    refine (paths_rect _ _ _ _).
    (* TODO: this is terrible. We really need some kind of “master lemma” about [judgement_of_premise] giving the master conditions under which two instances are equal; and ideally perhaps also some factoring of [judgement_of_premise] to enable proving that. *)
  Admitted. (* [fmap_judgement_of_premise_simple_map]: nasty and difficult (sticking point is equality of judgements), but hopefully self-contained *)

End Judgement_of_Premise.


Section Flattening.

  Context {σ : scope_system}.


  Local Definition flatten {Σ : signature σ} {a}
    (A : algebraic_extension Σ a)
  : family (judgement (Metavariable.extend Σ a)).
  (* This construction involves essentially two aspects:

     - translate the syntax of each expression in the rule from its “local”
       signatures to the overall signature;

     - reconstruct the head terms of the object premises *)
  Proof.
    exists (ae_premise A).
    intros i.
    apply (judgement_of_premise i).
    + apply Metavariable.fmap2.
      apply Family.subfamily_inclusion.
    + intros H_i_obj.
      destruct i as [ i | i ]; simpl in i.
      * (* case: i an object premise *)
        simple refine (_;_).
        -- apply include_metavariable. exact i.
        -- split; apply idpath.
      * (* case: i an equality premise *)
        destruct H_i_obj. (* ruled out by assumption *)
  Defined.

  (** Note: this map should additionally be an isomorphism *)
  Local Lemma flatten_fmap `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : Family.map_over (Judgement.fmap (Metavariable.fmap1 f a))
        (flatten A) (flatten (fmap f A)).
  Proof.
    exists idmap.
    intros i.
    eapply concat. 2: { apply inverse, fmap_judgement_of_premise. }
    apply inverse, judgement_of_premise_fmap1.
    - eapply concat. { apply inverse, Metavariable.fmap_compose. }
      eapply concat. 2: { apply Metavariable.fmap_compose. }
      eapply concat. { apply ap, Family.id_left. }
      eapply concat.
      { eapply (ap_3back Metavariable.fmap), Family.id_right. }
      apply inverse.
      eapply concat. { apply ap, Family.id_right. }
      eapply (ap_3back Metavariable.fmap), Family.id_left.
    - apply path_forall. intros i_is_ob.
      destruct i as [i_ob | i_eq].
      + apply idpath.
      + destruct i_is_ob.
  Defined.

  Definition flatten_fmap_simple `{Funext}
      {Σ : signature σ} {a a'}
      {A : algebraic_extension Σ a} {A' : algebraic_extension Σ a'}
      (f : simple_map A A')
    : Family.map_over
        (Judgement.fmap
           (Metavariable.fmap2 _ (arity_map_of_simple_map f)))
        (flatten A) (flatten A').
    Proof.
      exists f.
      intros i.
      apply inverse.
      eapply concat. { apply fmap_judgement_of_premise. }
      apply fmap_judgement_of_premise_simple_map.
      - eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { apply Metavariable.fmap_compose. }
        (* TODO: abstract the following as naturality lemma for
           subfamily inclusion w.r.t. functoriality of subfamilies
        (and make [arity_map_of_simple_map] use that functoriality) *)
        apply ap, Family.map_eq'. intros [j lt_j_i].
        exists (idpath _). cbn.
        eapply concat. { apply concat_p1. }
        apply inverse. eapply concat. { apply concat_1p. }
        eapply concat. { apply concat_1p. }
        apply ap_idmap.
      - intros i_is_ob. destruct i as [ i | i ]; destruct i_is_ob.
        cbn.
        unfold simple_map_form_commutes, simple_map_scope_commutes,
          ae_form, ae_scope.
        set (e := Family.map_commutes f (inl i)).
        set (Ai := ae_premise A (inl i)) in *.
        set (Ai' := ae_premise A' (f (inl i))) in *.
        clearbody e Ai Ai'.
        destruct e.
        exists (idpath _).
        cbn. set (fi := Family.map_commutes (arity_map_of_simple_map f) i).
        set (ai := a i) in *. destruct fi.
        split; apply idpath.
    Defined.

End Flattening.


Section Initial_Segment.
  (** Each premise of an algebraic extension will be typechecked in the _initial segment_ preceding it: that is, the algebraic extension giving by the earlier premises.

  (If the ordering relation is multi-valued, then  *)

  Context {σ : scope_system}.

  (** Next few definitions are auxiliary for [initial_segment] below *)
  Local Definition initial_segment_premise_aux
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : family (form * σ.(scope_carrier))
  := Family.fmap (fun cl_γ : syntactic_class * σ.(scope_carrier) =>
                    (form_object cl_γ.(fst), cl_γ.(snd)))
                 (ae_metavariables_of_premise r)
   + Family.fmap (fun cl_γ : syntactic_class * σ.(scope_carrier) =>
                    (form_equality cl_γ.(fst), cl_γ.(snd)))
       (Family.subfamily (ae_equality_premise A)
                         (fun j => ae_lt (inr j) r)).

  Local Definition initial_segment_include_premise_aux
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : Family.map
        (initial_segment_premise_aux A r)
        (ae_premise A).
  Proof.
    apply Family.Build_map'.
    intros [ [i_ob lt_i_r] | [i_eq lt_i_r] ].
    + exists (inl i_ob); apply idpath.
    + exists (inr i_eq); apply idpath.
  Defined.

  Arguments initial_segment_include_premise_aux : simpl never.

  Local Definition initial_segment_lt_aux
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : well_founded_order (initial_segment_premise_aux A r)
  := WellFounded.pullback
       (initial_segment_include_premise_aux A r)
       (ae_lt).

  Local Definition initial_segment_include_premise_lt_aux
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : ae_lt (initial_segment_include_premise_aux _ _ i) r.
  Proof.
    destruct i as [ [ i_ob e ] | [i_eq e] ]; apply e.
  Defined.

  Definition initial_segment_compare_premise_metas
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : Family.map
        (ae_metavariables_of_premise
           (initial_segment_include_premise_aux _ _ i))
        (Family.subfamily (ae_metavariables_of_premise r) (fun j =>
           initial_segment_lt_aux _ _ (inl j) i)).
  Proof.
    apply Family.Build_map'.
    intros [ j j_lt_i ].
    simple refine (((j;_);_);_).
    - cbn. eapply WellFounded.transitive.
      + exact j_lt_i.
      + apply initial_segment_include_premise_lt_aux.
    - destruct i as [ ? | ? ]; exact j_lt_i.
    - apply idpath.
  Defined.

  (** Auxiliary definition for [initial_segment] below *)
  Definition initial_segment_compare_signature
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : Signature.map
        (ae_signature_of_premise
          (initial_segment_include_premise_aux _ _ i))
        (Metavariable.extend Σ
          (Family.subfamily (ae_metavariables_of_premise r) (fun j =>
            initial_segment_lt_aux _ _ (inl j) i))).
  Proof.
    apply Metavariable.fmap2, initial_segment_compare_premise_metas.
  Defined.

  (** The “initial segment” of an algebraic extension preceding some given premise *)
  Local Definition initial_segment
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : algebraic_extension Σ (ae_metavariables_of_premise r).
  Proof.
    simple refine (Build_algebraic_extension _ _ _ _ _ _).
    - (* ae_equality_premise *)
      exact (Family.subfamily (ae_equality_premise A)
                              (fun j => ae_lt (inr j) r)).
    - (* ae_lt *)
      apply initial_segment_lt_aux.
    - (* ae_raw_context_type *)
      intros i x.
      refine (Expression.fmap _ _).
      + apply initial_segment_compare_signature.
      + set (i_orig
          := initial_segment_include_premise_aux A r i).
        destruct i as [ ? | ? ]; refine (ae_raw_context_type i_orig x).
    - (* ae_hypothetical_boundary *)
      intros i x.
      refine (Expression.fmap _ _).
      + apply initial_segment_compare_signature.
      + set (i_orig
          := initial_segment_include_premise_aux A r i).
        destruct i as [ ? | ? ];
          refine (ae_hypothetical_boundary_expressions A i_orig x).
  Defined.

  (* Perhaps better as (simple) map of alg exts. *)
  Local Lemma initial_segment_fmap_eq `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a} (p : A)
    : initial_segment (fmap f A) p
    = fmap f (initial_segment A p).
  Proof.
    simple refine (eq _ _ _ _); try apply idpath.
    - (* rule contexts *)
      intros i j. simpl in j.
      eapply concat. { apply Expression.fmap_fmap. }
      eapply concat. { apply inverse, rename_idmap. }
      apply ap.
      + (* there’s got to be a better way here
           than this 20 lines of duplicated code… *)
        destruct i as [ i_ob | i_eq ].
        * eapply concat. { apply Expression.fmap_fmap. }
          eapply concat.
          { apply ap. unfold initial_segment_include_premise_aux; cbn.
            apply idpath. }
          apply inverse.
          eapply concat. { apply Expression.fmap_fmap. }
          eapply concat.
          { apply ap. unfold initial_segment_include_premise_aux; cbn.
            apply idpath. }
          apply (ap_3back Expression.fmap).
          eapply concat.
          2: { apply ap. unfold initial_segment_include_premise_aux; cbn.
               apply idpath. }
          unfold initial_segment_compare_signature.
          eapply concat. { apply inverse, Metavariable.fmap_compose. }
          eapply concat. 2: { eapply ap10, ap, Metavariable.fmap_compose. }
          eapply concat. 2: { apply Metavariable.fmap_compose. }
          apply (ap2 (fun f g => Metavariable.fmap f g)).
          -- eapply concat. { apply Family.id_right. }
             apply inverse.
             eapply concat. 2: { apply Family.id_left. }
             apply ap10, ap. apply Family.id_right.
          -- apply idpath.
        * eapply concat. { apply Expression.fmap_fmap. }
          eapply concat.
          { apply ap. unfold initial_segment_include_premise_aux; cbn.
            apply idpath. }
          apply inverse.
          eapply concat. { apply Expression.fmap_fmap. }
          eapply concat.
          { apply ap. unfold initial_segment_include_premise_aux; cbn.
            apply idpath. }
          apply (ap_3back Expression.fmap).
          eapply concat.
          2: { apply ap. unfold initial_segment_include_premise_aux; cbn.
               apply idpath. }
          unfold initial_segment_compare_signature.
          eapply concat. { apply inverse, Metavariable.fmap_compose. }
          eapply concat. 2: { eapply ap10, ap, Metavariable.fmap_compose. }
          eapply concat. 2: { apply Metavariable.fmap_compose. }
          apply (ap2 (fun f g => Metavariable.fmap f g)).
          -- eapply concat. { apply Family.id_right. }
             apply inverse.
             eapply concat. 2: { apply Family.id_left. }
             apply ap10, ap. apply Family.id_right.
          -- apply idpath.
    - (* rule boundaries *)
      intros i.
      eapply concat.
      2: { eapply rename_hypothetical_boundary_expressions_idmap. }
      apply ap.
      simpl ap. apply path_forall; intros x.
      destruct i as [ i_ob | i_eq ].
      + simpl. unfold fmap_hypothetical_boundary.
        eapply concat.
        { eapply (ap_3back Expression.fmap).
          apply Metavariable.fmap_idmap. }
        eapply concat. { apply Expression.fmap_idmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { eapply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_right. }
          apply inverse.
          apply Family.id_left.
        * apply idpath.
      + simpl. unfold fmap_hypothetical_boundary.
        eapply concat.
        { eapply (ap_3back Expression.fmap).
          apply Metavariable.fmap_idmap. }
        eapply concat. { apply Expression.fmap_idmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { eapply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_right. }
          apply inverse.
          apply Family.id_left.
        * apply idpath.
  Time Defined.

  (* TODO: try to abstract some bits of this out, to:
   - improve timing of [Defined];
   - improve clarity of proof;
   - remove code duplication. *)
  Local Lemma initial_segment_fmap `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a} (p : A)
    : simple_map
        (initial_segment (fmap f A) p)
        (fmap f (initial_segment A p)).
  Proof.
    simple refine (Build_simple_map _ _ _ _ _ _ _ _).
    1: simple refine (Build_simple_map_aux _ _ _ _ _ _ _ _).
    - (* object premises *) apply Family.idmap.
    - (* equality premises *) apply Family.idmap.
    - (* well-ordering *) intros i j.
      cbn. recursive_destruct i; recursive_destruct j; apply equiv_idmap.
    - (* premise contexts *)
      intros i j. cbn in j.
      eapply concat. { apply Expression.fmap_fmap. }
      eapply concat. { apply inverse, rename_idmap. }
      destruct i as [ i_ob | i_eq ];
      apply (ap2 (fun f e => rename f e)); try apply idpath.
      + simpl. apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        unfold simple_map_signature_of_premise.
        unfold initial_segment_compare_signature.
        eapply concat. { eapply ap10, ap, inverse, Metavariable.fmap_compose. }
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { apply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_left. }
          apply inverse, Family.id_right.
        * apply idpath. (* I don’t know how but I won’t question this *)
      + simpl. apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        unfold simple_map_signature_of_premise.
        unfold initial_segment_compare_signature.
        eapply concat. { eapply ap10, ap, inverse, Metavariable.fmap_compose. }
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { apply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_left. }
          apply inverse, Family.id_right.
        * apply idpath.
    - (* premise hypothetical boundaries *)
      intros i.
      destruct i as [ i_ob | i_eq ]; simpl.
      + eapply concat.
        2: { apply inverse, rename_hypothetical_boundary_expressions_idmap. }
        apply inverse.
        simpl ap. apply path_forall; intros x.
        simpl. unfold fmap_hypothetical_boundary.
        eapply concat.
        { eapply (ap_3back Expression.fmap).
          apply Metavariable.fmap_idmap. }
        eapply concat. { apply Expression.fmap_idmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { eapply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_right. }
          apply inverse.
          apply Family.id_left.
        * apply idpath.
      + eapply concat.
        2: { apply inverse, rename_hypothetical_boundary_expressions_idmap. }
        apply inverse.
        simpl ap. apply path_forall; intros x.
        simpl. unfold fmap_hypothetical_boundary.
        eapply concat.
        { eapply (ap_3back Expression.fmap).
          apply Metavariable.fmap_idmap. }
        eapply concat. { apply Expression.fmap_idmap. }
        eapply concat. { apply Expression.fmap_fmap. }
        apply inverse.
        eapply concat. { apply Expression.fmap_fmap. }
        apply (ap_3back Expression.fmap).
        eapply concat. { apply inverse, Metavariable.fmap_compose. }
        eapply concat. 2: { eapply Metavariable.fmap_compose. }
        apply (ap2 (fun f g => Metavariable.fmap f g)).
        * eapply concat. { apply Family.id_right. }
          apply inverse.
          apply Family.id_left.
        * apply idpath.
  Time Defined.

  Local Lemma flatten_initial_segment_fmap `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a} (p : A)
    : Family.map
        (flatten (initial_segment (fmap f A) p))
        (flatten (fmap f (initial_segment A p))).
  Proof.
    simple refine (Family.map_transport _ (flatten_fmap_simple _)).
    2: { refine (initial_segment_fmap f p). }
    eapply concat. { apply ap, Metavariable.fmap_idmap. }
    apply path_forall; intros i. apply Judgement.fmap_idmap.
  Defined.

  Local Lemma flatten_initial_segment_fmap_applied `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a} (p : A)
      (i : initial_segment A p)
    : flatten (initial_segment (fmap f A) p) i
    = flatten (fmap f (initial_segment A p)) i.
  Proof.
    apply inverse.
    eapply concat.
    2: { exact (Family.map_commutes (flatten_initial_segment_fmap f p) i). }
    destruct i; apply idpath.
  Defined.

End Initial_Segment.
