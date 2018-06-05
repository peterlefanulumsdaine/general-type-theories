Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.SyntaxLemmas.

Section Algebraic_Extensions.

Context {σ : shape_system} {Σ : signature σ}.

Record algebraic_extension
  {a : arity σ} (* arity listing the _object_ premises of the extension *)
:=
  {
  (* The arity [a] supplies the family of object-judgment premises. *)
  (* The family of equality-judgment premises: *)
    ae_equality_premise : arity σ
  (* family indexing the premises of the extension, and giving for each… *)
  ; ae_premise :> family (Judgement.hypothetical_form * σ)
    := Family.sum
         (Family.fmap (fun cl_γ => (form_object (fst cl_γ), snd cl_γ)) a)
         (Family.fmap (fun cl_γ => (form_equality (fst cl_γ), snd cl_γ)) ae_equality_premise)
  (* - the judgement form of each premise, e.g. “term” or “type equality” *)
  ; ae_form : ae_premise -> Judgement.hypothetical_form
    := fun i => fst (ae_premise i)
  (* - the proto-context of each premise *)
  ; ae_shape : ae_premise -> σ
    := fun i => snd (ae_premise i)
  (* the ordering relation on the premises *)
  ; ae_lt : well_founded_order ae_premise
  (* for each premise, the arity specifying what metavariables are available
  in the syntax for this premise; i.e., the type/term arguments already
  introduced by earlier premises *)
  ; ae_metas : ae_premise -> arity _
    := fun i => Family.subfamily a (fun j => ae_lt (inl j) i)
  ; ae_signature : ae_premise -> signature _
    := fun i => Metavariable.extend Σ (ae_metas i)
  (* syntactic part of context of premise *)
  (* NOTE: should never be used directly, always through [ae_raw_context] *)
  ; ae_raw_context_type
    : forall (i : ae_premise) (v : ae_shape i),
        raw_type
          (ae_signature i)
          (ae_shape i)
  (* raw context of each premise *)
  ; ae_raw_context
    : forall i : ae_premise,
        raw_context (ae_signature i)
    := fun i => Build_raw_context _ (ae_raw_context_type i)
  (* hypothetical judgement boundary instance for each premise *)
  ; ae_hypothetical_boundary
    : forall i : ae_premise,
        Judgement.hypothetical_boundary
          (ae_signature i)
          (ae_form i)
          (ae_shape i)
  }.

Arguments algebraic_extension _ : clear implicits.

(* TODO: make the record argument implicit in most fields. *)

Local Definition premise_boundary
    {a} {A : algebraic_extension a} (r : A)
  : Judgement.boundary (ae_signature _ r)
                       (form_hypothetical (ae_form _ r)).
Proof.
  exists (ae_raw_context _ r).
  apply (ae_hypothetical_boundary).
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

Local Definition eq `{Funext} {a}
    {A A' : algebraic_extension a}
    (e_premises : ae_equality_premise A = ae_equality_premise A')
    (e_lt : transport
              (fun K => well_founded_order (_ + Family.fmap _ K))
              e_premises
              (ae_lt A)
            = ae_lt A')
    (equiv_premise : ae_premise A -> ae_premise A' := eq_premise e_premises)
    (fe_signature : forall i : ae_premise A,
      Signature.map (ae_signature A i) (ae_signature A' (equiv_premise i))
      := fun i => Metavariable.fmap2 _ (eq_metas e_premises e_lt i))
    (fe_shape : forall i : ae_premise A,
        (ae_shape A i <~> ae_shape A' (equiv_premise i))
      := fun i => equiv_path _ _ (ap _ (ap _ (Family.map_commutes _ i)^)))
    (e_raw_context : forall (i : ae_premise A) (j : _),
        Expression.fmap (fe_signature i) (ae_raw_context A i j)
        = rename (equiv_inverse (fe_shape i))
                 (ae_raw_context A' _ (fe_shape i j)))
    (e_hypothetical_boundary
       : forall i : ae_premise A,
        rename_hypothetical_boundary (fe_shape i)
        (fmap_hypothetical_boundary (fe_signature i)
        (transport (fun hjf => Judgement.hypothetical_boundary _ hjf _)
                   (ap fst (Family.map_commutes (eq_premise e_premises) i)^)
        (ae_hypothetical_boundary A i)))
        = ae_hypothetical_boundary A' (equiv_premise i))
  : A = A'.
Proof.
  destruct A, A'; cbn in e_premises, e_lt.
  destruct e_premises, e_lt; simpl in *.
  refine
    (ap (Build_algebraic_extension _ _ _ _) _
    @ ap (fun rc => Build_algebraic_extension _ _ _ rc _) _).
  - clear ae_raw_context0 ae_raw_context1 e_raw_context.
    apply path_forall; intros i.
    refine (_ @ e_hypothetical_boundary i). apply inverse.
    eapply concat.
    { unfold transport. apply rename_hypothetical_boundary_idmap. }
    unfold fe_signature.
    eapply concat.
    { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
      apply Metavariable.fmap2_idmap. }
    apply fmap_hypothetical_boundary_idmap.
  - clear e_hypothetical_boundary.
    apply path_forall; intros i.
    apply path_forall; intros j.  
    refine (_ @ e_raw_context i j @ _).
    + unfold fe_signature.
    eapply inverse, concat.
    { refine (ap (fun f => Expression.fmap f _) _).
      apply Metavariable.fmap2_idmap. }
    apply Expression.fmap_idmap.
    + unfold equiv_premise, transport.
      apply rename_idmap.
Defined.

End Algebraic_Extensions.

Arguments algebraic_extension {_} _ _.

Section Functoriality.

  Context {σ : shape_system}.

  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : algebraic_extension Σ' a.
  Proof.
    simple refine {| ae_equality_premise := ae_equality_premise A ;
                     ae_lt := ae_lt A |}.
    - (* ae_raw_context_type *)
      intros i v.
      refine (_ (ae_raw_context_type _ i v)).
      apply Expression.fmap, Metavariable.fmap1, f.
    - (* ae_hypothetical_boundary *)
      intros i.
      simple refine
        (fmap_hypothetical_boundary
          _ (ae_hypothetical_boundary _ i)).
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
      { refine (ap (fun f => Expression.fmap f _) _).
        apply Metavariable.fmap2_idmap. }
      eapply concat. { apply Expression.fmap_idmap. }
      eapply concat.
      { refine (ap (fun f => Expression.fmap f _) _).
        apply Metavariable.fmap1_idmap. }
      eapply concat. { apply Expression.fmap_idmap. }
      apply inverse, rename_idmap.
    - unfold transport; simpl. intros i.
      eapply concat.
      { apply rename_hypothetical_boundary_idmap. }
      eapply concat.
      { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
        apply Metavariable.fmap2_idmap. }
      eapply concat. { apply fmap_hypothetical_boundary_idmap. }
      eapply concat.
      { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
        apply Metavariable.fmap1_idmap. }
      apply fmap_hypothetical_boundary_idmap.
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
      { refine (ap (fun f => Expression.fmap f _) _).
        apply Metavariable.fmap2_idmap. }
      eapply concat. { apply Expression.fmap_idmap. }
      eapply concat.
      { refine (ap (fun f => Expression.fmap f _) _).
        apply Metavariable.fmap1_compose. }
      eapply concat. { apply Expression.fmap_compose. }
      apply inverse, rename_idmap.
    - unfold transport; simpl. intros i.
      eapply concat.
      { apply rename_hypothetical_boundary_idmap. }
      eapply concat.
      { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
        apply Metavariable.fmap2_idmap. }
      eapply concat. { apply fmap_hypothetical_boundary_idmap. }
      eapply concat.
      { refine (ap (fun f => fmap_hypothetical_boundary f _) _).
        apply Metavariable.fmap1_compose. }
      apply fmap_hypothetical_boundary_compose.
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
    : @premise_boundary _ _ _ (fmap f A) p
    = Judgement.fmap_boundary (Metavariable.fmap1 f (ae_metas A p))
                              (premise_boundary p).
  Proof.
    apply idpath.
  Defined.

End Functoriality.

Section Flattening.

  Context {σ : shape_system}.

  (* In flattening an algebraic extension (or rule), and in other settings (e.g. type-checking the premises), we often want to extract premises as judgements.

   We need to do this into several different signatures, so in this lemma, we isolate exactly what is required: a map from the signature of this premise, plus (in case the premise is an object premise) a symbol to use as the head of the judgement, i.e. the metavariable introduced by the premise. *)
  (* TODO: consider whether the flattening of the conclusion of rules can also be unified with this. *)
  Local Definition judgement_of_premise {Σ : signature σ}
      {a} {A : algebraic_extension Σ a} (i : A)
      {Σ'} (f : Signature.map (ae_signature _ i) Σ')
      (Sr : Judgement.is_object (ae_form _ i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_shape _ i))
             * (symbol_class S = Judgement.class_of (ae_form _ i))})
   : judgement_total Σ'.
  Proof.
    exists (form_hypothetical (ae_form _ i)).
    exists (Context.fmap f (ae_raw_context _ i)).
    apply Judgement.hypothetical_instance_from_boundary_and_head.
    - refine (Judgement.fmap_hypothetical_boundary f _).
      apply ae_hypothetical_boundary.
    - intro H_obj.
      destruct i as [ i_obj | i_eq ]; simpl in *.
      + (* case: i an object rule *)
        simple refine (raw_symbol' _ _ _).
        * refine (Sr _).1. constructor.
        * refine (snd (Sr _).2).
        * set (e := (fst (Sr tt).2)^). destruct e.
           intro v. apply raw_variable.
           exact (coproduct_inj1 shape_is_sum v).
      + (* case: i an equality rule *)
        destruct H_obj. (* ruled out by assumption *)
  Defined.

  Local Definition flatten {Σ : signature σ} {a}
    (A : algebraic_extension Σ a)
  : family (judgement_total (Metavariable.extend Σ a)).
  (* This construction involves essentially two aspects:

     - translate the syntax of each expression in the rule from its “local”
       signatures to the overall signature;

     - reconstruct the head terms of the object premises *)
  Proof.
    exists (ae_premise A).
    intros i.
    apply (judgement_of_premise i).
    + apply Metavariable.fmap2.
      apply Family.inclusion.
    + intros H_i_obj.
      destruct i as [ i | i ]; simpl in i.
      * (* case: i an object premise *)
        simple refine (_;_).
        -- apply include_metavariable. exact i.
        -- split; apply idpath.
      * (* case: i an equality premise *)
        destruct H_i_obj. (* ruled out by assumption *)
  Defined.

  (* TODO: upstream! *)
  Definition family_map_over_eq `{Funext}
      {X X'} {f : X -> X'}
      {K} {L} {ff gg : Family.map_over f K L}
      (e_map : forall k:K, ff k = gg k)
      (e_comm : forall k:K,
        Family.map_over_commutes ff k
        = ap L (e_map k) @ Family.map_over_commutes gg k)
    : ff = gg.
  Proof.
    destruct ff as [ff_ob ff_comm], gg as [gg_ob gg_comm].
    set (e_map' := path_forall _ _ e_map : ff_ob = gg_ob).
    assert (ee : e_map == ap10 e_map').
      { intros i; apply inverse, ap10_path_forall. }
    destruct e_map'. apply ap.
    apply path_forall; intros k.
    cbn in e_comm.
    eapply concat. { apply e_comm. }
    eapply concat. { eapply ap10, ap, ap, ee. }
    apply concat_1p.
  Defined.

  (* TODO: upstream! *)
  Definition family_map_over_eq' `{Funext}
      {X X'} {f : X -> X'}
      {K} {L} {ff gg : Family.map_over f K L}
    : (forall k:K, { e : ff k = gg k
         & Family.map_over_commutes ff k
           = ap L e @ Family.map_over_commutes gg k } )
    -> ff = gg.
  Proof.
    intros e.
    simple refine (family_map_over_eq _ _); intros k.
    - exact (e k).1.
    - exact (e k).2.
  Defined.

  (* TODO: upstream *)
  Lemma family_sum_fmap_compose_over `{Funext}
      {X X' X''} {f' : X' -> X''} {f : X -> X'}
      {K} {K'} {K''} (g' : Family.map_over f' K' K'') (g : Family.map_over f K K')
      {L} {L'} {L''} (h' : Family.map_over f' L' L'') (h : Family.map_over f L L')
    : Family.compose_over (Family.fmap_of_sum g' h') (Family.fmap_of_sum g h)
      = Family.fmap_of_sum (Family.compose_over g' g) (Family.compose_over h' h).
  Proof.
    simple refine (family_map_over_eq' _).
    intros [k | l]; exists (idpath _);
      apply inverse, concat_1p.
  Defined.

  (* TODO: upstream *)
  Lemma family_sum_fmap_compose `{Funext}
      {X}
      {K K' K'' : family X} (g' : Family.map K' K'') (g : Family.map K K')
      {L L' L'' : family X} (h' : Family.map L' L'') (h : Family.map L L')
    : Family.compose (Family.fmap_of_sum g' h') (Family.fmap_of_sum g h)
      = Family.fmap_of_sum (Family.compose g' g) (Family.compose h' h).
  Proof.
    exact (family_sum_fmap_compose_over g' g h' h).
  Defined.

  (* TODO: upstream *)
  Lemma family_map_fmap_compose `{Funext}
      {X Y} (f : X -> Y)
      {K K' K'' : family X} (g' : Family.map K' K'') (g : Family.map K K')
    : Family.compose (Family.map_fmap f g') (Family.map_fmap f g)
      = Family.map_fmap f (Family.compose g' g). 
  Proof.
    apply Family.map_eq'.
    intros k; exists (idpath _); cbn.
    apply inverse.
    eapply concat. { apply concat_1p. }
    eapply concat. { apply ap_pp. }
    apply ap.
    eapply concat. {apply ap, ap_idmap. }
    apply inverse, ap_idmap.
  Defined.

  (* TODO: upstream *)
  Lemma metavariable_fmap_compose `{Funext}
        {Σ Σ' Σ'' : signature σ} (f' : Signature.map Σ' Σ'') (f : Signature.map Σ Σ')
        {a a' a'' : arity σ} (g' : Family.map a' a'') (g : Family.map a a')
      : Signature.compose (Metavariable.fmap f' g') (Metavariable.fmap f g)
        = Metavariable.fmap (Signature.compose f' f) (Family.compose g' g).
  Proof.
    unfold Signature.compose, Metavariable.fmap.
    eapply concat. { apply family_sum_fmap_compose. }
    apply ap. apply family_map_fmap_compose.
  Defined.

  (* TODO: upstream *)
  Definition fmap_hypothetical_instance_from_boundary_and_head `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {hjf} {γ : σ} (B : Judgement.hypothetical_boundary Σ hjf γ)
      (e : Judgement.is_object hjf -> raw_expression Σ (Judgement.class_of hjf) γ)
    : fmap_hypothetical_judgement f
        (Judgement.hypothetical_instance_from_boundary_and_head _ B e)
      = Judgement.hypothetical_instance_from_boundary_and_head _
          (Judgement.fmap_hypothetical_boundary f B)
          (fun hjf_ob => Expression.fmap f (e hjf_ob)).
  Proof.
    destruct hjf as [ocl | ecl].
    - apply path_forall; intros [ ? | ]; apply idpath.
    - apply idpath.
  Defined.

  (* TODO: upstream to [auxiliary] *)
  Definition ap2 {X Y Z} (f : X -> Y -> Z)
      {x x'} (e_x : x = x') {y y'} (e_y : y = y')
    : f x y = f x' y'.
  Proof.
    exact (ap _ e_y @ ap (fun x => f x _) e_x).
  Defined.

  Local Definition judgement_of_premise_fmap1 `{Funext}
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {a} {A : algebraic_extension Σ a} {i : A}
      {Σ''} {f' : Signature.map (ae_signature A i) Σ''}
      {f'' : Signature.map (ae_signature (fmap f A) i) Σ''}
      (e_f : f' = Signature.compose f'' (Metavariable.fmap1 f _)) 
      {Sr : Judgement.is_object (ae_form A i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (ae_shape A i))
             * (symbol_class S = Judgement.class_of (ae_form A i))}}
      {Sr' : Judgement.is_object (ae_form (fmap f A) i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (ae_shape (fmap f A) i))
             * (symbol_class S = Judgement.class_of (ae_form (fmap f A) i))}}
      (e_Sr : Sr = Sr')
   : judgement_of_premise i f' Sr
     = @judgement_of_premise _ _ (fmap f A) i _ f'' Sr'.
  Proof.
    destruct e_f^, e_Sr. clear e_f.
    eapply (ap (Build_judgement_total _)).
    refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _
           @ ap (Build_judgement _) _).
    - (* context part *)
      apply path_forall; intros x.
      apply Expression.fmap_compose.
    - (* hypothetical part *)
      apply (ap2 (Judgement.hypothetical_instance_from_boundary_and_head _)).
      + apply fmap_hypothetical_boundary_compose.
      + apply path_forall; intros i_is_ob.
        destruct i as [i_ob | i_eq]; destruct i_is_ob.
        apply idpath.
  Defined.

  (* TODO: upstream *)
  Definition fmap_judgement_of_premise `{Funext}
      {Σ} {a} {A : algebraic_extension Σ a} {i : A}
      {Σ' Σ''} (f' : Signature.map Σ' Σ'')
      (f : Signature.map (ae_signature A i) Σ')
      (Sr : Judgement.is_object (ae_form A i)
           -> { S : Σ'
             & (symbol_arity S = Arity.simple (ae_shape A i))
             * (symbol_class S = Judgement.class_of (ae_form A i))})
      (Sr' := (fun i_ob =>
           (f' (Sr i_ob).1; 
              (ap snd (Family.map_commutes _ _) @ fst (Sr i_ob).2
              , ap fst (Family.map_commutes _ _) @ snd (Sr i_ob).2)))
         : Judgement.is_object (ae_form A i)
           -> { S : Σ''
             & (symbol_arity S = Arity.simple (ae_shape A i))
             * (symbol_class S = Judgement.class_of (ae_form A i))})
   : fmap_judgement_total f' (judgement_of_premise i f Sr)
     = @judgement_of_premise _ _ A i _ (Signature.compose f' f) Sr'.
  Proof.
    eapply (ap (Build_judgement_total _)).
    refine (ap (fun Γ => Build_judgement (Build_raw_context _ Γ) _) _
           @ ap (Build_judgement _) _).
    - (* context part *)
      apply path_forall; intros x.
      apply inverse, Expression.fmap_compose.
    - (* hypothetical part *)
      eapply concat.
      { refine (fmap_hypothetical_instance_from_boundary_and_head _ _ _). }
      apply (ap2 (Judgement.hypothetical_instance_from_boundary_and_head _)).
      + apply inverse, fmap_hypothetical_boundary_compose.
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
        revert e_cS; apply SyntaxLemmas.inverse_sufficient;
          intro e; destruct e^; clear e.          
        revert e_aS; apply SyntaxLemmas.inverse_sufficient;
          intro e; destruct e^; clear e.
        apply idpath.
  Defined.
  
  Local Lemma flatten_fmap `{Funext}
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} (A : algebraic_extension Σ a)
    : Family.map_over (fmap_judgement_total (Metavariable.fmap1 f a))
        (flatten A) (flatten (fmap f A)).
  Proof.
    exists idmap.
    intros i.
    eapply concat. 2: { apply inverse, fmap_judgement_of_premise. }
    apply inverse, judgement_of_premise_fmap1.
    - eapply concat. { apply metavariable_fmap_compose. }
      eapply concat. 2: { apply inverse, metavariable_fmap_compose. }
      eapply concat. { apply ap, Family.id_left. }
      eapply concat. { eapply (ap (fun f => Metavariable.fmap f _)), Family.id_right. }
      apply inverse.                     
      eapply concat. { apply ap, Family.id_right. }
      eapply (ap (fun f => Metavariable.fmap f _)), Family.id_left.
    - apply path_forall. intros i_is_ob.
      destruct i as [i_ob | i_eq].
      + apply idpath.
      + destruct i_is_ob.
  Defined.

End Flattening.

Section Initial_Segment.

  Context {σ : shape_system}.

  (** Next few definitions are auxiliary for [initial_segment] below *)
  Local Definition initial_segment_premise_aux
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : family (hypothetical_form * σ.(shape_carrier))
  := Family.fmap (fun cl_γ : syntactic_class * σ.(shape_carrier) =>
                    (form_object cl_γ.(fst), cl_γ.(snd))) (ae_metas A r)
   + Family.fmap (fun cl_γ : syntactic_class * σ.(shape_carrier) =>
                    (form_equality cl_γ.(fst), cl_γ.(snd)))
       (Family.subfamily (ae_equality_premise A)
                         (fun j => ae_lt A (inr j) r)).

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
       (ae_lt A).

  Local Definition initial_segment_include_premise_lt_aux
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : ae_lt A (initial_segment_include_premise_aux _ _ i) r.
  Proof.
    destruct i as [ [ i_ob e ] | [i_eq e] ]; apply e.
  Defined.

  Definition initial_segment_compare_premise_metas
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : Family.map
        (ae_metas A (initial_segment_include_premise_aux _ _ i))
        (Family.subfamily (ae_metas A r) (fun j =>
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

  (* TODO: rename [ae_metas], [ae_signature] to [ae_premise_metas], [ae_premise_signature]? *)
  (** Auxiliary definition for [initial_segment] below *)
  Definition initial_segment_compare_signature
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} {r : A}
      (i : initial_segment_premise_aux A r)
    : Signature.map
        (ae_signature A
           (initial_segment_include_premise_aux _ _ i))
        (Metavariable.extend Σ
           (Family.subfamily (ae_metas A r) (fun j =>
           initial_segment_lt_aux _ _ (inl j) i))).
  Proof.
    apply Metavariable.fmap2, initial_segment_compare_premise_metas.
  Defined.

  Local Definition initial_segment
      {Σ : signature σ} {a} (A : algebraic_extension Σ a) (r : A)
    : algebraic_extension Σ (ae_metas A r).
  Proof.
    simple refine (Build_algebraic_extension _ _ _ _ _).
    - (* ae_equality_premise *)
      exact (Family.subfamily (ae_equality_premise A)
                              (fun j => ae_lt A (inr j) r)).
    - (* ae_lt *)
      apply initial_segment_lt_aux.
    - (* ae_raw_context_type *)
      intros i x.
      refine (Expression.fmap _ _).
      + apply initial_segment_compare_signature.
      + set (i_orig
          := initial_segment_include_premise_aux A r i).
        destruct i as [ ? | ? ]; refine (ae_raw_context_type A i_orig x).
    - (* ae_hypothetical_boundary *)
      intros i x.
      refine (Expression.fmap _ _).
      + apply initial_segment_compare_signature.
      + set (i_orig
          := initial_segment_include_premise_aux A r i).
        destruct i as [ ? | ? ]; refine (ae_hypothetical_boundary A i_orig x).
  Defined.

  (* Perhaps better as map (we’d have to define the notion of map first…)? *)
  Local Lemma initial_segment_fmap `{Funext}
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
      apply (ap2 (fun f e => rename f e)).
      + apply idpath.
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
          apply (ap (fun f => Expression.fmap f _)).
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
          apply (ap (fun f => Expression.fmap f _)).
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
      eapply concat. 2: { eapply rename_hypothetical_boundary_idmap. }
      apply (ap2 (fun f b => rename_hypothetical_boundary f b)).
      + apply idpath. 
      + simpl ap. apply path_forall; intros x.
        destruct i as [ i_ob | i_eq ].
        * simpl. unfold fmap_hypothetical_boundary.
          eapply concat.
          { eapply (ap (fun f => Expression.fmap f _)). 
            apply Metavariable.fmap_idmap. }
          eapply concat. { apply Expression.fmap_idmap. }
          eapply concat. { apply Expression.fmap_fmap. }
          apply inverse. 
          eapply concat. { apply Expression.fmap_fmap. }
          apply (ap (fun f => Expression.fmap f _)).
          eapply concat. { apply inverse, Metavariable.fmap_compose. }
          eapply concat. 2: { eapply Metavariable.fmap_compose. }
          apply (ap2 (fun f g => Metavariable.fmap f g)).
          -- eapply concat. { apply Family.id_right. }
             apply inverse.
             apply Family.id_left.
          -- apply idpath.
        * simpl. unfold fmap_hypothetical_boundary.
          eapply concat.
          { eapply (ap (fun f => Expression.fmap f _)). 
            apply Metavariable.fmap_idmap. }
          eapply concat. { apply Expression.fmap_idmap. }
          eapply concat. { apply Expression.fmap_fmap. }
          apply inverse. 
          eapply concat. { apply Expression.fmap_fmap. }
          apply (ap (fun f => Expression.fmap f _)).
          eapply concat. { apply inverse, Metavariable.fmap_compose. }
          eapply concat. 2: { eapply Metavariable.fmap_compose. }
          apply (ap2 (fun f g => Metavariable.fmap f g)).
          -- eapply concat. { apply Family.id_right. }
             apply inverse.
             apply Family.id_left.
          -- apply idpath.
  Time Defined.

  (* Really… probably better  *)
  Local Lemma flatten_initial_segment_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a} (p : A)
      (i : initial_segment A p)
    : flatten (initial_segment (fmap f A) p) i
    = flatten (fmap f (initial_segment A p)) i.
  Proof.
    admit.
  Admitted.

End Initial_Segment.