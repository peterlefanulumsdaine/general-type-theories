Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.SyntaxLemmas.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatRule.

Section FlatTypeTheory.

  Context {σ : shape_system}.

  (** A flat type theory is just a family of flat rules. *)
  Definition flat_type_theory (Σ : signature σ) : Type
     := family (flat_rule Σ).

  (** The closure system associated to a flat type theory [T]:
  consists of structural rules for the signature, plus all instantiations
  of all rules of [T]. *)
  Local Definition closure_system {Σ : signature σ} (T : flat_type_theory Σ)
    : Closure.system (judgement_total Σ)
    := structural_rule Σ + Family.bind T FlatRule.closure_system.

  (** One can translate flat type theories under signature maps *)
  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_type_theory Σ -> flat_type_theory Σ'.
  Proof.
    apply Family.fmap, FlatRule.fmap, f.
  Defined.

End FlatTypeTheory.

Section Derivations.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (** A derivation of a total judgement in the given flat type theory [T] from
      hypotheses [H], with structural rules included. *)
  Local Definition derivation {Σ : signature σ} (T : flat_type_theory Σ) H
    : judgement_total Σ -> Type
  := Closure.derivation (closure_system T) H.

  (** Type of derivations of the conclusion of a rule [R] from its premises,
    in flat type theory [T], with given hypotheses. 

  I.e. type expressing the proposition that [R] is a derivable rule of [T]. *)
  Local Definition flat_rule_derivation
        (T : flat_type_theory Σ) (R : flat_rule Σ)
    : Type
  := derivation 
       (fmap include_symbol T)
       (flat_rule_premises R)
       (flat_rule_conclusion R).

End Derivations.

(** A first few utility derivations, usable for building up others. *)
(* TODO: unify with [UtilityDerivations.v]. *)
Section UtilityDerivations.

  Context {σ : shape_system} `{H_Funext : Funext}.

  (** Commonly-required analogue of [Closure.deduce']. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma deduce_modulo_rename {Σ : signature σ}
      {T : flat_type_theory Σ} {H : family _} {J : judgement_total _}
      (r : closure_system T)
      (e : shape_of_judgement J
          <~> shape_of_judgement (Closure.conclusion (closure_system T r)))
      (e_J : Judgement.rename (Closure.conclusion (closure_system T r)) e
             = J)
      (D : forall p : Closure.premises (closure_system T r),
          derivation T H (Closure.premises _ p))
    : derivation T H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, RawStructuralRule.rename.
      exists (Closure.conclusion (closure_system T r)). exact (_;e).
    - apply e_J.
    - intros [].
      exact (Closure.deduce _ _ r D).
  Defined.

  (** Commonly-required analogue of [Closure.deduce'], similar to [deduce_modulo_rename] above. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma hypothesis_modulo_rename {Σ : signature σ}
      {T : flat_type_theory Σ} {H : family (judgement_total _)}
      {J : judgement_total _}
      (h : H)
      (e : shape_of_judgement J <~> shape_of_judgement (H h))
      (e_J : Judgement.rename (H h) e = J)
    : derivation T H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, RawStructuralRule.rename.
      exists (H h). exact (_;e).
    - apply e_J.
    - intros [].
      exact (Closure.hypothesis _ _ h).
  Defined.

  (** Any rule of a type theory is derivable over the theory itself. *)
  (* TODO: consider name *)
  Lemma flat_type_theory_derive_rule `{Funext}
      {Σ : signature σ} (T : flat_type_theory Σ) (r : T)
    : flat_rule_derivation T (T r).
  Proof.
    unfold flat_rule_derivation.
    simple refine (deduce_modulo_rename _ _ _ _).
    - apply inr. exists r, [::]. apply unit_instantiation.
    - apply shape_sum_empty_inr.
    - cbn. apply judgement_eq_rename_iff_eq_rename_inverse.
      apply unit_instantiate_judgement.
    - cbn. intros p.
      simple refine (hypothesis_modulo_rename _ _ _).
      + exact p.
      + apply equiv_inverse, shape_sum_empty_inr.
      + cbn. apply inverse, unit_instantiate_judgement.
  Defined.

End UtilityDerivations.

(** Interaction between derivations and instantiation of metavariables *) 
Section Instantiation.

  Context `{Funext}.
  Context {σ : shape_system} {Σ : signature σ}.

  (** Given a flat rule [R] over a signature [Σ], an arity [a] specifying a
   metavariable extension, and an instantiation [I] of [a] in [Σ] over some
   context [Γ],

   any instance of [R] over the extended signature [extend Σ a] gets translated
   under [I] into an instance of [R] over [Σ], modulo renaming. 

   Note: this can’t be in [Raw.FlatRule], since it uses the structural rules. *)
  Local Definition instantiate_flat_rule
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : flat_rule Σ)
    : Closure.map_over
        (Metavariable.instantiate_judgement Γ I)
        (FlatRule.closure_system (FlatRule.fmap include_symbol r))
        (structural_rule Σ + FlatRule.closure_system r).
  Proof.
    intros [Δ J].
    (* The derivation essentially consists of the instance
     [(Metavariable.instantiate_context _ I Δ
     ; instantiate_instantiation I J)]
     wrapped in renamings along [shape_assoc].
     *)
    simple refine (Closure.deduce' _ _ _).
    { apply inl. apply RawStructuralRule.rename. cbn.
      set (j := Metavariable.instantiate_judgement Γ I
         (Closure.conclusion
            (FlatRule.closure_system (FlatRule.fmap include_symbol r) (Δ;J)))).
      exists (Judgement.rename j (shape_assoc _ _ _)^-1).
      refine (_ ; shape_assoc _ _ _).
    }
    { apply rename_judgement_inverse. }
    intros []; cbn.
    simple refine (Closure.deduce' _ _ _).
    { apply inr. 
      exists (Metavariable.instantiate_context _ I Δ).
      exact (instantiate_instantiation I J).
    }
    { apply instantiate_instantiate_judgement. }
    cbn. intros p.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, RawStructuralRule.rename. cbn.
      exists
        (Metavariable.instantiate_judgement Γ I
          (Metavariable.instantiate_judgement Δ J
            (fmap_judgement_total
              (Metavariable.fmap1 include_symbol _)
              (flat_rule_premises r p)))).
      refine (_ ; (equiv_inverse (shape_assoc _ _ _))).
    }
    { apply inverse, instantiate_instantiate_judgement. }
    intros [].
    simple refine (Closure.hypothesis' _ _).
    { exact p. }
    { apply idpath. }
  Defined.

  (** For any flat type theory [T], an an instantiation [I] from a metavariable 
  extension [Σ + a] of its signature, there is a closure system map from the
  interpretation of [T] over [Σ + a] to the interpretation of [Σ]: any
  rule of [T] instantiated under [Σ + a] translates back under [I] to an
  instantiation over [Σ] of the same rule of [T]. *)
  Local Definition instantiate
      (T : flat_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
   : Closure.map_over (Metavariable.instantiate_judgement Γ I)
       (closure_system (fmap include_symbol T)) 
       (closure_system T).
  Proof.
    apply Closure.sum_rect.
    - apply Closure.map_from_family_map.
      refine (Family.compose_over (Family.inl) (RawStructuralRule.instantiate _)).
    - intros [r I_r].
      refine (Closure.fmap_derivation _ (instantiate_flat_rule I (T r) I_r)).
      clear I_r.
      apply Closure.map_from_family_map.
      apply (Family.fmap_of_sum (Family.idmap _)).
      (* TODO: the following could be a lemma about [Family.bind]? *)
      apply Family.Build_map'.
      intros I_r. exists (r;I_r). apply idpath.
  Defined.

  (** Instantiate derivation [d] with metavariable instantiation [I]. *)
  Local Definition instantiate_derivation
      (T : flat_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      {hyps : family _} (j : judgement_total (Metavariable.extend Σ a))
      (d : derivation (fmap include_symbol T) hyps j)
    : derivation T (Family.fmap (Metavariable.instantiate_judgement _ I) hyps)
                   (Metavariable.instantiate_judgement _ I j).
  Proof.
    simple refine (Closure.fmap_derivation_over _ d).
    apply instantiate.
  Defined.

End Instantiation.
  
Section Maps.

  Context `{H_funext : Funext}.
  Context {σ : shape_system}.

  (* A flat type theory map [ff : T -> T'] over a map [f : Σ -> Σ'] of their signatures consists of derivations exhibiting the translation of each rule of [T] as a derivable rule of [T']. *)
  Local Definition map_over
    {Σ Σ': signature σ} (f : Signature.map Σ Σ')
    (T : flat_type_theory Σ) (T' : flat_type_theory Σ')
  := forall R : T,
      flat_rule_derivation T' (FlatRule.fmap f (T R)).

  Local Definition map
    {Σ} (T T' : flat_type_theory Σ)
  := map_over (Signature.idmap Σ) T T'.

  Local Definition fmap_closure_system_over
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
    (ff : map_over f T T')
  : Closure.map_over (fmap_judgement_total f)
      (closure_system T)
      (closure_system T').
  Proof.
    apply Closure.sum_rect.
    { (* structural rules *)
      apply Closure.map_from_family_map.
      refine (Family.compose_over (Family.inl) _).
      apply RawStructuralRule.fmap.
    }
    (* Logical rules *)
    intros [r [Γ I]]. cbn.
    (* From here, want to get goal into a form where it can be obtained
     by [instantiate_derivation]. *)
    eapply transport. { apply inverse, fmap_instantiate_judgement. }
    eapply (transport (fun H => derivation _ H _)).
    { apply inverse.
      eapply concat. { apply inverse, Family.fmap_compose. }
      eapply concat.
      { refine (ap10 _ _). apply ap, path_forall; intros i.
        apply fmap_instantiate_judgement. }
      apply Family.fmap_compose.
    }
    apply instantiate_derivation.
    apply ff.
  Defined.

  Local Definition fmap_closure_system
      {Σ : signature σ} {T T' : flat_type_theory Σ} (f : map T T')
    : Closure.map (closure_system T) (closure_system T').
  Proof.
    refine (transport (fun g => Closure.map_over g _ _) _
             (fmap_closure_system_over f)).
    apply path_forall; intros i. apply fmap_judgement_total_idmap.
  Defined.

  Local Lemma map_from_family_map
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
      (ff : Family.map_over (FlatRule.fmap f) T T')
    : map_over f T T'.
  Proof.
    intros R.
    refine (transport _ (Family.map_over_commutes ff R) _).
    apply flat_type_theory_derive_rule.
  Defined.

  Local Lemma map_to_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : flat_type_theory Σ)
    : map_over f T (fmap f T).
  Proof.
    apply map_from_family_map.
    apply Family.map_to_fmap.
  Defined.

  (* TODO: careful with naming: this should really be the actual functoriality in flat type theory maps. *)
  Local Lemma fmap_derivation
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : flat_type_theory Σ} {H : family (judgement_total Σ)} {J}
      (D : derivation T H J)
    : derivation
        (fmap f T)
        (Family.fmap (fmap_judgement_total f) H)
        (fmap_judgement_total f J).
  Proof.
    refine (Closure.fmap_derivation_over _ D).
    apply fmap_closure_system_over.
    apply map_to_fmap.
  Defined.

End Maps.
