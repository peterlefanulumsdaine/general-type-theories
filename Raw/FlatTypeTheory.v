Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.RawSubstitution.
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
       (flat_rule_premises _ R)
       (flat_rule_conclusion _ R).

End Derivations.

Section Instantiation.

  Context {σ : shape_system} {Σ : signature σ}.

  (* TODO: upstream to [FlatRule] *)
  Definition instantiate_flat_rule
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : flat_rule Σ)
    : Family.map_over
        (Closure.fmap (Metavariable.instantiate_judgement Γ I))
        (FlatRule.closure_system (FlatRule.fmap include_symbol r))
        (FlatRule.closure_system r).
  Proof.
    (* Sketch: will require lemma about instantiating twice! *)
  Admitted.

  (* TODO: upstream to [RawStructuralRule] *)
  Definition instantiate_structural_rule
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
    : Family.map_over
        (Closure.fmap (Metavariable.instantiate_judgement Γ I))
        (structural_rule (Metavariable.extend Σ a))
        (structural_rule Σ).
  Proof.
    (* Sketch: do this by hand for the ones given as closure conditions;
     for the ones given as flat rules, use [instantiate_flat_rule]. *)
  Admitted.

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
    apply Closure.map_from_family_map.
    apply Family.fmap_of_sum.
    - apply instantiate_structural_rule.
    - apply Family.Build_map'.
      intros [r I_r].
      exists (r;instantiate_flat_rule I (T r) I_r).
      exact (Family.map_over_commutes (instantiate_flat_rule I (T r)) _).
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

  Context `{H : Funext}.
  Context {σ : shape_system}.

  (* A flat type theory map [ff : T -> T'] over a map [f : Σ -> Σ'] of their signatures consists of derivations exhibiting the translation of each rule of [T] as a derivable rule of [T']. *)
  Local Definition map_over
    {Σ Σ': signature σ} (f : Signature.map Σ Σ')
    (T : flat_type_theory Σ) (T' : flat_type_theory Σ')
  := forall R : T,
      flat_rule_derivation T' (FlatRule.fmap f (T R)).

  Local Definition fmap_closure_system
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
      eapply concat. { apply inverse, Family.fmap_comp. }
      eapply concat.
      { refine (ap10 _ _). apply ap, path_forall; intros i.
        apply fmap_instantiate_judgement. }
      apply Family.fmap_comp.
    }
    apply instantiate_derivation.
    apply ff.
  Defined.

  (* TODO: maps of type theories preserve derivability. *)
End Maps.
