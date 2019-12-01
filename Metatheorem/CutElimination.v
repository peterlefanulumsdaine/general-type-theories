Require Import HoTT.
Require Import Syntax.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.StructuralRule.
Require Import Typing.FlatTypeTheory.

(** The main goal of this file is the theorem [subst_elimination], showing
that for suitable theories [T], any derivation over [T] using the full 
structural rules can be translated into a derivation not using the rules
[subst_apply], [subst_equal].

The main subsidiary lemmas are [subst_apply_admissible] and
[subst_equal_admissible], showing that (generalisations of) these rules are
admissible over the closure system given by [T] together with the other
structural rules. *)

Section Subst_Free_Derivations.

  Context {σ} {Σ : signature σ}.

  Definition closure_system_without_subst (T : flat_type_theory Σ)
    := structural_rule_without_subst Σ + Family.bind T FlatRule.closure_system.

  Definition subst_free_derivation (T : flat_type_theory Σ)
    := derivation (closure_system_without_subst T).

  (* TODO: we will probably need to generalise various lemmas from ordinary to
  subst-free derivations.  Hopefully this can be done, as far as possible, by
  proving the original lemmas in type-class based ways, which will then apply
  automatically to subst-free derivations. *)

End Subst_Free_Derivations.

Section Flat_Conditions.
(** Conditions on flat rules/type theories sufficient for admissibility of
substitution to hold over them.

  The main such condition is: every rule should have empty conclusion context.
To use one established terminology, all rules should be in _universal form_,
as opposed to _hypothetical form_. 

  For substitution to (admissibly) respect equality, we additionally need to
know that the theory is _congruous_, in that for each flat rule of object form,
the associated congruence rule should be admissible (?derivable). *)

  Context {σ} {Σ : signature σ}.

  Definition in_universal_form (R : flat_rule Σ)
    := is_empty (shape_of_judgement (flat_rule_conclusion R)).

  Definition substitutive (T : flat_type_theory Σ)
    := forall r : T, in_universal_form (T r).

  (* TODO: once defined, upstream to [FlatRule]? *)
  Definition flat_congruence_rule (R : flat_rule Σ) : flat_rule Σ.
  Proof.
  Admitted. (* [flat_congruence_rule]: shouldn’t be too much work to define *)

  Definition congruous (T : flat_type_theory Σ) : Type.
  Admitted. (* [congruous]: requires definition upstream of _admissibiility_
             of a rule over a closure system/flat type theory. *)

End Flat_Conditions.

Section Subst_Elimination.

  Context {σ : shape_system} {Σ : signature σ}.

  Theorem subst_elimination
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} (d : FlatTypeTheory.derivation T (Family.empty _) J)
    : Closure.derivation (closure_system_without_subst T) (Family.empty _) J.
  Proof.
(* Sketch proof: start by roughly paralleling our definition of substitution, then do the main induction.  In detail,

  Lemma 1. given a cut-free derivation of a judgement J and a typed renaming into the context of J, can rename throughout derivation to get a cut-free derivation of the renamed judgement.

  Lemma 2. given a cut-free derivation of a judgement J, and a “context map” into the context of J, can substitute throughout derivation to get a cut-free derivartion of the substituted judgement, using Lemma 1 to extend the context map when going under binders.

  Lemma 3. the main induction to cut-eliminate in all proofs: if the last rule is anything apart from cut, then just cut-eliminate the subderivations inductively; if last rule is a cut into a hypothesis, then cut-eliminate the subderivations of well-typedness of the substitution; if last rule is a cut into a non-hypothesis, then cut-eliminate the derivations of the substitution and the main premise, and then substitute the substitution into the cut-free derivation of the main premise using Lemma 2. *)

  Admitted. (* Theorem [subst_elimination]: major goal, requires a lot of upstream work *)

End Subst_Elimination.

