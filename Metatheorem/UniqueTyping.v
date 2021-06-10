
From HoTT Require Import HoTT.
Close Scope mc_scope. (* to make notations like [A * B] work easily *)

Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.All.
Require Import Presented.PresentedRawTypeTheory.

(* Main goals of this file: 

- [is_tight_type_theory]: tightness of a raw type theory
- [unique_typing]: theorem giving unique typing, for any tight type theory
*)

(* TODO: upstream contents of this section periodically, but keep this section as a holding pen as long as the file is under heavy development. *)
Section Auxiliary.

  (* TODO: maybe better as [Contr { y : B & R x y }]?  Try refactoring; see how it plays with coercions. *)
  Record functional_relation {A B} (R : A -> B -> Type) : Type
  := {
    total (x:A) : { y : B & R x y } ;
    unique {x} {y y'}: R x y -> R x y' -> y = y'
  }.

  Definition function_of_functional_relation
      {A B} {R : A -> B -> Type} (R_fun : functional_relation R)
    : A -> B
  := fun a => (total _ R_fun a).1.

  Coercion function_of_functional_relation : functional_relation >-> Funclass.

  Definition function_of_functional_relation_is_related
      {A B} {R : A -> B -> Type} (R_fun : functional_relation R)
    : forall a : A, R a (R_fun a)
  := fun a => (total _ R_fun a).2.

  Record is_one_to_one_correspondence {A B} (R : A -> B -> Type)
  := {
    forward : functional_relation R ;
    backward : functional_relation (flip R)
  }.

End Auxiliary.

Section Fix_Scope_System.

Context {σ : scope_system}.

Definition raw_rule_object_premise {Σ : signature σ} (R : raw_rule Σ)
    : Type
  := {i : raw_rule_premise R
          & Judgement.is_object (raw_rule_premise R i)}.

(* TODO: unify this with the similar construction in [Presented.AlgebraicExtension.judgement_of_premise]. *)
Definition meta_generic_application {Σ : signature σ} {a : arity σ} (i : a)
  : raw_expression (Metavariable.extend Σ a)
      (argument_class i) (argument_scope i).
Proof.
  simple refine (raw_symbol' _ _ _).
  * apply inr, i.
  * reflexivity.
  * intro j. apply raw_variable.
    exact (coproduct_inj1 scope_is_sum j).
Defined.

Definition premise_introduces_meta {Σ : signature σ} {R : raw_rule Σ}
    (p : raw_rule_object_premise R) (m : raw_rule_metas R)
  : Type.
Proof.
  simple refine { e : _ * _ & _}.
  - exact (class_of (raw_rule_premise R p.1)
          = argument_class m).
  - exact ((context_of_judgement (raw_rule_premise R p.1) : σ)
          = argument_scope m).
  - exact (transport _ (snd e)
           (transport (fun cl => raw_expression _ cl _) (fst e)
             (Judgement.head (raw_rule_premise R p.1) p.2))
            = meta_generic_application m).
Defined.

Definition is_tight_rule {Σ : signature σ} (R : raw_rule Σ)
  : Type
:= is_one_to_one_correspondence (@premise_introduces_meta _ R).

Definition raw_type_theory_object_rule
    {Σ : signature σ} (T : raw_type_theory Σ)
  : Type
:= { R :T & Judgement.is_object (raw_rule_conclusion (T R)) }.

Coercion pr1_raw_type_theory_object_rule
    {Σ : signature σ} (T : raw_type_theory Σ)
  : raw_type_theory_object_rule T -> T
  := pr1.

(* TODO: unify this with the similar construction in [Presented.RawTypeTheory]. *)
Definition symbol_generic_application {Σ : signature σ} (S : Σ)
  : raw_expression (Metavariable.extend Σ (symbol_arity S))
      (symbol_class S) (scope_empty _).
Proof.
  srapply raw_symbol'.
  * apply inl, S.
  * reflexivity.
  * intro m.
    refine (rename _ (meta_generic_application m)).
    apply (coproduct_inj2 scope_is_sum).
Defined.

Record rule_introduces_symbol {Σ : signature σ} (R : raw_rule Σ) (S : Σ)
:= {
  symbol_rule_metas : raw_rule_metas R = symbol_arity S;
  symbol_rule_is_object : Judgement.is_object (raw_rule_conclusion R);
  symbol_rule_class : class_of (raw_rule_conclusion R) = symbol_class S;
  symbol_rule_context
    : (context_of_judgement (raw_rule_conclusion R) : σ) = scope_empty _;
  symbol_rule_conclusion
    : (transport _ symbol_rule_context
      (transport (fun cl => raw_expression _ cl _) symbol_rule_class
      (transport (fun a => raw_expression (_ a) _ _) symbol_rule_metas
        (Judgement.head (raw_rule_conclusion R) symbol_rule_is_object))))
    = symbol_generic_application S
}.
(* Note: this definition involves transport along an equality of signatures.
  [Metavariable.extend Σ (raw_rule_metas R))
  = Metavariable.extend Σ (symbol_arity S)]
coming from the equality [raw_rule_metas R = symbol_arity S].

If it turns out that transport in the signature is unpleasant to work with,
we could instead use a translation along the signature map induced by the equality,
or even replace the equality with an equivalence of arities.

Presumably this will be easiest to work with by setting things up so that the raw rule is abstract, and so it and the equalities can be destructed. *)

Definition is_tight_type_theory {Σ : signature σ} (T : raw_type_theory Σ)
    : Type
  := (forall R : T, is_tight_rule (T R))
     * is_one_to_one_correspondence
         (fun (R : raw_type_theory_object_rule T) S
              => rule_introduces_symbol (T R.1) S).

(* We can now state the main goal of the file: *)  
Theorem unique_typing {Σ : signature σ} (T : raw_type_theory Σ)
    (T_tight : is_tight_type_theory T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : RawTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (d' : RawTypeTheory.derivation T [<>] [! Γ |- a ; A' !])
  : RawTypeTheory.derivation T [<>] [! Γ |- A ≡ A' !].
Proof.
Admitted.
(* TODO: make sure this is updated to include extra hypothesis that may be needed (e.g. possibly substitutivity). *)

(* Sketch proof: we will take a slightly different approach from the paper, proving first the “natural type” theorem, and then deducing unique typing as a corollary. *)

Definition natural_type {Σ : signature σ}
    {T : raw_type_theory Σ} (T_tight : is_tight_type_theory T)
    (Γ : raw_context Σ) (t : raw_term Σ Γ)
  : raw_type Σ Γ.
Proof.
  destruct Γ as [γ Γ]. simpl in t |- *.

  induction t as [ γ i | γ S t_args nat_ty_t_args].
  (* For a variable: look up its type in the context. *)
  { exact (Γ i). } 
  (* For a symbol application,
  - find the rule introducing the symbol;
  - take the type from the conclusion of this rule,
  - instantiated using the arguments of the application.
   *)
  assert { R_S : raw_rule Σ
                 & is_tight_rule R_S * rule_introduces_symbol R_S S }
    as [R_S [R_S_tight R_S_introduces_S]].
  { simple refine (_;_); try split.
    - exact (T (backward _ (snd T_tight) S)).
    - apply (fst (T_tight)).
    - apply (function_of_functional_relation_is_related
               (backward _ (snd T_tight))).
  }
  refine (rename _ (instantiate_expression _ _)).
  - exact (scope_sum_empty_inl γ)^-1.
  - admit. (* [t_args] should be viewable as an instantiation of [R_S]. Maybe factor this out? *)
  - admit. (* extract the type of the conclusion of [R_S] *)
Admitted.
(* TODOs:
- implicit args for [forward], [backward]
- define access functions for tightness?
*)

(* TODO: consider naming *)
(* TODO: further acceptability hypotheses on [T] may be necessary *) 
Definition natural_type_theorem
    {Σ : signature σ} {T : raw_type_theory Σ}
    (T_tight : is_tight_type_theory T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A : raw_type Σ Γ)
    (d : RawTypeTheory.derivation T [<>] [! Γ |- a ; A !])
    (T_a := natural_type T_tight Γ a)
  : RawTypeTheory.derivation T [<>] [! Γ |- a ; T_a  !]
    * RawTypeTheory.derivation T [<>] [! Γ |- A ≡ T_a !].
Admitted.

(* TODO: now conclude unique typing as corollary of this. *)

End Fix_Scope_System.
