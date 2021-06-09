Require Import HoTT.HoTT.
Require Import Auxiliary.Coproduct.

(* A _Scope_ abstract the kind of scopes that contexts and bindings can have.

  There are several motivations for this:

  - firstly, it allows the same code to simultaneously cover both syntax with
    de Bruijn indices and syntax with named variables — those will be two
    examples of scope systems.

  - secondly, it abstracts just the properties of both those settings that are
    really needed in the definition of substitution etc., hence giving a clean
    and robust interface.

  - thirdly, it is written with an eye towards possible later generalisation
    to infinitary settings, where genuinely different scope systems might occur.
*)

(** A record describing scopes that can be used for contexts and bindings.
  \cref{def:scope-system} *)
Record scope_system :=
  { scope_carrier :> Type
  ; scope_position : scope_carrier -> Type
      (* each scope has some positions; maybe should map to sets *)
  ; scope_empty : scope_carrier (* the empty *)
  ; scope_is_empty : is_empty (scope_position scope_empty)
      (* the empty scope binds nothing *)
  ; scope_sum : scope_carrier -> scope_carrier -> scope_carrier
      (* the sum of two scopes *)
  ; scope_is_sum
      (* the positions in the sum are the sum of positions *)
     : forall γ δ : scope_carrier,
       Coproduct.is_coproduct
         (scope_position (scope_sum γ δ)) (scope_position γ) (scope_position δ)
  ; scope_extend : scope_carrier -> scope_carrier
      (* a scope extended by one more more position *)
  ; scope_is_extend
     : forall γ : scope_carrier,
       Coproduct.is_plusone (scope_position (scope_extend γ)) (scope_position γ)
  }.

Global Arguments scope_sum {_} _ _.
Global Arguments scope_is_sum {_ _ _}.
Global Arguments scope_is_empty {_}.

Coercion scope_position : scope_carrier >-> Sortclass.

Section Associativities.
(** Lemmas on associativity, unitality, etc of sums of scopes.*)

(* TODO: these could be upstreamed to [Coproduct], perhaps?
If that makes them less convenient to apply, then they can at least be deduced
here from general lemmas about coproducts. *)

  Context {σ : scope_system}.

  (* use this and [fmap1], [fmap2] where they’ve previously been given inline, e.g. in [rename], [instantiate_rename]. *)
  Lemma fmap_scope_sum {γ γ' δ δ' : σ} (f : γ -> γ') (g : δ -> δ')
    : (scope_sum γ δ) -> (scope_sum γ' δ').
  Proof.
    refine (coproduct_rect scope_is_sum _ _ _).
    - intros; apply (coproduct_inj1 (scope_is_sum)); auto.
    - intros; apply (coproduct_inj2 (scope_is_sum)); auto.
  Defined.

  Lemma fmap1_scope_sum {γ γ' δ : σ} (f : γ -> γ')
    : (scope_sum γ δ) -> (scope_sum γ' δ).
  Proof.
    exact (fmap_scope_sum f idmap).
  Defined.

  Lemma fmap2_scope_sum {γ δ δ' : σ} (g : δ -> δ')
    : (scope_sum γ δ) -> (scope_sum γ δ').
  Proof.
    exact (fmap_scope_sum idmap g).
  Defined.

  Definition scope_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 scope_is_sum
               : γ -> scope_sum γ (scope_empty _)).
  Proof.
    apply coproduct_empty_inj1_is_equiv, scope_is_empty.
  Defined.

  Definition scope_sum_empty_inl (γ : σ)
    : γ <~> scope_sum γ (scope_empty _)
  := Build_Equiv _ _ _ (scope_sum_empty_inl_is_equiv γ).

  Definition scope_sum_empty_inr_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj2 scope_is_sum
               : γ -> scope_sum (scope_empty _) γ).
  Proof.
    apply coproduct_empty_inj2_is_equiv, scope_is_empty.
  Defined.

  Definition scope_sum_empty_inr (γ : σ)
    : γ <~> scope_sum (scope_empty _) γ
  := Build_Equiv _ _ _ (scope_sum_empty_inr_is_equiv γ).

  Definition scope_assoc_ltor {γ δ κ : scope_carrier σ}
    : scope_sum (scope_sum γ δ) κ -> scope_sum γ (scope_sum δ κ).
  Proof.
    simple refine (Coproduct.assoc_ltor _ _ _ _);
      try apply scope_is_sum; try apply scope_is_sum.
  Defined.

  Definition scope_assoc_rtol {γ δ κ : scope_carrier σ}
    : scope_sum γ (scope_sum δ κ) -> scope_sum (scope_sum γ δ) κ.
  Proof.
    simple refine (Coproduct.assoc_rtol _ _ _ _);
      try apply scope_is_sum; try apply scope_is_sum.
  Defined.

  Definition scope_assoc (γ δ κ : scope_carrier σ)
    : scope_sum γ (scope_sum δ κ) <~> scope_sum (scope_sum γ δ) κ.
  Proof.
    simple refine (equiv_adjointify scope_assoc_rtol scope_assoc_ltor _ _);
      unfold pointwise_paths.
    - apply Coproduct.assoc_ltortol; apply scope_is_sum.
    - apply Coproduct.assoc_rtoltor; apply scope_is_sum.
  Defined.

  Instance scope_assoc_is_equiv {γ δ κ} : IsEquiv (scope_assoc γ δ κ)
    := equiv_isequiv (scope_assoc _ _ _).

End Associativities.
