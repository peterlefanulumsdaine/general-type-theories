Require Import HoTT.
Require Import Auxiliary.Coproduct.

(* A _Shape_ abstract the kind of shapes that contexts and bindings can have.

  There are several motivations for this:

  - firstly, it allows the same code to simultaneously cover both syntax with
    de Bruijn indices and syntax with named variables — those will be two
    examples of shape systems.

  - secondly, it abstracts just the properties of both those settings that are
    really needed in the definition of substitution etc., hence giving a clean
    and robust interface.

  - thirdly, it is written with an eye towards possible later generalisation
    to infinitary settings, where genuinely different shape systems might occur.
*)

(** A record describing shapes that can be used for contexts and bindings. *)
Record shape_system :=
  { shape_carrier :> Type
  ; shape_position : shape_carrier -> Type
      (* each shape has some positions; maybe should map to sets *)
  ; shape_empty : shape_carrier (* the empty *)
  ; shape_is_empty : is_empty (shape_position shape_empty)
      (* the empty shape binds nothing *)
  ; shape_sum : shape_carrier -> shape_carrier -> shape_carrier
      (* the sum of two shapes *)
  ; shape_is_sum
      (* the positions in the sum are the sum of positions *)
     : forall γ δ : shape_carrier,
       Coproduct.is_coproduct
         (shape_position (shape_sum γ δ)) (shape_position γ) (shape_position δ)
  ; shape_extend : shape_carrier -> shape_carrier
      (* a shape extended by one more more position *)
  ; shape_is_extend
     : forall γ : shape_carrier,
       Coproduct.is_plusone (shape_position (shape_extend γ)) (shape_position γ)
  }.

Global Arguments shape_sum {_} _ _.
Global Arguments shape_is_sum {_} [_ _].
Global Arguments shape_is_empty {_}.

Coercion shape_position : shape_carrier >-> Sortclass.

Section Associativities.
(** Lemmas on associativity, unitality, etc of sums of shapes.*)

(* TODO: these could be upstreamed to [Coproduct], perhaps? 
If that makes them less convenient to apply, then they can at least be deduced
here from general lemmas about coproducts. *)

  Context {σ : shape_system}.

  (* use this and [fmap1], [fmap2] where they’ve previously been given inline, e.g. in [Expression.rename], [instantiate_rename]. *)
  Lemma fmap_shape_sum {γ γ' δ δ' : σ} (f : γ -> γ') (g : δ -> δ')
    : (shape_sum γ δ) -> (shape_sum γ' δ').
  Proof.
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros; apply (coproduct_inj1 (shape_is_sum)); auto.
    - intros; apply (coproduct_inj2 (shape_is_sum)); auto.
  Defined.

  Lemma fmap1_shape_sum {γ γ' δ : σ} (f : γ -> γ')
    : (shape_sum γ δ) -> (shape_sum γ' δ).
  Proof.
    exact (fmap_shape_sum f idmap).
  Defined.

  Lemma fmap2_shape_sum {γ δ δ' : σ} (g : δ -> δ')
    : (shape_sum γ δ) -> (shape_sum γ δ').
  Proof.
    exact (fmap_shape_sum idmap g).
  Defined.

  Definition shape_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 shape_is_sum
               : γ -> shape_sum γ (shape_empty _)).
  Proof.
    apply coproduct_empty_inj1_is_equiv, shape_is_empty.
  Defined.

  Definition shape_sum_empty_inl (γ : σ)
    : γ <~> shape_sum γ (shape_empty _)
  := BuildEquiv _ _ _ (shape_sum_empty_inl_is_equiv γ).

  Definition shape_sum_empty_inr_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj2 shape_is_sum
               : γ -> shape_sum (shape_empty _) γ).
  Proof.
    apply coproduct_empty_inj2_is_equiv, shape_is_empty.
  Defined.

  Definition shape_sum_empty_inr (γ : σ)
    : γ <~> shape_sum (shape_empty _) γ
  := BuildEquiv _ _ _ (shape_sum_empty_inr_is_equiv γ).

  Definition shape_assoc_ltor {γ δ κ : shape_carrier σ}
    : shape_sum (shape_sum γ δ) κ -> shape_sum γ (shape_sum δ κ).
  Proof.
    simple refine (Coproduct.assoc_ltor _ _ _ _);
      try apply shape_is_sum; try apply shape_is_sum.
  Defined.

  Definition shape_assoc_rtol {γ δ κ : shape_carrier σ}
    : shape_sum γ (shape_sum δ κ) -> shape_sum (shape_sum γ δ) κ.
  Proof.
    simple refine (Coproduct.assoc_rtol _ _ _ _);
      try apply shape_is_sum; try apply shape_is_sum.
  Defined.

  Definition shape_assoc (γ δ κ : shape_carrier σ)
    : shape_sum γ (shape_sum δ κ) <~> shape_sum (shape_sum γ δ) κ.
  Proof.
    simple refine (equiv_adjointify shape_assoc_rtol shape_assoc_ltor _ _);
      unfold Sect.
    - apply Coproduct.assoc_ltortol; apply shape_is_sum.
    - apply Coproduct.assoc_rtoltor; apply shape_is_sum.
  Defined.

  Instance shape_assoc_is_equiv {γ δ κ} : IsEquiv (shape_assoc γ δ κ)
    := equiv_isequiv (shape_assoc _ _ _).

End Associativities.