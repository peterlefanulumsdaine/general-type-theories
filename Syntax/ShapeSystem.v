Require Import HoTT.
Require Import Auxiliary.Coproduct.

(* A _Shape_ abstract the kind of shapes that contexts and bindings can have.

  There are several motivations for this:

  - firstly, it allows the same code to simultaneously cover both syntax with de Bruijn
    indices and syntax with named variables — those will be two examples of shape systems.

  - secondly, it abstracts just the properties of both those settings that are really
    needed in the definition of substitution etc., hence giving a clean and robust
    interface.

  - thirdly, it is written with an eye towards possible later generalisation to infinitary
    settings, where genuinely different shape systems might occur.
*)

(** A record describing shapes that can be used for contexts and bindings. *)
Record shape_system :=
  { shape_carrier :> Type
  ; shape_position : shape_carrier -> Type (* each shape has some positions, maybe should map to sets *)
  ; shape_empty : shape_carrier (* the empty *)
  ; shape_is_empty : is_empty (shape_position shape_empty) (* the empty shape binds nothing *)
  ; shape_sum : shape_carrier -> shape_carrier -> shape_carrier (* the sum of two shapes *)
  ; shape_is_sum (* the positions in the sum are the sum of positions *)
     : forall γ δ : shape_carrier,
       Coproduct.is_coproduct (shape_position (shape_sum γ δ)) (shape_position γ) (shape_position δ)
  ; shape_extend : shape_carrier -> shape_carrier (* a shape extended by one more more position *)
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

  Definition shape_sum_empty_inl_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj1 shape_is_sum
               : γ -> shape_sum γ (shape_empty _)).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + intros i; exact i.
      + apply (empty_rect _ shape_is_empty).
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + intros i. apply ap.
        refine (coproduct_comp_inj1 _).
      + apply (empty_rect _ shape_is_empty).
    - intros i. refine (coproduct_comp_inj1 _).
  Defined.

  Definition shape_sum_empty_inl (γ : σ)
    : γ <~> shape_sum γ (shape_empty _)
  := BuildEquiv _ _ _ (shape_sum_empty_inl_is_equiv γ).

  Definition shape_sum_empty_inr_is_equiv (γ : σ)
    : IsEquiv (coproduct_inj2 shape_is_sum
               : γ -> shape_sum (shape_empty _) γ).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (coproduct_rect shape_is_sum).
      + apply (empty_rect _ shape_is_empty).
      + intros i; exact i.
    - unfold Sect. apply (coproduct_rect shape_is_sum).
      + apply (empty_rect _ shape_is_empty).
      + intros i. apply ap.
        refine (coproduct_comp_inj2 _).
    - intros i. refine (coproduct_comp_inj2 _).
  Defined.

  Definition shape_sum_empty_inr (γ : σ)
    : γ <~> shape_sum (shape_empty _) γ
  := BuildEquiv _ _ _ (shape_sum_empty_inr_is_equiv γ).

  (* TODO: unify with [Coproduct.assoc] *)
  Definition shape_assoc (γ δ κ : shape_carrier σ)
    : shape_sum γ (shape_sum δ κ) <~> shape_sum (shape_sum γ δ) κ.
  Proof.
    simple refine (equiv_adjointify _ _ _ _); unfold Sect.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj1 shape_is_sum), (coproduct_inj2 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj2 shape_is_sum), (coproduct_inj1 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj2 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
  Defined.

  Instance shape_assoc_is_equiv {γ δ κ} : IsEquiv (shape_assoc γ δ κ)
    := equiv_isequiv (shape_assoc _ _ _).

End Associativities.