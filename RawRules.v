Require Import HoTT.
Require Import Auxiliary RawSyntax.

(* TODO: consider moving somewhere upstream *)
Section Raw_Syntax_Construction.

(* Arities of symbols will arise in two ways:

  1. Arities we write by hand.
 
    These will typically use [< … >] notation.

  2. Arities of metavariables, from [Metavariable_Extension].

    These will have only (Ty, shape_empty) arguments, and be indexed by the positions of some protocxt, which will itself probably be built up by [shape_extend].

  So we give functions/notations for giving arguments for each of these forms.

  Eventually, one should be able to write e.g.

  [S/ A ; e1 , e2 , e3 /]

  [M/ A ; e1 , e2 , e3 /]

  for the expression consisting of a symbol S (resp. a metavariable symbol M) applied to expressions e1, e2, e3.

*)

Definition inr_Metavariable {Σ} {a : Arity}
  : a -> Metavariable_Extension Σ a
:= inr.

Definition Args Σ (a : Arity) γ : Type
:= forall (i : a),
     Raw_Syntax Σ (arg_class i) (shape_coprod γ (arg_pcxt i)).


Definition empty_metavariable_args {Σ} {γ}
  : Args Σ (metavariable_arity (shape_empty _)) γ
:= empty_rect _ shape_is_empty _.

Definition snoc_metavariable_args {Σ} {γ δ : Proto_Cxt}
  : Args Σ (metavariable_arity δ) γ
  -> Raw_Syntax Σ Tm γ
  -> Args Σ (metavariable_arity (shape_extend _ δ)) γ.
Proof.
  intros ts t.
  simple refine (plusone_rect _ _ (shape_is_plusone _ δ) _ _ _); cbn.
  - refine (Raw_Weaken _ t).
    exact (coprod_inj1 shape_is_coprod).
  - exact ts.
Defined.

End Raw_Syntax_Construction.

Notation " '[M/' A /] " := (symb_raw (inr_Metavariable A) empty_metavariable_args) : raw_syntax_scope.

Notation " '[M/' A ; x , .. , z /] "
  := (symb_raw (inr_Metavariable A) (snoc_metavariable_args .. (snoc_metavariable_args (empty_metavariable_args) x) .. z)) : raw_syntax_scope.

Open Scope raw_syntax_scope.

Section Structural_Rules.

(* TODO: the context formation rules are a special case — need to be defined directly as closure conditions, since rules only provide hypothetical judgements. *)
  
Context (Σ : Signature).

(* The var rule:

  |– A type
-----------
x:A |– x:A

“The first rule of type club is… in context x:A, x is of type A.”

*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [< 
      (Ty , shape_empty _ )    (* [ A ] *)
    >] : Arity).
  (* Name the symbols. *)
  pose (A := None : Metas).
  exists Metas.
  (* premises *)
  - refine [< _ >].
    (* Premise:  |— A type *)
    exists (HJF (obj_HJF Ty)).
    exists [: :].
    intros [ [] | ].  (* destructing an “option Empty” *)
    exact [M/ A /].
  (* conclusion *)
  - exists (HJF (obj_HJF Tm)).
    (* context of conclusion *)
    exists [: [M/ A /] :].
    intros [ [ [] | ] | ]; cbn.  (* destructing an “opetion (option Empty)” *)
    (* the term *)
    + refine (var_raw _).
      apply (plusone_top _ _ (shape_is_plusone _ _)).
    (* the type *)
    + exact [M/ A /].
Defined.

End Structural_Rules.
