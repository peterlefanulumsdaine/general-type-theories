Require Import HoTT.
Require Import Auxiliary RawSyntax.

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
