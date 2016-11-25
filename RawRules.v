Require Import HoTT.
Require Import Auxiliary RawSyntax.

Section Structural_Rules.

(* TODO: the context formation rules are a special case — need to be defined directly as closure conditions, since rules only provide hypothetical judgements. *)
  
Context (Σ : Signature).

(* The var rule:

  |– A type
-----------
x:A |– x:A
*)

Definition var_raw_rule : Raw_Rule Σ.
Proof.
  (* arity/metavariables of rule *)
  pose (Metas := [< 
      (Ty , shape_empty _ )    (* [ A ] *)
    >] : Arity).
  pose (A_symbol := inr None : Metavariable_Extension Σ Metas).
  transparent assert (A_raw_type : (Raw_Syntax (Metavariable_Extension Σ Metas)
             Ty (shape_empty _))).
    refine (symb_raw A_symbol _).
    apply (empty_rect _ shape_is_empty).
  exists Metas.
  (* premises *)
  - refine [< _ >].
    (* Premise:  |— A type *)
    exists (HJF (obj_HJF Ty)).
    exists [: :].
    intros [ [] | ].  (* destructing an “option Empty” *)
    exact A_raw_type.
  (* conclusion *)
  - exists (HJF (obj_HJF Tm)).
    (* context of conclusion *)
    exists [: A_raw_type :].
    intros [ [ [] | ] | ]; cbn.  (* destructing an “opetion (option Empty)” *)
    (* the term *)
    + refine (var_raw _).
      apply (plusone_top _ _ (shape_is_plusone _ _)).
    (* the type *)
    + refine (Raw_Weaken _ A_raw_type).
      apply (plusone_next _ _ (shape_is_plusone _ _)).
Defined.

End Structural_Rules.
