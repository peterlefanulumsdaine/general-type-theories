Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import RawSyntax.SyntacticClass.
Require Import RawSyntax.Arity.

Section Signature.

  Context {σ : shape_system}.

  Definition signature : Type
    := family (syntactic_class * arity σ).

  Definition symbol_class {Σ : signature} (S : Σ) : syntactic_class
    := fst (Σ S).

  Definition symbol_arity {Σ : signature} (S : Σ) : arity σ
    := snd (Σ S).

End Signature.

Arguments signature _ : clear implicits.

Section Map.

  Context {σ : shape_system}.
 
  Local Definition map (Σ Σ' : signature σ) : Type
    := Family.map Σ Σ'.

  Identity Coercion family_map_of_map : map >-> Family.map.

  Local Definition idmap (Σ : signature σ)
    : map Σ Σ
  := Family.idmap Σ.
  
  Local Definition compose {Σ Σ' Σ'' : signature σ}
    : map Σ' Σ'' -> map Σ Σ' -> map Σ Σ''
  := Family.compose.
  
End Map.
