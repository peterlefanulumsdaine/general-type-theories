Require Import HoTT.
Require Import Syntax.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Syntax.SyntacticClass.
Require Import Syntax.Arity.

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

Section Examples.

  Context {σ : shape_system}.

  Local Definition empty : signature σ
  := [<>].

  Local Definition empty_rect Σ : map empty Σ
  := Family.empty_rect.

  Local Definition empty_rect_unique `{Funext} {Σ} (f : map empty Σ)
    : f = empty_rect Σ.
  Proof.
    apply Family.empty_rect_unique.
  Defined.
  
End Examples.

Arguments empty _ : clear implicits.