(** Arities, type classes, and other things that come before we actually describe syntax. *)

Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.

Inductive syntactic_class : Type := class_type | class_term.

Section Arity.
  Context `{σ : shape_system}.

  Global Definition arity : Type
    := family (syntactic_class * shape_carrier σ).

  (**

    Entries in the family represent arguments of a constructor; the [σ] component
    represents the variables bound in each argument.

    For instance, the [Π-intro] rule (i.e. fully annotated λ-abstraction) would have arity
    [Family_from_List [(Ty,0), (Ty,1), (Tm,1)]]; application would have arity
    [Family_from_List [(Ty,0), (Ty,1), (Tm,0), (Tm,0)]].

    The use of [family] instead of e.g. [list] serves two purposes. Firstly, it abstracts
    the aspects of the [list] version that we really need, and so makes the code
    significantly cleaner/more robust. Secondly, it allows this definition to be later
    re-used for non-finitary syntax, although we do not intend to explore that for now.
   *)

  (* Access functions for arity *)
  Global Definition argument_class {a : arity} (i : a) : syntactic_class := fst (a i).
  Global Definition argument_shape {a : arity} (i : a) : σ := snd (a i).

  (* Given a shape, return the arity of that shape in which all the
     syntactic classes are terms. *)
  Definition simple_arity (γ : σ)
    : arity
    := {| family_index := γ
        ; family_element i := (class_term, shape_empty _)
       |}.

End Arity.

Arguments arity _ : clear implicits.

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
