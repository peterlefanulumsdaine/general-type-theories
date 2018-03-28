Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Signature.

Section RawSyntax.

  Context {σ : shape_system}.

  Context {Σ : signature σ}.

  (* A raw syntactic expression of a syntactic class, relative to a shape *)
  Inductive raw_expression
    : syntactic_class -> σ -> Type
    :=
    (* a variable is a position in the context *)
    | raw_variable (γ : σ) (i : γ)
        : raw_expression class_term γ
    (* relative to a context [γ], given a symbol [S], if for each of its
       arguments we have a raw syntactic expression relative to [γ] extended by
       the argument's arity, [S args] is a raw syntactic expression over [γ] *)
    | raw_symbol (γ : σ) (S : Σ)
                 (args : forall (i : symbol_arity S),
                   raw_expression (argument_class i)
                                  (shape_sum γ (argument_shape i)))
      : raw_expression (symbol_class S) γ.

  Global Arguments raw_variable [_] _.
  Global Arguments raw_symbol [_] _ _.

  (** Convenient abbreviations, to improve readability of code. *)
  Definition raw_type := raw_expression class_type.
  Definition raw_term := raw_expression class_term.

  (* Supose [S] is a symbol whose arity is [a] and we would like to use [S]
     to form a raw expresssion. Then we have to provide arguments so that
     we can apply [S] to them. The following type describes these arguments. *)
  Definition arguments (a : arity σ) γ : Type
  := forall (i : a),
      raw_expression (argument_class i) (shape_sum γ (argument_shape i)).

  (* Useful, with [idpath] as the equality argument, when want wants to construct the
  smybol argument interactively — this is difficult with original [symb_raw] due to [class
  S] appearing in the conclusion. *)
  Definition raw_symbol'
      {γ} {cl} (S : Σ) (e : symbol_class S = cl)
      (args : arguments (symbol_arity S) γ)
    : raw_expression cl γ.
  Proof.
    destruct e.
    now apply raw_symbol.
  Defined.

End RawSyntax.

Global Arguments raw_expression {_} _ _ _.
Global Arguments raw_type {_} _ _.
Global Arguments raw_term {_} _ _.
Global Arguments arguments {_} _ _ _.

