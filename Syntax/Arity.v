From HoTT Require Import HoTT.

Require Import Syntax.ScopeSystem.
Require Import Auxiliary.Family.
Require Import Syntax.SyntacticClass.

Section Arity.
  Context `{σ : scope_system}.

  (** \cref{def:arity} *)
  Global Definition arity : Type
    := family (syntactic_class * scope_carrier σ).

  (**
  Entries in the family represent arguments of a constructor; the [σ] component
  represents the variables bound in each argument.

  For instance, the [Π-intro] rule (i.e. fully annotated λ-abstraction) would
  have arity [Family_from_List [(Ty,0), (Ty,1), (Tm,1)]]; application would
  have arity [Family_from_List [(Ty,0), (Ty,1), (Tm,0), (Tm,0)]].

  The use of [family] instead of e.g. [list] serves two purposes. Firstly, it
  abstracts the aspects of the [list] version that we really need, and so makes
  the code significantly cleaner/more robust. Secondly, it allows this
  definition to be later re-used for non-finitary syntax, although we do not
  intend to explore that for now.
   *)

  (* Access functions for arity *)
  Global Definition argument_class {a : arity} (i : a) : syntactic_class
    := fst (a i).
  Global Definition argument_scope {a : arity} (i : a) : σ := snd (a i).

  (* Given a scope, return the arity of that scope in which all the
     syntactic classes are terms. *)
  Local Definition simple (γ : σ) : arity
    := {| family_index := γ
        ; family_element i := (class_term, scope_empty _)
       |}.

End Arity.

Bind Scope family_scope with arity.

Arguments arity _ : clear implicits.
