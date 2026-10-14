(* Anomaly "index out of bounds" in [apply] (legacy unifier) with universe
   polymorphism + primitive projections.

   Compile with plain:   rocq compile anomaly_mwe.v
   (no -noinit, no -indices-matter, no libraries needed)

   Observed on Rocq 9.1.1 and on master (9.3+alpha, commit 195cc6ea85):
     Error: Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
     Please report at http://rocq-prover.org/bugs/.
*)

Set Universe Polymorphism.
Set Primitive Projections.

(* A polymorphic primitive record with 2 universe levels: index@{u u0}. *)
Record family (X : Type) := { index : Type }.

Definition fmap (n : nat) (K : family nat) : family nat
  := {| index := index _ K |}.

(* A polymorphic inductive with only 1 universe level (fewer than [family]). *)
Inductive form@{u} : Type@{u} := fo.

Axiom K : family nat.
Definition slot (jf : form) : family nat := K.

Axiom T : family nat -> Type.
Axiom lemma : forall n P, T (fmap n P).

Goal forall x, T (slot x).
Proof.
  intros.
  apply lemma. (* Anomaly; [eapply lemma] too.
                  [refine (lemma _ _)] works; [simple apply lemma] gives an ordinary error. *)
Abort.
