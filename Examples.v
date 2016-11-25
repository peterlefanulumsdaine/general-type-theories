Require Import Auxiliary.
Require Import RawSyntax.
Require Import Arith.

Section Types_as_shapes.
  Definition Type_Shape : Shape_System.
  Proof.
    refine {|
        Shape := Type ;
        positions := (fun A => A) ;
        shape_empty := Empty_set ;
        shape_coprod := sum ;
        shape_extend := option
      |}.
    - constructor.
      intros P x; elim x.
    - intros A B.
      simple refine {|
          coprod_inj1 := @inl A B ;
          coprod_inj2 := @inr A B ;
        |}.
      + intros P f g x.
        destruct x as [a|b].
        * apply f.
        * apply g.
      + reflexivity.
      + reflexivity.
    - intro A.
      simple refine {|
          plusone_top := None ;
          plusone_next := @Some A
        |}.
      * { intros P e f [x|].
          - now apply f.
          - exact e. }
      * reflexivity.
      * reflexivity.
  Defined.

End Types_as_shapes.

Section Free_shapes.

  Inductive f_cxt : Type :=
  | f_empty : f_cxt
  | f_coprod : f_cxt -> f_cxt -> f_cxt
  | f_extend : f_cxt -> f_cxt.
  
  Fixpoint f_positions (c : f_cxt) : Type :=
    match c with
    | f_empty => Empty_set
    | f_coprod c d => sum (f_positions c) (f_positions d)
    | f_extend c => option (f_positions c)
    end.

  Definition Free_Shape : Shape_System.
  Proof.
    refine {|
        Shape := f_cxt ;
        positions := f_positions ;
        shape_empty := f_empty ;
        shape_coprod := f_coprod ;
        shape_extend := f_extend
      |}.
    - constructor.
      intros P x; elim x.
    - intros c d.
      simple refine {|
          coprod_inj1 := @inl (f_positions c) (f_positions d) ;
          coprod_inj2 := @inr (f_positions c) (f_positions d) ;
        |}.
      + intros P f g x.
        destruct x as [a|b].
        * apply f.
        * apply g.
      + reflexivity.
      + reflexivity.
    - intro c.
      simple refine {|
          plusone_top := None ;
          plusone_next := @Some (f_positions c)
        |}.
      * { intros P e f [x|].
          - now apply f.
          - exact e. }
      * reflexivity.
      * reflexivity.
  Defined.

End Free_shapes.

Section DeBruijn.

  Inductive DB_Set : nat -> Type :=
    | zero_db : forall {n}, DB_Set (S n)
    | succ_db : forall {n}, DB_Set n -> DB_Set (S n).

  Fixpoint DB_inl (n m : nat) (x : DB_Set n) : DB_Set (n + m).
  Proof.
    destruct x.
    - exact zero_db.
    - now apply succ_db, DB_inl.
  Defined.

  Fixpoint DB_inr (n m : nat) (x : DB_Set m) : DB_Set (n + m).
  Proof.
    destruct n.
    - exact x.
    - apply succ_db, DB_inr; exact x.
  Defined.

  (** Annoyingly, stdlib makes eq_nat opaque, we roll our own. *)

  (* Definition db_extend *)
  (*            {n m : nat} *)
  (*            (P : DB_Set (n + m) -> Type) : *)
  (*   forall k, DB_Set k -> Type. *)
  (* Proof. *)
  (*   intro k. *)
  (*   destruct (eq_nat_decide k (n + m)) as [E|N]. *)
  (*   - rewrite (proj1 (eq_nat_is_eq k (n + m)) E). *)
  (*     exact P. *)
  (*   - intros _ ; exact unit. *)
  (* Defined. *)

  (* (* The built-in eq_nat_refl is opaque! *) *)
  (* Lemma my_eq_nat_refl (n : nat) : eq_nat n n. *)
  (* Proof. *)
  (*   induction n. *)
  (*   - exact I. *)
  (*   - assumption. *)
  (* Defined. *)

  (* Lemma eq_nat_decide_refl (n : nat) : *)
  (*   eq_nat_decide n n = left (my_eq_nat_refl n). *)
  (* Proof. *)
  (*   induction n. *)
  (*   - reflexivity. *)
  (*   - assumption. *)
  (* Defined. *)

  (* Lemma eq_nat_is_eq_is_refl (n : nat) : *)
  (*   proj1 (eq_nat_is_eq n n) (my_eq_nat_refl n) = eq_refl n. *)
  (* Proof. *)
  (*   induction n. *)
  (*   - simpl. *)

  (* Definition db_extend_inject *)
  (*            (n m : nat) *)
  (*            (P : DB_Set (n + m) -> Type) *)
  (*            (i : DB_Set (n + m)) : *)
  (*   P i -> db_extend P (n + m) i. *)
  (* Proof. *)
  (*   intro x. *)
  (*   unfold db_extend. *)
  (*   destruct (eq_nat_decide_refl (n + m)) as [? E]. *)
  (*   rewrite E. *)

    
  (* Defined. *)

  Definition DeBruijn : Shape_System.
  Proof.
    refine {| ProtoCxt := nat ;
              vars := DB_Set ;
              shape_coprod := plus
           |}.
    (* protoctx_is_coprod *)
    - apply plus_is_coprod.

    (* protoctx_extend *)
    (* protoctx_is_extend *)

  simple refine (Build_Shape_System _ _ _ _ _ _).
  - exact nat.
  - exact Fin.t. (* should be fin *)
  - admit. (* should be + *)
  - admit.
  - admit. (* should be +1 *)
  - admit.
Admitted.

Definition natVars : Shape_System.
Proof.
  simple refine (Build_Shape_System _ _ _ _ _ _ _ _).
  - admit. (* finite subsets of nat *)
  - admit. (* should be El *)
  - admit. (* should be some implementation of disjoint union *)
  - admit.
  - admit. (* should be some choice of fresh var *)
  - admit.
Admitted.

(* TODO: Should also generalise to any constructively infinite type. *)