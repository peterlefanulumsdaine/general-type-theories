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

  Definition db_extend
             {n m : nat}
             (P : DB_Set (n + m) -> Type) :
    forall k, DB_Set k -> Type.
  Proof.
    intro k.
    destruct (beq_nat_decide k (n + m)) as [E|_].
    - rewrite (proj1 (eq_nat_is_eq k (n + m)) E).
      exact P.
    - intros _ ; exact unit.
  Defined.

  Definition db_extend_inject
             (n m : nat)
             (P : DB_Set (n + m) -> Type)
             (i : DB_Set (n + m)) :
    P i -> db_extend P (n + m) i.
  Proof.
    intro x.
    unfold db_extend.



             


  Fixpoint DB_coprod_rect
           (n m : nat)
           (P : DB_Set (n + m) -> Type)
           (G : forall (y : DB_Set n), P (DB_inl n m y))
           (H : forall (z : DB_Set m), P (DB_inr n m z))
           (x : DB_Set (n + m)) :
    P x.
  Proof.
    induction n.
    - exact x.

    
    rewrite x.
    destruct n as [|n].
    - apply H.
    - dependent induction x.
      + apply (| zero_db).
      + apply (IH 
      






  Definition DB_inl (n m : nat) (x : DB_Set n) : DB_Set (n + m).
  Proof.
    destruct x as [k H].
    exists k.
    apply (lt_le_trans k n).
    - assumption.
    - now apply le_plus_l.
  Defined.

  Definition DB_inr (n m : nat) (y : DB_Set m) : DB_Set (n + m).
  Proof.
    destruct y as [k H].
    exists (n + k)%nat.
    now apply plus_lt_compat_l.
  Defined.

  Lemma lt_dec (n m : nat) : {n < m} + {m <= n}.

  Fixpoint DB_coprod_rect (n m : nat)
           (P : DB_Set (n + m) -> Type)
           (G : forall (g : DB_Set n), P (DB_inl n m g))
           (H : forall (h : DB_Set m), P (DB_inr n m h))
           (x : DB_Set (n + m)) :
    P x.
  Proof.
    destruct x as [k L].
    destruct (lt_dec k n) as [D|E].
    - apply G.
  Admitted.

  Lemma plus_is_coprod (n m : nat) : is_coprod (DB_Set (n + m)) (DB_Set n) (DB_Set m).
  Proof.
    simple refine {|
        coprod_inj1 := DB_inl n m ;
        coprod_inj2 := DB_inr n m ;
        coprod_rect := DB_coprod_rect n m
      |}.
    (* coprod_comp1 *)
    - intros.
      simpl.
    (* coprod_comp2 *)
    - reflexivity.
  Defined.

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