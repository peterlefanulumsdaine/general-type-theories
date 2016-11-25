Require Import Auxiliary.
Require Import RawSyntax.
Require Import Arith.

Section TypesAsContexts.
  Definition TypesProtoCtx : ProtoCxtSystem.
  Proof.
    refine {|
        ProtoCxt := Type ;
        vars := (fun A => A) ;
        protocxt_coprod := sum ;
        protocxt_extend := option
      |}.
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
End TypesAsContexts.


Section FreeProtoCxt.

  Inductive f_cxt : Type :=
    | f_empty : f_cxt
    | f_coprod : f_cxt -> f_cxt -> f_cxt
    | f_extend : f_cxt -> f_cxt.

  Inductive f_vars : f_cxt -> Type :=
    | f_inl (c d : f_cxt) : f_vars c -> f_vars (f_coprod c d)
    | f_inr (c d : f_cxt) : f_vars d -> f_vars (f_coprod c d)
    | f_top (c : f_cxt) : f_vars (f_extend c)
    | f_next (c : f_cxt) : f_vars c -> f_vars (f_extend c).

  Definition extend {c d : f_cxt} (P : f_vars (f_coprod c d) -> Type) :
    forall e, f_vars e -> Type.
  Proof.
    intros e x ; destruct x.
    - exact (forall (E : c = c0),
             (match E in (_ = y) return (f_vars y -> Type) with
              | eq_refl => (fun z => P (f_inl c d z))
              end) x).
    - exact (forall (E : d = d0),
             (match E in (_ = y) return (f_vars y -> Type) with
              | eq_refl => (fun z => P (f_inr c d z))
              end) x).
    - exact unit.
    - exact unit.
  Defined.

  (* Lemma extend_eq *)
  (*       {c d : f_cxt} *)
  (*       (P : f_vars (f_coprod c d) -> Type) *)
  (*       (x : f_vars (f_coprod c d)) : *)
  (*   P x = extend P (f_coprod c d) x. *)
  (* Proof. *)
  (*   inversion x. *)
  (*   unfold extend; simpl. *)


  Lemma f_cxt_is_coprod (c d : f_cxt) : is_coprod (f_vars (f_coprod c d)) (f_vars c) (f_vars d).
  Proof.
    simple refine {| 
             coprod_inj1 := f_inl c d ;
             coprod_inj2 := f_inr c d
           |}.
    - intros P G H x.
      dependent induction x.

      assert (forall (y : f_vars (f_coprod c


  Definition FreeProtoCxt : ProtoCxtSystem.
  Proof.
    simple refine
           {|
             ProtoCxt := f_cxt ;
             vars := f_vars ;
             protocxt_coprod := f_coprod ;
             protocxt_extend := f_extend
           |}.
    - intros c d.
      simple refine 

  

End FreeProtoCxt.

Section DeBruijn.

  Inductive DBSet : nat -> Type :=
    | DB_Zero : forall {n}, DBSet (S n)
    | DB_Succ : forall {n}, DBSet n -> DBSet (S n).

  Fixpoint DB_inl (n m : nat) (x : DBSet n) : DBSet (n + m).
  Proof.
    destruct x.
    - exact DB_Zero.
    - now apply DB_Succ, DB_inl.
  Defined.

  Fixpoint DB_inr (n m : nat) (x : DBSet m) : DBSet (n + m).
  Proof.
    destruct n.
    - exact x.
    - apply DB_Succ, DB_inr; exact x.
  Defined.

  Fixpoint DB_coprod_rect
           (n m : nat)
           (P : DBSet (n + m) -> Type)
           (G : forall (y : DBSet n), P (DB_inl n m y))
           (H : forall (z : DBSet m), P (DB_inr n m z))
           (x : DBSet (n + m)) :
    P x.
  Proof.
    induction n.
    - exact x.

    
    rewrite x.
    destruct n as [|n].
    - apply H.
    - dependent induction x.
      + apply (G DB_Zero).
      + apply (IH 
      






  Definition DB_inl (n m : nat) (x : DBSet n) : DBSet (n + m).
  Proof.
    destruct x as [k H].
    exists k.
    apply (lt_le_trans k n).
    - assumption.
    - now apply le_plus_l.
  Defined.

  Definition DB_inr (n m : nat) (y : DBSet m) : DBSet (n + m).
  Proof.
    destruct y as [k H].
    exists (n + k)%nat.
    now apply plus_lt_compat_l.
  Defined.

  Lemma lt_dec (n m : nat) : {n < m} + {m <= n}.

  Fixpoint DB_coprod_rect (n m : nat)
           (P : DBSet (n + m) -> Type)
           (G : forall (g : DBSet n), P (DB_inl n m g))
           (H : forall (h : DBSet m), P (DB_inr n m h))
           (x : DBSet (n + m)) :
    P x.
  Proof.
    destruct x as [k L].
    destruct (lt_dec k n) as [D|E].
    - apply G.
  Admitted.

  Lemma plus_is_coprod (n m : nat) : is_coprod (DBSet (n + m)) (DBSet n) (DBSet m).
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

  Definition DeBruijn : ProtoCxtSystem.
  Proof.
    refine {| ProtoCxt := nat ;
              vars := DBSet ;
              protocxt_coprod := plus
           |}.
    (* protoctx_is_coprod *)
    - apply plus_is_coprod.

    (* protoctx_extend *)
    (* protoctx_is_extend *)

  simple refine (Build_ProtoCxtSystem _ _ _ _ _ _).
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