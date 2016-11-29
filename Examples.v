Require Import HoTT.
Require Import Auxiliary.
Require Import RawSyntax.

Section Types_as_shapes.
  Definition Type_Shape : Shape_System.
  Proof.
    refine {|
        Shape := Type ;
        positions := (fun A => A) ;
        shape_empty := Empty ;
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
    | f_empty => Empty
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

  Inductive DB_positions : nat -> Type :=
    | zero_db : forall {n}, DB_positions (S n)
    | succ_db : forall {n}, DB_positions n -> DB_positions (S n).

  Fixpoint DB_inl (n m : nat) (x : DB_positions n) : DB_positions (n + m).
  Proof.
    destruct x.
    - exact zero_db.
    - apply succ_db, DB_inl; exact x.
  Defined.

  Fixpoint DB_inr (n m : nat) (x : DB_positions m) : DB_positions (n + m).
  Proof.
    destruct n.
    - exact x.
    - apply succ_db, DB_inr; exact x. (* XXX Here "now" fails with f_equal. *)
  Defined.

  Lemma DB_is_empty : is_empty (DB_positions 0).
  Proof.
    constructor; intros P.
    assert (H : forall k i (p : k = 0), P (transport _ p i)).
    {
      intros n i.
      destruct i as [ k | k ? ];
      intros p; destruct (equiv_inverse equiv_path_nat p).
    }
    intros x; exact (H _ x (idpath _)).
  Defined.

  Definition DB_ext {n k : nat}
             (P : DB_positions (n.+1) -> Type)
             (i : DB_positions k)
    := forall (p : k = n.+1), P (transport DB_positions p i).

  Lemma S_injective {n m : nat} : S n = S m -> n = m.
  Proof.
    intro p. exact (ap pred p).
  Defined.

  (* NOTE: this is the only sticking point for computation of [DB_is_plusone], [DB_is_coprod].  If we could find an alternative proof of [ap_S_S_injective] which makes [ap_S_S_injective_idpath] a judgemental equality, then those would all compute. *)
  Lemma ap_S_S_injective {n m : nat} (p : S n = S m) :
    ap S (S_injective p) = p.
  Proof.
    apply hset_nat.
  Defined.

  Lemma ap_S_S_injective_idpath (n: nat) :
    ap_S_S_injective (idpath : n.+1 = n.+1) = idpath.
  Proof.
    apply path_ishprop.
  Defined.
  

  Lemma DB_is_plusone (n : nat) : is_plusone (DB_positions (n.+1)) (DB_positions n).
  Proof.
    simple refine {|
             plusone_top := zero_db ;
             plusone_next := succ_db |}.
    - intros P x f.
      transparent assert (H : (forall k (i : DB_positions k), DB_ext P i)).
      + intros k i.
        { destruct i as [l|l].
          - intro p.
            pose (q := S_injective p).
            refine (transport 
              (fun e => P (transport DB_positions e _))
              (ap_S_S_injective p : ap S q = p) _).
            clearbody q ; clear p.
            destruct q.
            exact x.            
          - intro p.
            pose (q := S_injective p).
            refine (transport 
              (fun e => P (transport DB_positions e _))
              (ap_S_S_injective p : ap S q = p) _).
            clearbody q ; clear p.
            destruct q.
            apply f. }
      + intro y. apply (H (n .+1) y idpath).
    - intros P x f. simpl.
      rewrite ap_S_S_injective_idpath. apply idpath.
    - intros P x f k. simpl.
      rewrite ap_S_S_injective_idpath. apply idpath.
  Defined.

  Lemma DB_is_coprod (n m : nat) :
    is_coprod (DB_positions (n + m)) (DB_positions n) (DB_positions m).
  Proof.
    simple refine
      {| coprod_inj1 := DB_inl _ _
      ;  coprod_inj2 := DB_inr _ _
      |}.
    (* coprod_rect *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + exact f2.
      + apply (plusone_rect _ _ (DB_is_plusone _)); simpl.
        * exact (f1 (zero_db)).
        * apply IH.
          -- intros i1. exact (f1 (succ_db i1)).
          -- exact f2.
    (* coprod_comp1 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + apply (empty_rect _ DB_is_empty).
      + apply (plusone_rect _ _ (DB_is_plusone _)).
        * apply (plusone_comp_top _ _ (DB_is_plusone _)).
        * intros i1. 
          refine (_ @ _).
            apply (plusone_comp_next _ _ (DB_is_plusone _)).
          refine (IH _ _ _ i1).
    (* coprod_comp2 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + intros i2; apply idpath.
      + intros i2.
        refine (_ @ _).
          apply (plusone_comp_next _ _ (DB_is_plusone _)).
        refine (IH _ _ _ i2).
  Defined.

  Definition DeBruijn : Shape_System.
  Proof.
    refine {| Shape := nat ;
              positions := DB_positions ;
              shape_empty := 0 ;
              shape_coprod := (fun n m => (n + m)%nat) ;
              shape_extend := S
           |}.
    (* shape_is_empty *)
    - apply DB_is_empty.
    (* shape_is_coprod *)
    - apply DB_is_coprod.
    (* shape_is_plusone *)
    - apply DB_is_plusone.
  Defined.

End DeBruijn.

(* TODO: variables as strings, or as natural numbers *)

(* TODO: Should also generalise to any constructively infinite type. *)