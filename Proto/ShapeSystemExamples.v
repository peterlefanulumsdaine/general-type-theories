Require Import HoTT.
Require Import Raw.Syntax.
Require Import Auxiliary.Coproduct.
Require Import Proto.ShapeSystems.

Section Types_as_shapes.

  Definition is_empty_Empty : is_empty Empty.
  Proof.
    constructor.
    intros P x; elim x.
  Defined.

  Definition is_coproduct_sum (A B : Type)
    : is_coproduct (sum A B) A B.
  Proof.
    simple refine {|
        coproduct_inj1 := @inl A B ;
        coproduct_inj2 := @inr A B ;
      |}.
    - intros P f g x.
      destruct x as [a|b].
      + apply f.
      + apply g.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition is_plusone_option (A : Type)
    : is_plusone (option A) A.
  Proof.
    simple refine {|
        plusone_one := None ;
        plusone_inj := @Some A
        |}.
    - intros P e f [x|].
      + now apply f.
      + exact e.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition Type_Shape : Shape_System.
  Proof.
    refine {|
        Shape := Type ;
        positions := (fun A => A) ;
        shape_empty := Empty ;
        shape_coproduct := sum ;
        shape_extend := option
      |}.
    - apply is_empty_Empty.
    - apply is_coproduct_sum.
    - apply is_plusone_option.
  Defined.

End Types_as_shapes.

Section Free_shapes.

  Inductive f_cxt : Type :=
  | f_empty : f_cxt
  | f_coproduct : f_cxt -> f_cxt -> f_cxt
  | f_extend : f_cxt -> f_cxt.
  
  Fixpoint f_positions (c : f_cxt) : Type :=
    match c with
    | f_empty => Empty
    | f_coproduct c d => sum (f_positions c) (f_positions d)
    | f_extend c => option (f_positions c)
    end.

  Definition Free_Shape : Shape_System.
  Proof.
    refine {|
        Shape := f_cxt ;
        positions := f_positions ;
        shape_empty := f_empty ;
        shape_coproduct := f_coproduct ;
        shape_extend := f_extend
      |}.
    - apply is_empty_Empty.
    - intros. apply is_coproduct_sum.
    - intros. apply is_plusone_option.
  Defined.

End Free_shapes.

Section DeBruijn.

  Inductive DB_positions : nat -> Type :=
    | zero_db : forall {n}, DB_positions (S n)
    | succ_db : forall {n}, DB_positions n -> DB_positions (S n).

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
    - now apply succ_db, DB_inr; exact x.
  Defined.

  Lemma S_injective {n m : nat} : S n = S m -> n = m.
  Proof.
    intro p. exact (ap pred p).
  Defined.

  (* NOTE: this is the only sticking point for computation of [DB_is_plusone], [DB_is_coproduct].  If we could find an alternative proof of [ap_S_S_injective] which makes [ap_S_S_injective_idpath] a judgemental equality, then those would all compute.

  As it is, they will compute just when applied to actual numerals, but not for general numbers. *)
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
             plusone_one := zero_db ;
             plusone_inj := succ_db |}.
    - intros P x f.
      transparent assert (H : (forall k (i : DB_positions k), DB_ext P i)).
      { intros k i.
        destruct i as [l|l].
        * intro p.
          pose (q := S_injective p).
          refine (transport 
            (fun e => P (transport DB_positions e _))
            (ap_S_S_injective p : ap S q = p) _).
          clearbody q ; clear p.
          destruct q.
          exact x.            
        * intro p.
          pose (q := S_injective p).
          refine (transport 
            (fun e => P (transport DB_positions e _))
            (ap_S_S_injective p : ap S q = p) _).
          clearbody q ; clear p.
          destruct q.
          apply f. }
      intro y. apply (H (n .+1) y idpath).
    - intros P x f. simpl.
      rewrite ap_S_S_injective_idpath. apply idpath.
    - intros P x f k. simpl.
      rewrite ap_S_S_injective_idpath. apply idpath.
  Defined.

  Lemma DB_is_coproduct (n m : nat) :
    is_coproduct (DB_positions (n + m)) (DB_positions n) (DB_positions m).
  Proof.
    simple refine
      {| coproduct_inj1 := DB_inl _ _
      ;  coproduct_inj2 := DB_inr _ _
      |}.
    (* coproduct_rect *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + exact f2.
      + apply (plusone_rect _ _ (DB_is_plusone _)); simpl.
        * exact (f1 (zero_db)).
        * apply IH.
          -- intros i1. exact (f1 (succ_db i1)).
          -- exact f2.
    (* coproduct_comp1 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + apply (empty_rect _ DB_is_empty).
      + apply (plusone_rect _ _ (DB_is_plusone _)).
        * apply (plusone_comp_one _ _ (DB_is_plusone _)).
        * intros i1. 
          refine (_ @ _).
            apply (plusone_comp_inj _ _ (DB_is_plusone _)).
          refine (IH _ _ _ i1).
    (* coproduct_comp2 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + intros i2; apply idpath.
      + intros i2.
        refine (_ @ _).
          apply (plusone_comp_inj _ _ (DB_is_plusone _)).
        refine (IH _ _ _ i2).
  Defined.

  Definition DeBruijn : Shape_System.
  Proof.
    refine {| Shape := nat ;
              positions := DB_positions ;
              shape_empty := 0 ;
              shape_coproduct := (fun n m => (n + m)%nat) ;
              shape_extend := S
           |}.
    - apply DB_is_empty.
    - apply DB_is_coproduct.
    - apply DB_is_plusone.
  Defined.

End DeBruijn.

(* A second de Bruijn style shape system, defining the positions as a fixpoint instead of an inductive family. *)
 
Section DeBruijn_Fixpoint.

  Fixpoint DBF_positions (n : nat) : Type :=
    match n with
    | 0 => Empty
    | n'.+1 => option (DBF_positions n')
    end.

  Definition zero_dbf {n} : DBF_positions (n.+1)
  := None.

  Definition succ_dbf {n} (i : DBF_positions n) : DBF_positions (n.+1)
  := Some i.

  Fixpoint DBF_inl (n m : nat) (i : DBF_positions n) {struct n}
    : DBF_positions (n + m).
  Proof.
    destruct n as [ | n'].
    - destruct i.
    - destruct i as [ j | ].
      + exact (succ_dbf (DBF_inl _ _ j)).
      + exact zero_dbf.
  Defined.

  Fixpoint DBF_inr (n m : nat) (i : DBF_positions m) {struct n}
    : DBF_positions (n + m).
  Proof.
    destruct n as [ | n'].
    - exact i.
    - apply succ_dbf, DBF_inr, i.
  Defined.

  Lemma DBF_is_coproduct (n m : nat) :
    is_coproduct (DBF_positions (n + m)) (DBF_positions n) (DBF_positions m).
  Proof.
    simple refine
      {| coproduct_inj1 := DBF_inl _ _
      ;  coproduct_inj2 := DBF_inr _ _
      |}.
    (* coproduct_rect *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + exact f2.
      + apply (plusone_rect _ _ (is_plusone_option _)); simpl.
        * exact (f1 (zero_dbf)).
        * apply IH.
          -- intros i1. exact (f1 (succ_dbf i1)).
          -- exact f2.
    (* coproduct_comp1 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + intros [].
      + apply (plusone_rect _ _ (is_plusone_option _)).
        * apply idpath.
        * intros i1. exact (IH _ _ _ i1). 
    (* coproduct_comp2 *)
    - induction n as [ | n' IH]; intros P f1 f2.
      + intros i2; apply idpath.
      + intros i2. exact (IH _ _ _ i2).
  Defined.

  Definition DeBruijn_Fixpoint : Shape_System.
  Proof.
    refine {| Shape := nat ;
              positions := DBF_positions ;
              shape_empty := 0 ;
              shape_coproduct := (fun n m => (n + m)%nat) ;
              shape_extend := S
           |}.
    - apply is_empty_Empty.
    - apply DBF_is_coproduct.
    - intros; apply is_plusone_option.
  Defined.

End DeBruijn_Fixpoint.

(* TODO: (finite sets of) strings, or as natural numbers, or any constructively infinite type (maybe with decidable equality) *)

(* TODO: variables as “natural numbers <n” *)
