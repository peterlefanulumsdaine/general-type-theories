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


  Definition DB_ext {n k : nat}
             (P : DB_positions (n.+1) -> Type)
             (i : DB_positions k)
    := forall (p : k = n.+1), P (transport DB_positions p i).

  Lemma S_injective {n m : nat} : S n = S m -> n = m.
  Proof.
    intro p. exact (ap pred p).
  Defined.

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
  

  Lemma DB_isplusone (n : nat) : is_plusone (DB_positions (n.+1)) (DB_positions n).
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

  Lemma DB_positions_sum (n m : nat) :
    DB_positions n + DB_positions m <~> DB_positions (n + m).
  Proof.
    exists (fun x => match x with
                     | inl y => DB_inl n m y
                     | inr z => DB_inr n m z
                     end).
    simple refine (isequiv_adjointify _ _ _ _).
    - induction n as [|n' IH].
      + apply inr.
      + { refine (plusone_rect _ _ (DB_isplusone _) _ _ _).
          - left.
            apply zero_db.
          - intro i.
            destruct (IH i) as [j|j].
            + left.
              exact (succ_db j).
            + right.
              exact j. }
    - induction n as [|n' IH].
      + intro ; apply idpath.
      + refine (plusone_rect _ _ (DB_isplusone _) _ _ _).
        * lazy [nat_rect].
          rewrite plusone_comp_top.
          apply idpath.
        * intro i.
          unfold Sect in IH.
          lazy [nat_rect].
          rewrite plusone_comp_next.
          (* got stuck here. *)
          (* pose (E := IH i). *)
          (* lazy [nat_rect] in E. *)

          (* refine (_ @ _). *)
          (* refine (ap (fun c => match c with  *)
          (*     | inl y => _ *)
          (*     | inr z => _ *)
          (*     end) _). *)
          (* refine (ap (fun c => match c with  *)
          (*     | inl y => _ *)
          (*     | inr z => _ *)
          (*     end) _). *)
          
          (* exact E. *)

          (*   refine (_ @ _). *)
 
          (*     refine (plusone_comp_next _ _ (DB_isplusone _) _ _ _ _). *)
          (*     . *)
          (* rewrite IH. *)
          

          (* simpl. *)
          (* rewrite ap_S_S_injective_idpath. *)
          (* rewrite IH. *)
          (* simpl. *)
          (* apply idpath. *)
  Admitted.

  Definition DeBruijn : Shape_System.
  Proof.
    refine {| Shape := nat ;
              positions := DB_positions ;
              shape_empty := 0 ;
              shape_coprod := (fun n m => (n + m)%nat) ;
              shape_extend := S
           |}.
    (* shape_is_empty *)
    - constructor.
      intros P x.
      admit. (* P zero_db is empty *)
    (* shape_is_coprod *)
    - admit.
    (* shape_is_plusone *)
    - intro c.
      admit.
  Admitted.

End DeBruijn.

(* TODO: variables as strings, or as natural numbers *)

(* TODO: Should also generalise to any constructively infinite type. *)