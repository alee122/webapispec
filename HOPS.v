Require Import Coq.Lists.List.
Import ListNotations.
Require Import Bool.Bool.
Import BoolNotations.

From Hammer Require Import Hammer Tactics.

Definition op_eqb {A : Type} (A_eqb : A -> A -> bool) (a1 a2 : option A) : bool :=
    match a1,a2 with
    | None,None => true
    | Some a1',Some a2' => A_eqb a1' a2'
    | _,_ => false
    end.
          
Lemma eqb_refl_op_eqb_refl : forall {A : Type} A_eqb (a : option A),
    (forall a', A_eqb a' a' = true) ->
    op_eqb A_eqb a a = true.
Proof.
  intros. unfold op_eqb; simpl. destruct a; simpl.
  apply H. reflexivity.
Qed.

Lemma eqb_eq_op_eqb_eq : forall {A : Type} A_eqb (a1 a2 : option A),
    (forall a1' a2', A_eqb a1' a2' = true <-> a1' = a2') ->
    op_eqb A_eqb a1 a2 = true <-> a1 = a2.
Proof.
  intros. split. intros. destruct a1,a2; inversion H0; sfirstorder.
  sauto lq: on.
Qed.

Fixpoint l_eqb {A : Type} (A_eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [],[] => true
  | e1::l1',e2::l2' => (A_eqb e1 e2) && (l_eqb A_eqb l1' l2')
  | _,_ => false
  end.

Lemma eqb_refl_l_eqb_refl : forall {A : Type} A_eqb,
    (forall a', A_eqb a' a' = true) ->
    forall (l : list A), l_eqb A_eqb l l = true.
Proof.
  intros. induction l. sfirstorder. simpl. apply andb_true_iff. split.
  apply H. apply IHl.
Qed.

Lemma eqb_eq_l_eqb_eq : forall {A : Type} A_eqb,
    (forall a1' a2', A_eqb a1' a2' = true <-> a1' = a2') ->
    forall (l1 l2 : list A), l_eqb A_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1. destruct l2; sfirstorder.
  split. intros. destruct l2; inversion H0. apply andb_true_iff in H2. sfirstorder.
  intros; rewrite H0. eapply eqb_refl_l_eqb_refl. intros. erewrite H. reflexivity.
Qed.
