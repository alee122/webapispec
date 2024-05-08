From Hammer Require Import Hammer Tactics.
Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.CookieRecord.
Require Import Bool.Bool.
Import BoolNotations.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.Arith.
Require Import BrowserInfoFlow.HOPS.

Inductive Method :=
| MethodGet.
Definition method_eqb (m1 m2 : Method) := true.

Record request :=
  mkRequest {
      url__rq : url.url ;
      origin : option url.url ;
      method : Method ;
      body__rq : option nat ;
      cookies : list CookieMapping
    }.

Definition eqb rq1 rq2 := 
  url.eqb rq1.(url__rq) rq2.(url__rq) &&
    (op_eqb url_eqb rq1.(origin) rq2.(origin)) &&
    method_eqb rq1.(method) rq2.(method) &&
    (op_eqb Nat.eqb rq1.(body__rq) rq2.(body__rq)) &&
    (l_eqb cm_eqb rq1.(cookies) rq2.(cookies)).

Lemma eqb_refl : forall rq,
    eqb rq rq = true.
Proof.
  destruct rq; unfold eqb; simpl.
  repeat (apply andb_true_iff; split);
    try (* hammer result: *) sauto use:  Nat.eqb_refl, eqb_eq, url.eqb_refl unfold: url.url inv: option.
  sauto lq: on.
  sauto use: domain_eqb_refl unfold: url.url, host.
  eapply eqb_refl_l_eqb_refl. apply cm_eqb_refl.
Qed.
Lemma eqb_eq : forall rq1 rq2,
    eqb rq1 rq2 = true <-> rq1 = rq2.
Proof.
  split; intros. 2: sauto use: eqb_refl.
  destruct rq1, rq2; unfold eqb in H; simpl in *; destruct method0, method1; try hauto. 
  repeat (match goal with
          | [H : _ && _ = true |- _ ] => eapply andb_true_iff in H; destruct H
          end).
  f_equal; try strivial use: url.eqb_eq, cm_eqb_eq;
    try (eapply (eqb_eq_op_eqb_eq); eauto);
    try (eapply (eqb_eq_l_eqb_eq); eauto);
	sauto use: Url.eqb_eq, Nat.eqb_eq, cm_eqb_eq.
Qed.

Inductive Initiator :=
| ScriptLocation : Initiator
| iFrameLocation : Initiator
| iFrameContainer : Initiator -> Initiator
| PairFirst : Initiator -> Initiator
| PairSecond : Initiator -> Initiator
| WindowLocation : Initiator
| WindowContainer : Initiator -> Initiator.

Fixpoint initiator_eqb i1 i2 :=
  match i1,i2 with
  | ScriptLocation,ScriptLocation
  | iFrameLocation,iFrameLocation
  | WindowLocation,WindowLocation => true
  | iFrameContainer i1',iFrameContainer i2'
  | WindowContainer i1',WindowContainer i2'
  | PairFirst i1', PairFirst i2'
  | PairSecond i1', PairSecond i2' => initiator_eqb i1' i2'
  | _,_ => false
  end.

Lemma initiator_eqb_refl : forall i,
    initiator_eqb i i = true.
Proof.
  induction i; sfirstorder.
Qed.

Lemma initiator_eqb_eq : forall i1 i2,
    initiator_eqb i1 i2 = true <-> i1 = i2.
Proof.
  induction i1, i2; try sfirstorder; hauto lq: on.
Qed.

Fixpoint initiator_object i :=
  match i with
  | iFrameContainer i'
  | PairFirst i'
  | PairSecond i'
  | WindowContainer i' => initiator_object i'
  | WindowLocation
  | ScriptLocation
  | iFrameLocation => i
  end.

Record unfilled_request := mkUnfilledRequest
                            { initiator_rq : Initiator ;
                              u_rq : request }.

Definition ur_eqb ur1 ur2 :=
  initiator_eqb ur1.(initiator_rq) ur2.(initiator_rq) &&
    eqb ur1.(u_rq) ur2.(u_rq).

Lemma ur_eqb_refl : forall urq,
    ur_eqb urq urq = true.
Proof.
  sauto use: initiator_eqb_refl, eqb_refl, andb_true_intro unfold: u_rq, initiator_rq.
Qed.

Fixpoint is_parent (i1 i2 : Initiator) : bool :=
  match i1, i2 with
  (* Navigation through the tree: *)
  | PairFirst i1',PairFirst i2' => is_parent i1' i2'
  | PairSecond i1',PairSecond i2' => is_parent i1' i2'
  | iFrameContainer i1',iFrameContainer i2' => is_parent i1' i2'
  (* After finding the specific script, with a non-empty path to a frame *)
  | ScriptLocation,_ => true
  | _,_ => false
  end.

Definition assign_origin ur o : unfilled_request :=
  let rq := ur.(u_rq) in 
  mkUnfilledRequest ur.(initiator_rq) (mkRequest rq.(url__rq) o rq.(method) rq.(body__rq) rq.(cookies)).
