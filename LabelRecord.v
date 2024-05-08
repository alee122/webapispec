Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.SWSigs.
Require Import Coq.Bool.Bool.
Import BoolNotations.
From Coq Require Import MSets Arith.
Require Import Coq.MSets.MSetEqProperties.
From Hammer Require Import Hammer Tactics.

Module S := UrlSets.S.
Record label := mkLabel { origin_url: url.url; scripts: S.t }.

Definition eqb (l1 l2 : label) :=
  url.eqb l1.(origin_url) l2.(origin_url) && S.equal l1.(scripts) l2.(scripts).

Lemma refl : forall l, eqb l l = true.
Proof.
  destruct l. unfold eqb, url_eqb; simpl.
  erewrite url.eqb_refl.
  (* hammer result: *) sauto use: UrlSets.SAx.equal_refl, andb_true_intro.
Qed.

Definition flowb l1 l2 := url.eqb l1.(origin_url) l2.(origin_url) && S.subset l1.(scripts) l2.(scripts).
(* maybe replace the boolean with elements of the security lattice? ICFlow, IFlow, CFlow, NoFlow idk *) 
Definition can_flow l1 l2 := flowb l1 l2 = true.

Lemma flowb_can_flow : forall (l1 l2 : label),
    flowb l1 l2 = true <-> can_flow l1 l2.
Proof.
  split; intros; eauto.
Qed.

Lemma flow_transitivity : forall (l1 l2 l3 : label),
    can_flow l1 l2 /\ can_flow l2 l3 -> can_flow l1 l3.
Proof.
  unfold can_flow, flowb; intros.
  repeat (match goal with
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ && _ = true |- _ ] => eapply andb_true_iff in H; destruct H
          end).
  eapply andb_true_iff. split.
  eapply url.url_eqb_trans; eauto.
  (* hammer proof: *) sauto use: UrlSets.subset_transitivity unfold: scripts.
Qed.

Lemma flow_reflexivity : forall (l : label),
    can_flow l l.
Proof.
  intros; unfold can_flow, flowb. erewrite andb_true_iff. split;
    sauto use: url.eqb_refl, UrlSets.SAx.subset_refl.
Qed.
