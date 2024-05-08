From Coq Require Import MSets Arith.
Require Import Coq.MSets.MSetEqProperties.
Require Import Coq.Bool.Bool.

Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.CookieRecord.
Require Import BrowserInfoFlow.HOPS.

From Hammer Require Import Hammer.

Module S := UrlSets.S.
Inductive response_content :=
| RpStatic : response_content
| RpScript : url.url -> response_content
| RpiFrame : url.url -> response_content
| RpPair : response_content -> response_content -> response_content.

Fixpoint content_eqb rc1 rc2 : bool :=
  match rc1, rc2 with
  | RpStatic,RpStatic => true
  | RpScript u1, RpScript u2 
  | RpiFrame u1, RpiFrame u2 => url.eqb u1 u2
  | RpPair rc11 rc12, RpPair rc21 rc22 => (content_eqb rc11 rc21) && (content_eqb rc12 rc22)
  | _,_ => false
  end.

Lemma content_eqb_refl : forall rc,
    content_eqb rc rc = true.
Proof.
  induction rc; simpl; try sfirstorder; try apply url.eqb_refl.
  rewrite IHrc1, IHrc2. sfirstorder.
Qed.

Lemma content_eqb_eq : forall rc1 rc2,
    content_eqb rc1 rc2 = true <-> rc1 = rc2.
Proof.
  induction rc1; simpl; split; intros; try (subst; sfirstorder use: url.eqb_eq).
  destruct rc2; inversion H. sfirstorder use: url.eqb_eq.
  destruct rc2; inversion H. sfirstorder use: url.eqb_eq.
  destruct rc2; inversion H. sfirstorder use: url.eqb_eq.
  destruct rc2; try inversion H. apply andb_true_iff in H.
  destruct H. eapply IHrc1_2 in H0. eapply IHrc1_1 in H.
  subst. reflexivity.
  hauto lq: on.
Qed.

Record response :=  mkResponse { response_url: url.url; content: response_content ; cookies : list SetCookie}.

(* Maybe later make "SW_update" that leaves all other fields *)
Definition eqb rp1 rp2 :=
  (url.eqb rp1.(response_url) rp2.(response_url)) &&
    (content_eqb rp1.(content) rp2.(content)) &&
    (l_eqb sc_eqb rp1.(cookies) rp2.(cookies)).

Lemma refl : forall rp, eqb rp rp = true.
Proof. 
  induction rp; unfold eqb; simpl in *; intros. unfold eqb. repeat (rewrite andb_true_iff; split).
  apply url.eqb_refl.  apply content_eqb_refl. eapply (eqb_refl_l_eqb_refl). eapply sc_eqb_refl.
Qed.

Lemma eqb_eq : forall rp1 rp2,
    eqb rp1 rp2 = true <-> rp1 = rp2.
Proof.
  split; intros. 2 : sauto use: refl.
  destruct rp1, rp2. unfold eqb in H; simpl in H.
  repeat (match goal with
          | [ H : _ && _ = true |- _] => apply andb_true_iff in H; destruct H
          end). f_equal; try hfcrush use: url.eqb_eq, content_eqb_eq.
  eapply (eqb_eq_l_eqb_eq). 2: inversion H0; reflexivity. eapply sc_eqb_eq.
Qed.
