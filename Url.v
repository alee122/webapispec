From Coq Require Import MSets Arith.
Require Import Coq.MSets.MSetEqProperties.
Require Import Coq.Bool.Bool.
Import BoolNotations.

From Hammer Require Import Hammer Tactics.

Inductive Protocol :=
| ProtocolHTTP
| ProtocolHTTPS.

Definition protocol_eqb p1 p2 :=
  match p1,p2 with
  | ProtocolHTTP, ProtocolHTTP => true 
  | ProtocolHTTPS, ProtocolHTTPS => true 
  | _,_ => false
  end.

Lemma protocol_eqb_eq : forall p1 p2,
    protocol_eqb p1 p2 = true <-> p1 = p2.
Proof.
  (* hammer proof: *) sauto lq: on.
Qed.

Lemma protocol_eqb_refl : forall p,
    protocol_eqb p p = true.
Proof.
  (* hammer proof: *) sauto lq: on.
Qed.

Inductive Domain :=
| domain : nat -> Domain
| subdomain : nat -> Domain -> Domain.
Fixpoint domain_eqb d1 d2 :=
  match d1,d2 with
  | domain n1, domain n2 => Nat.eqb n1 n2
  | subdomain n1 d1', subdomain n2 d2' => Nat.eqb n1 n2 && domain_eqb d1' d2'
  | _,_ => false
  end.
Fixpoint sub_or_eq_domain d1 d2 :=
  domain_eqb d1 d2 || 
  match d1, d2 with
  | subdomain _ d1', _ => sub_or_eq_domain d1' d2
  | _,_ => false
  end.
Lemma domain_eqb_refl : forall d,
    domain_eqb d d = true.
Proof.
  induction d; simpl; sauto use: Nat.eqb_refl, andb_true_intro.
Qed.

Lemma Gt_Lt_symm : forall x y,
    (x ?= y)%nat = Gt <-> (y ?= x)%nat = Lt.
Proof.
  split; hfcrush use: Nat.compare_gt_iff, nat_compare_lt.
Qed.

Lemma domain_eqb_eq : forall d1 d2,
    domain_eqb d1 d2 = true <-> d1 = d2.
Proof.
  induction d1; split; intros;
    [destruct d2; inversion H
    | rewrite H; eapply domain_eqb_refl
    | destruct d2; inversion H
    | rewrite H; eapply domain_eqb_refl].

  eapply Nat.eqb_eq in H1. rewrite H1. reflexivity.
  eapply andb_true_iff in H1. destruct H1.
  eapply Nat.eqb_eq in H0. eapply IHd1 in H1. subst. reflexivity.
Qed.

Fixpoint domain_compare (d1 d2 : Domain) : comparison :=
  match d1,d2 with
  | domain n1, domain n2 => Nat.compare n1 n2
  | subdomain _ _, domain _ => Lt
  | domain _, subdomain _ _ => Gt
  | subdomain n1 d1', subdomain n2 d2' =>
      match (domain_compare d1' d2') with
      | Eq => Nat.compare n1 n2
      | Lt => Lt
      | Gt => Gt
      end
  end.

Lemma domain_compare_refl : forall d,
    domain_compare d d = Eq.
Proof.
  induction d; simpl. eapply Nat.compare_refl.
  rewrite IHd. eapply Nat.compare_refl.
Qed.

Lemma domain_compare_eq : forall d1 d2,
    domain_compare d1 d2 = Eq -> d1 = d2.
Proof.
  induction d1; intros; destruct d2; intros; inversion H;
  hfcrush use: Nat.lt_irrefl, Nat.compare_refl, Nat.compare_eq_iff, Nat.compare_gt_iff inv: comparison.
Qed.
Lemma domain_compare_eq_iff : forall d1 d2,
    domain_compare d1 d2 = Eq <-> d1 = d2.
Proof.
  split; intros. eapply domain_compare_eq. assumption. rewrite H. eapply domain_compare_refl.
Qed.

Lemma domain_Gt_Lt_sym : forall d2 d1,
    domain_compare d1 d2 = Lt <->
      domain_compare d2 d1 = Gt.
Proof.
  induction d2; intros; split; intros.
  destruct d1; inversion H. simpl.
  eapply Nat.compare_nle_iff. eapply Nat.compare_nge_iff in H1. sfirstorder.
  destruct d1; inversion H. simpl. hauto use: Nat.compare_nle_iff, Nat.compare_nge_iff.
  destruct d1; inversion H. simpl. reflexivity.
  simpl. reflexivity. inversion H. destruct d1. simpl.
  strivial use: Gt_Lt_symm.
  reflexivity. destruct d1; inversion H. simpl in *.
  case_eq (domain_compare d2 d1); intros. rewrite domain_compare_eq_iff in H0.
  rewrite H0 in H. rewrite domain_compare_refl in H. strivial use: Gt_Lt_symm.
  2: reflexivity. case_eq (domain_compare d1 d2); intros.
  rewrite domain_compare_eq_iff in H2. subst. rewrite domain_compare_refl in H0. inversion H0.
  rewrite IHd2 in H2. rewrite H0 in H2. assumption.
  rewrite H2 in H. sfirstorder.
  destruct d1; inversion H. simpl.
  case_eq (domain_compare d2 d1); intros. rewrite domain_compare_eq_iff in H0.
  subst. erewrite domain_compare_refl in H1. rewrite domain_compare_refl.
  hfcrush use: Nat.compare_lt_iff, Nat.compare_gt_iff.
  rewrite H0 in H1. inversion H1. rewrite <- IHd2 in H0. rewrite H0. reflexivity.
Qed.
Lemma domain_compare_lt_trans : forall host1 host0 host2,
  domain_compare host0 host1 = Lt -> 
  domain_compare host1 host2 = Lt -> 
  domain_compare host0 host2 = Lt.
Proof.
  induction host1; intros; destruct host0, host2.
  simpl. simpl. rewrite <- nat_compare_lt.
  inversion H. inversion H0. rewrite <- nat_compare_lt in H3, H2. sfirstorder.
  inversion H.
  inversion H0.
  inversion H.
  inversion H.
  reflexivity.
  inversion H.
  inversion H0.
  inversion H.
  inversion H.
  reflexivity.
  simpl. inversion H. inversion H0.
  case_eq (domain_compare host0 host1);
    case_eq (domain_compare host1 host2); intros;
    try (rewrite domain_compare_eq_iff in H1);
    try (rewrite domain_compare_eq_iff in H4); subst.
  rewrite domain_compare_refl. rewrite domain_compare_refl in H3, H2. rewrite H2.
  rewrite Nat_as_OT.compare_lt_iff in H3, H2. rewrite Nat_as_OT.compare_lt_iff. sfirstorder.
  rewrite H1. reflexivity.
  rewrite H1 in H3. inversion H3.
  rewrite H4. reflexivity.
  assert (domain_compare host0 host2 = Lt). apply IHhost1; eauto. rewrite H5. reflexivity.
  rewrite H1 in H3. inversion H3.
  rewrite H4. reflexivity.
  rewrite H4 in H2. inversion H2. 
  rewrite H4 in H2. inversion H2. 
Qed.

Record Url :=
  mkUrl { protocol : Protocol ;
          host : Domain ;
          path : nat }.

Definition url_eqb u1 u2 :=
  protocol_eqb u1.(protocol) u2.(protocol) &&
    domain_eqb u1.(host) u2.(host) &&
    Nat.eqb u1.(path) u2.(path).

Definition url_eq u1 u2 :=
  url_eqb u1 u2 = true.

Lemma url_eq_refl : forall u,
    url_eq u u.
Proof.
  hauto use: domain_eqb_refl, Nat.eqb_refl, andb_true_intro unfold: url_eqb, path, protocol_eqb, protocol, host, url_eq.
Qed. 

Lemma eqb_refl : forall u,
    url_eqb u u = true.
Proof.
  sauto use: url_eq_refl unfold: url_eq.
Qed.

Lemma url_eq_symm : forall u1 u2,
    url_eq u1 u2 -> url_eq u2 u1.
Proof.
  unfold url_eq, url_eqb; intros; destruct u1, u2; simpl in *.
  eapply andb_prop in H. destruct H. eapply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H0. apply domain_eqb_eq in H1. eapply protocol_eqb_eq in H.
  sauto use: domain_eqb_refl, Nat.eqb_refl, protocol_eqb_refl, andb_true_intro.
Qed.

Lemma eqb_eq : forall (u1 u2 : Url),
    url_eqb u1 u2 = true <-> u1 = u2.
Proof.
  split; intros; destruct u1, u2; unfold eqb, url_eqb in *; simpl in *.
  eapply andb_prop in H. destruct H. eapply andb_prop in H. destruct H.
  apply Nat.eqb_eq in H0. apply domain_eqb_eq in H1. eapply protocol_eqb_eq in H.
  (* hammer proof: *) sfirstorder.
  inversion H.
  (* hammer proof: *) hauto use: protocol_eqb_refl, domain_eqb_refl, Nat.eqb_refl, andb_true_intro.
Qed.
  
Lemma url_eqb_trans : forall (u1 u2 u3 : Url),
    url_eqb u1 u2 = true -> url_eqb u2 u3 = true -> url_eqb u1 u3 = true.
Proof.
  intros.
  rewrite eqb_eq.
  rewrite eqb_eq in H, H0.
  sfirstorder.
Qed.

Lemma url_eq_trans : forall (u1 u2 u3 : Url),
    url_eq u1 u2 -> url_eq u2 u3 -> url_eq u1 u3.
Proof.
  unfold url_eq. eapply url_eqb_trans.
Qed.

Module Type URL.
  Parameter url : Type.
  Parameter eqb : url -> url -> bool.

  Axiom eqb_eq : forall (u1 u2 : url),
      eqb u1 u2 = true <-> u1 = u2.
  Axiom eqb_refl : forall (u : url),
      eqb u u = true.
  Axiom url_eqb_trans : forall (u1 u2 u3 : url),
    eqb u1 u2 = true -> eqb u2 u3 = true -> eqb u1 u3 = true.
End URL.

Module url <: URL.

  Definition url := Url.
  Definition eqb := url_eqb.
  
  Lemma eqb_eq : forall (u1 u2 : url),
      eqb u1 u2 = true <-> u1 = u2.
  Proof.
    split; intros; destruct u1, u2; unfold eqb, url_eqb in *; simpl in *.
    eapply andb_prop in H. destruct H. eapply andb_prop in H. destruct H.
    apply Nat.eqb_eq in H0. apply domain_eqb_eq in H1. eapply protocol_eqb_eq in H.
    (* hammer proof: *) sfirstorder.
    inversion H.
    (* hammer proof: *) hauto use: Nat.eqb_refl, domain_eqb_refl, protocol_eqb_refl unfold: andb.
  Qed.
  
  Lemma url_eqb_trans : forall (u1 u2 u3 : url),
    eqb u1 u2 = true -> eqb u2 u3 = true -> eqb u1 u3 = true.
  Proof.
    intros.
    rewrite eqb_eq.
    rewrite eqb_eq in H, H0.
    sfirstorder.
  Qed.
  Lemma eqb_refl : forall u,
      eqb u u = true.
  Proof.
    (* hammer proof: *) strivial use: eqb_eq unfold: url.
  Qed.
End url.

Module UrlLeibnizEq <: OrderedTypeWithLeibniz.
  Definition t := Url.
  Definition eq u1 u2 :=
    url_eqb u1 u2 = true.
  Definition eq_equiv :=
    Build_Equivalence url_eq url_eq_refl url_eq_symm url_eq_trans.
  Definition lt u1 u2 :=
    match u1.(protocol),u2.(protocol) with
    | ProtocolHTTP,ProtocolHTTPS => True
    | ProtocolHTTPS, ProtocolHTTP => False
    | _,_ => match (domain_compare u1.(host) u2.(host)), (Nat.compare u1.(path) u2.(path)) with
            | Lt,_
            | Eq,Lt => True
            | _,_ => False
            end
    end.

  Lemma url_lt_irrefl : forall u,
      ~ (lt u u).
  Proof.
    unfold lt, not; intros; destruct u, protocol0; simpl in *;
      (* hammer proof: *) hauto use: Nat.compare_refl, domain_compare_refl inv: comparison.
  Qed.

  Lemma url_lt_trans : forall u1 u2 u3, (* wow horrible *)
      lt u1 u2 -> lt u2 u3 -> lt u1 u3.
  Proof.
    unfold lt; destruct u1,u2,u3; destruct protocol0, protocol1, protocol2;
      simpl; intros; try trivial; try hauto.
    case_eq (domain_compare host0 host1); intros hostH; rewrite hostH in H. 3: sfirstorder.
    case_eq (domain_compare host1 host2); intros hostH2; rewrite hostH2 in H0. 3: sfirstorder. 
    eapply domain_compare_eq in hostH, hostH2. assert (host0 = host2) by sfirstorder.
    rewrite H1. rewrite domain_compare_refl.
    case_eq (path0 ?= path1)%nat; case_eq (path1 ?= path2)%nat; intros; simpl in *; try trivial; try hauto.
    assert ((path0 ?= path2)%nat = Lt).
    rewrite <- nat_compare_lt in H2, H3. rewrite <- nat_compare_lt. sfirstorder.
    rewrite H4. trivial.
    assert (domain_compare host0 host2 = Lt). sfirstorder use: domain_compare_eq.
    rewrite H1. trivial.
    case_eq (domain_compare host1 host2); intros hostH2; rewrite hostH2 in H0. 3: sfirstorder. 
    assert (domain_compare host0 host2 = Lt). sfirstorder use: domain_compare_eq.
    rewrite H1. trivial. 
    assert (domain_compare host0 host2 = Lt). eapply domain_compare_lt_trans; eauto.
    rewrite H1. trivial.

    (* rewrite <- nat_compare_lt in H, H0. rewrite <- nat_compare_lt. sfirstorder. *)
    (* rewrite H1. trivial. *)

    case_eq (domain_compare host0 host1); intros; rewrite H1 in H. 3: sfirstorder.
    case_eq (domain_compare host1 host2); intros hostH2; rewrite hostH2 in H0. 3: sfirstorder. 
    eapply domain_compare_eq in H1, hostH2. assert (host0 = host2) by sfirstorder.
    rewrite H2. rewrite domain_compare_refl.
    case_eq (path0 ?= path1)%nat;
      case_eq (path1 ?= path2)%nat; intros; simpl in *; try trivial; try hauto.
    assert ((path0 ?= path2)%nat = Lt). 
    rewrite <- nat_compare_lt in H4, H3. rewrite <- nat_compare_lt. sfirstorder.
    rewrite H5. trivial.
    assert (domain_compare host0 host2 = Lt). sfirstorder use: domain_compare_eq.
    rewrite H2. trivial. 

    case_eq (domain_compare host1 host2); intros hostH2; rewrite hostH2 in H0. 3: sfirstorder. 
    eapply domain_compare_eq in hostH2. assert (host1 = host2) by sfirstorder.
    rewrite <- H2. rewrite H1. trivial.
    hauto use: domain_compare_eq, domain_compare_refl, domain_compare_lt_trans inv: comparison.
  Qed.
  #[global]
  Declare Instance lt_strorder : StrictOrder lt.
  (* Definition lt_strorder := Build_StrictOrder lt url_lt_irrefl url_lt_trans. *)
  #[global]
  Declare Instance lt_compat : Proper (eq ==> eq ==> iff) lt.

  Definition compare u1 u2 :=
    match u1.(protocol), u2.(protocol) with
    | ProtocolHTTP, ProtocolHTTPS => Lt
    | ProtocolHTTPS, ProtocolHTTP => Gt
    | _,_ => match (domain_compare u1.(host) u2.(host)), (Nat.compare u1.(path) u2.(path)) with
            | Lt,_
            | Eq,Lt => Lt
            | Eq,Eq => Eq
            | Eq,Gt
            | Gt,_ => Gt
            end
    end.

  Lemma Eq_symm : forall x y,
      (x ?= y)%nat = Eq -> (y ?= x)%nat = Eq.
  Proof.
    sfirstorder use: Nat.compare_eq_iff.
  Qed.

  Lemma compare_spec : forall x y,
      CompSpec eq lt x y (compare x y).
  Proof.
    unfold CompSpec; intros; case_eq (compare x y); destruct x,y; unfold compare; intros; simpl in *.

    unfold eq, url_eqb.
    case_eq (protocol_eqb protocol0 protocol1); intro protH.
    (* hammer proof: *) 2: hauto.
    case_eq (domain_eqb host0 host1); intro hostH.
    2: hfcrush use: domain_eqb_eq, domain_compare_eq, not_true_iff_false,
          CompOpp_inj, protocol_eqb_eq inv: Protocol.
    case_eq (Nat.eqb path0 path1); intro pathH.
    (* hammer proof: *) 2: hecrush use: Nat.eqb_neq, Nat.compare_eq_iff inv: comparison.
    simpl. rewrite pathH, hostH.
    (* hammer proof: *) sauto lq: on.

    unfold lt; destruct protocol0, protocol1; simpl in *.
    sauto. sfirstorder. hauto lq: on. sauto q:on.

    unfold lt; destruct protocol0, protocol1; simpl in *. 2: hauto lq: on. 2: sfirstorder.
    case_eq (domain_compare host0 host1); case_eq (path0 ?= path1)%nat; intros; try hauto.
    eapply domain_compare_eq in H1. rewrite H1. rewrite H1 in H. rewrite domain_compare_refl in H.
    eapply Gt_Lt_symm in H0. rewrite H0. rewrite domain_compare_refl. sfirstorder.
    rewrite <- H1. 
    eapply domain_Gt_Lt_sym in H1. rewrite H1. 
    rewrite domain_Gt_Lt_sym in H1. rewrite H1. sfirstorder.
    rewrite <- domain_Gt_Lt_sym in H1. rewrite H1. sfirstorder.
    rewrite <- domain_Gt_Lt_sym in H1. rewrite H1. sfirstorder.

    case_eq (domain_compare host0 host1); case_eq (path0 ?= path1)%nat; intros; try hauto.
    eapply domain_compare_eq_iff in H1. rewrite H1. eapply Gt_Lt_symm in H0. rewrite H0. 
    rewrite domain_compare_refl. sfirstorder.
    eapply domain_Gt_Lt_sym in H1. rewrite H1. sfirstorder.
    rewrite <- domain_Gt_Lt_sym in H1. rewrite H1. sfirstorder.
    rewrite Gt_Lt_symm in H0. rewrite <- domain_Gt_Lt_sym in H1. rewrite H0, H1. sfirstorder.
  Qed.
  
  Lemma eq_dec : forall u1 u2 : Url,
      {eq u1 u2} + {~ eq u1 u2}.
  Proof.
    destruct u1, u2; unfold eq, url_eqb; simpl.

    case_eq (protocol_eqb protocol0 protocol1); intro protH.
    case_eq (domain_eqb host0 host1); intro hostH.
    case_eq (Nat.eqb path0 path1); intro pathH.

    (* hammer proof: *) sfirstorder.
    (* hammer proof: *) sfirstorder.
    (* hammer proof: *) sfirstorder.
    (* hammer proof: *) sfirstorder.
  Qed.

  Lemma eq_leibniz : forall u1 u2, eq u1 u2 -> u1 = u2.
  Proof.
    unfold eq. intros. strivial use: eqb_eq.
  Qed.
End UrlLeibnizEq.

Module UrlSets.
  Module S := MakeWithLeibniz UrlLeibnizEq. 
  Module SAx := MSetEqProperties.EqProperties S.

  Lemma subset_transitivity : forall (s1 s2 s3 : S.t),
      S.subset s1 s2 = true /\ S.subset s2 s3 = true -> S.subset s1 s3 = true.
  Proof.
    intros. destruct H. eapply SAx.subset_trans; eassumption.
  Qed.
  
  Lemma subset_union_subset : forall (s1 s2 s3 : S.t),
      S.subset s1 s3 = true /\ S.subset s2 s3 = true -> S.subset (S.union s1 s2) s3 = true.
  Proof.
    intros. destruct H. eapply SAx.union_subset_3; eauto.
  Qed.

  Lemma subset_empty_empty : forall s,
      S.subset s S.empty = true ->
      S.Empty s.
  Proof.
    intros. induction s. sauto.
  Qed.
End UrlSets.


