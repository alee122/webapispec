Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.HOPS.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

From Hammer Require Import Hammer Tactics.

Inductive CookieName :=
| NoPrefix (cn_npn:nat)
| Secure (cn_sn:nat)
| Host (cn_hn:nat)
.
Definition cookie_name_eqb cn1 cn2 :=
  match cn1,cn2 with
  | NoPrefix n1, NoPrefix n2 
  | Secure n1, Secure n2
  | Host n1, Host n2 => Nat.eqb n1 n2
  | _,_ => false
  end.
Lemma cookie_name_eqb_refl : forall cn,
    cookie_name_eqb cn cn = true.
Proof. sauto use: Nat.eqb_refl. Qed.
Lemma cookie_name_eqb_eq : forall cn1 cn2,
    cookie_name_eqb cn1 cn2 = true <-> cn1 = cn2.
Proof.
  hauto lq: on use: cookie_name_eqb_refl, Nat.eqb_eq, Bool.diff_false_true unfold: cookie_name_eqb.
Qed.

Record CookieMapping := mkCookieMapping {
  cm_name  : CookieName;
  cm_value : nat;
}.
Definition cm_eqb cm1 cm2 :=
  (cookie_name_eqb cm1.(cm_name) cm2.(cm_name)) &&
    (cm1.(cm_value) =? cm2.(cm_value)).
Lemma cm_eqb_refl : forall cm,
    cm_eqb cm cm = true.
Proof.
  destruct cm; unfold cm_eqb; simpl.
  sauto use: cookie_name_eqb_refl, Nat.eqb_refl, andb_true_intro.
Qed.
Lemma cm_eqb_eq : forall cm1 cm2,
    cm_eqb cm1 cm2 = true <-> cm1 = cm2.
Proof.
  split. destruct cm1, cm2; unfold cm_eqb; simpl; intros.
  eapply andb_true_iff in H. destruct H.
  hfcrush use: Nat.eqb_eq, cookie_name_eqb_eq.
  intros. subst. sauto use: cm_eqb_refl.
Qed.

Inductive SameSite :=
| SSStrict
| SSLax
| SSNone
.
Definition ss_eqb ss1 ss2 :=
  match ss1,ss2 with
  | SSStrict,SSStrict
  | SSLax,SSLax
  | SSNone,SSNone => true
  | _,_ => false
  end.
Lemma ss_eqb_refl : forall ss,
    ss_eqb ss ss = true.
Proof. sauto lq: on. Qed.
Lemma ss_eqb_eq : forall ss1 ss2,
    ss_eqb ss1 ss2 = true <-> ss1 = ss2.
Proof. sauto lq: on. Qed.

Record SetCookie := mkSetCookie {
  sc_name       : CookieName;
  sc_value      : nat;
  sc_domain     : option Domain; (* make option (new domain ind) *)
  sc_path       : nat;
  sc_secure     : bool;
  sc_http_only  : bool;
  sc_same_site  : SameSite;
}.

Definition sc_eqb (sc1 sc2 : SetCookie) : bool:=
  cookie_name_eqb sc1.(sc_name) sc2.(sc_name) &&
  ss_eqb sc1.(sc_same_site) sc2.(sc_same_site) &&
    (sc1.(sc_value) =? sc2.(sc_value)) &&
    (op_eqb domain_eqb sc1.(sc_domain) sc2.(sc_domain)) &&
    (sc1.(sc_path) =? sc2.(sc_path)) && 
    (Bool.eqb sc1.(sc_secure) sc2.(sc_secure)) &&
    (Bool.eqb sc1.(sc_http_only) sc2.(sc_http_only)).
Lemma sc_eqb_refl : forall sc,
    sc_eqb sc sc = true.
Proof. unfold sc_eqb; destruct sc; simpl. repeat (apply andb_true_iff; split);
         try (sauto use: Nat.eqb_refl, cookie_name_eqb_refl, ss_eqb_refl lq: on).
       apply eqb_refl_op_eqb_refl. eapply domain_eqb_refl.
Qed.

Lemma sc_eqb_eq : forall sc1 sc2,
    sc_eqb sc1 sc2 = true <-> sc1 = sc2.
Proof.
  split. destruct sc1, sc2; unfold sc_eqb; simpl. intros.
  repeat (match goal with
          | [H : _ && _ = true |- _ ] => eapply andb_true_iff in H; destruct H
          end).
  rewrite eqb_eq_op_eqb_eq in H3. 2: apply domain_eqb_eq.
  hauto lq: on use: eqb_true_iff, cookie_name_eqb_eq, ss_eqb_eq, Nat.eqb_eq.
  scongruence use: sc_eqb_refl.
Qed.

Definition Cookie := list CookieMapping. (* goes in request headers *)
Definition ResponseCookies := list SetCookie.
Definition CookieJar := list (Domain * SetCookie). (* stored in browser *)
(* domain is registering domain (Initiator domain or response domain) *)
 
Definition check_same_site (u:Url) (sc:SetCookie) : bool :=
  match (sc_same_site sc) with
  (* if a cookie is same-site=none it must have the secure attr *)
  | SSNone => (protocol_eqb u.(protocol) ProtocolHTTPS) && sc.(sc_secure)
  | _ => true
  end.

Definition check_cookie_domain_set (u:Url) (sc:SetCookie) : bool :=
  match (sc_domain sc) with
  | None => true
  | Some d => sub_or_eq_domain u.(host) d
  end.

Definition is_valid_setcookie (u:Url) (sc:SetCookie) : bool :=
  check_same_site u sc &&
  match (sc_name sc) with
  | Secure n =>  (* must be set by a secure origin with the secure attribute *)
    (sc_secure sc) && (protocol_eqb (protocol u) ProtocolHTTPS) &&
    (* domain must be None or eq or a parent *)
    check_cookie_domain_set u sc
  | Host n =>
    (* must be set by a secure origin with the secure attribute *)
    (sc_secure sc) && (protocol_eqb (protocol u) ProtocolHTTPS) &&
    (* (* MUST contain a "Path" attribute with a value of "/" *) *)
    (* /\ (sc_path sc) = slash /\ *)
    (* match (url_path u) with *)
    (* | url_path_res ru => ru = slash *)
    (* | _ => False *)
    (* end *)
    (* domain must be "" *)
      match (sc_domain sc) with
      | None => true
      | _ => false
      end
  | NoPrefix n =>
      (if (sc_secure sc) then (protocol_eqb (protocol u) ProtocolHTTPS) else true) &&
        (* set with secure mist be https, domain must be None or eq or a parent *)
        check_cookie_domain_set u sc
  end.
