Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.
Require Import BrowserInfoFlow.CookieImpl.
Require Import BrowserInfoFlow.Events.
Require Import BrowserInfoFlow.Invariant.
Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.HOPS.
Require Import BrowserInfoFlow.GeneralEventHandlers.

From Hammer Require Import Hammer.

Ltac unfold_interface :=
  unfold B.update_most_recent_rq_cookies, B.most_recent_urq, B.add_to_jar, B.cookie_mapping_for_origin in *.

Program Definition rp_cookie_handler (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.inbox b) with
  | Some rp => let d := RP.get_rp_domain rp in
              let scs := RP.get_rp_cookies rp in 
              match (forallb (fun sc => C.is_valid_setcookie (RP.get_rp_url rp) sc) scs) with
              | true =>
                  (update_dom_with_response
                     (B.add_to_jar b
                        (map
                           (fun rpc => (d, rpc)) scs),
                       (E.EvHTTPSetCookie d scs) :: t))
              | _ => None
              end
  | _ => None
  end.
Next Obligation.
  prelude.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.

Program Definition rq_cookie_insert' (v : valid) : option valid :=
  let b := fst v in
  let t := snd v in
  match t,(B.most_recent_urq b) with
  | (E.EvRequest ur__e o) :: t', Some ur__o =>
      let cookie_mapping := B.cookie_mapping_for_origin b (RQ.destination ur__e) in
      match (RequestRecord.ur_eqb ur__o ur__e) with
      | true => 
          match (B.update_most_recent_rq_cookies b cookie_mapping) with
          | Some b' => Some (b',
                          (E.EvRequest (RQ.populate_cookies ur__e cookie_mapping) o) :: t')
          | _ => None
          end
      | _ => None
      end
  | _,_ => None
  end.
Next Obligation.
  prelude; unfold_interface. 
  - repeat split.
    -- hauto b: on.
    -- hauto b: on.
  - unfold RequestRecord.ur_eqb in Heq_anonymous1. eapply eq_sym in Heq_anonymous1. eapply andb_true_iff in Heq_anonymous1.
    destruct Heq_anonymous1. eapply RequestRecord.eqb_eq in H0. eapply RequestRecord.initiator_eqb_eq in H. 
    rewrite <- Heq_t in *. clear Heq_t;
      repeat (match goal with | [ H : Forall _ (_ :: _) |- _ ] => eapply Forall_cons_iff in H; destruct H end);
      repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- destruct b, outbox; inversion Heq_anonymous. simpl in *.
       eapply Forall_cons. destruct u; inversion Heq_anonymous0; subst; simpl in *.
       sfirstorder.
       sauto lq: on.
    -- hauto lq: on.
  - eapply Forall_cons. trivial. rewrite <- Heq_t in *.
    repeat (match goal with | [ H : Forall _ (_ :: _) |- _ ] => eapply Forall_cons_iff in H; destruct H end).
    sfirstorder.
Qed.

Program Definition dom_rq_cookie_handler (v : valid) : option valid :=
  match (make_unloaded_request v) with
  | Some v' =>
      rq_cookie_insert' v
  | _ => None
  end.

Program Definition user_rq_cookie_handler (urq : RQ.unfilled_request) (v : valid) : option valid :=
  match (user_request urq v) with
  | Some v' =>
      rq_cookie_insert' v
  | _ => None
  end.

Program Definition js_set_cookie_handler (v : valid)
  (new_cookies : list C.set_cookie) (i : RQ.initiator) : option valid :=
  let b := fst v in
  let t := snd v in
  match (B.initiator_window_url b i) with
  | Some u =>
      let d := u.(host) in
      match (forallb (fun sc => C.is_valid_setcookie u sc) new_cookies) with
      | true =>
          (update_dom_with_response
             (B.add_to_jar b
                (map
                   (fun rpc => (d, rpc)) new_cookies),
               (E.EvHTTPSetCookie d new_cookies) :: t))
      | _ => None
      end
  | _ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.

Program Definition js_get_cookies_handler (v : valid) (i : RQ.initiator) : option valid :=
  let b := fst v in
  let t := snd v in
  match (B.initiator_window_url b i) with
  | Some u => 
      match (B.dom_label_initiator b i) with 
      | Some l =>
          let all_cookies := B.find_cookies b u in
          let cookies := filter (fun sc => match (C.sc_http_only sc) with
                                        | true =>
                                            (L.can_flow l (L.no_scripts u))
                                        | _ => true
                                        end) all_cookies in
          Some (b, (E.EvJSGetCookie cookies l) :: t)
      | _ => None
      end
  | _ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - apply Forall_cons.
    2: sfirstorder.
    induction (B.find_cookies b u). apply Forall_nil.
    assert (a :: l1 = [a] ++ l1) by sfirstorder. rewrite H. clear H. erewrite filter_app. simpl.
    case_eq ((if C.sc_http_only a as anonymous' return (anonymous' = C.sc_http_only a -> bool)
              then fun _ : true = C.sc_http_only a => L.can_flow l (L.no_scripts u)
              else fun _ : false = C.sc_http_only a => true) eq_refl); intros.
    simpl. eapply Forall_cons.
    case_eq (CookieRecord.sc_http_only a); intros. unfold C.sc_http_only in H.
    rewrite H0 in H. unfold L.can_flow in H. unfold LabelRecord.flowb in H.
    eapply andb_true_iff in H. destruct H. unfold L.no_scripts in H1.
    apply UrlSets.subset_empty_empty;
      sfirstorder.
    sfirstorder. 
    sfirstorder. 
    sfirstorder. 
Qed.

Program Definition js_get_cookie_handler (v : valid) (name : C.cookie_name) (i : RQ.initiator) : option valid :=
  let b := fst v in
  let t := snd v in
  match (B.initiator_window_url b i) with
  | Some u => 
      match (B.dom_label_initiator b i) with 
      | Some l =>
          match (B.find_cookie b name) with
          | Some sc => match (C.sc_http_only sc) with
                      | false => Some (b, (E.EvJSGetCookie [sc] l) :: t)
                      | true => 
                          match (L.can_flow l (L.no_scripts (B.origin b))) with
                          | true => Some (b, (E.EvJSGetCookie [sc] l) :: t)
                          | false => None
                          end
                      end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - simpl in *. apply Forall_cons.
    2: sfirstorder.
    apply Forall_cons. unfold C.sc_http_only in Heq_anonymous. rewrite <- Heq_anonymous. trivial.
    sfirstorder.
Qed.
Next Obligation.
  prelude; unfold_interface.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - apply Forall_cons.
    2: sfirstorder.
    apply Forall_cons. unfold C.sc_http_only in Heq_anonymous3. rewrite <- Heq_anonymous3.
    unfold L.can_flow in Heq_anonymous. unfold LabelRecord.flowb in Heq_anonymous.
    apply eq_sym in Heq_anonymous. eapply andb_true_iff in Heq_anonymous. destruct Heq_anonymous.
    unfold L.no_scripts in H0. simpl in H0. apply UrlSets.subset_empty_empty.
    sfirstorder.
    sfirstorder.
Qed.
Fail Next Obligation.
