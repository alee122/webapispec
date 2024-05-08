Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.

Require Import BrowserInfoFlow.SWSigs.
Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.CookieRecord.
Require Import BrowserInfoFlow.DomRecord.
Require BrowserInfoFlow.LabelRecord.
Require BrowserInfoFlow.ResponseRecord.
Require BrowserInfoFlow.RequestRecord.
Require BrowserInfoFlow.BrowserRecord.

From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.
Module L <: LABEL(url).
  Module S := UrlSets.S.
  Definition label := LabelRecord.label.
  Definition eqb := LabelRecord.eqb.
  Definition refl := LabelRecord.refl.
  Definition flowb := LabelRecord.flowb.
  Definition can_flow := LabelRecord.can_flow.
  Definition flowb_can_flow := LabelRecord.flowb_can_flow.
  Definition flow_transitivity := LabelRecord.flow_transitivity.
  Definition flow_reflexivity := LabelRecord.flow_reflexivity.
  Definition origin_url := LabelRecord.origin_url.
  Definition scripts := LabelRecord.scripts.
  Definition mkLabel := LabelRecord.mkLabel.
End L.
Definition label := L.label.

Module RP <: RESPONSE(url).
  Module S := UrlSets.S.
  (* Maybe later make "SW_update" that leaves all other fields *)
  Definition response := ResponseRecord.response.
  Definition cookies := list SetCookie.
  Definition eqb := ResponseRecord.eqb.
  Definition refl := ResponseRecord.refl.
  Definition eqb_eq := ResponseRecord.eqb_eq.
  Definition response_url := ResponseRecord.response_url.
  Definition content := ResponseRecord.content.
  Definition mkResponse := ResponseRecord.mkResponse.
End RP.
Definition response := RP.response.

Module RQ <: REQUEST(url).
  Import RequestRecord.
  Definition request := request.
  Definition eqb := eqb.
  Definition refl := eqb_refl.
  Definition eqb_eq := eqb_eq.
  Definition request_url := url__rq.
  Definition unfilled_request := unfilled_request.
  Definition u_rq := u_rq.
  Definition u_init := initiator_rq.
  Definition initiator := Initiator.
End RQ.
Definition request := RQ.request.


Module B <: BROWSER(url).
  Import BrowserRecord.
  Module RP := RP.
  Module RQ := RQ.
  Module L := L.
  Definition browser := browser_state.
  Definition cache := cache. 
  Definition unfilled := RQ.unfilled_request.
  Definition cache_lookup := cache_lookup.
  Definition cache_member := cache_member.
  Definition mkBrowser := mkBrowser.
  Definition dom_label (b : browser) := L.mkLabel b.(origin) (dom_label b.(dom)).
  Definition cache_update b p := mkBrowser (origin b) (dom b) (sw b) (p :: b.(browser_cache)) b.(outbox) b.(inbox) b.(jar).
  Definition inbox_update b i := mkBrowser (origin b) (dom b) (sw b) (b.(browser_cache)) b.(outbox) i b.(jar).
  Definition update_sw b sw' := mkBrowser b.(origin) b.(dom) sw' b.(browser_cache) b.(outbox) b.(inbox) b.(jar).
  Definition update_cache (b : browser) c' := mkBrowser b.(origin) b.(dom) b.(sw) c' b.(outbox) b.(inbox) b.(jar).
  Definition curr_sw b := b.(sw).
  Definition curr_dom b := b.(dom).
  Definition curr_cache b := b.(browser_cache).
  Definition reduce_outbox := reduce_outbox.
  Definition inbox b := b.(inbox).
  Definition next_rq b :=
    match b.(outbox) with
    | [] => None
    | urq :: _ => Some (RQ.u_rq urq)
    end.
  Definition outbox b := b.(outbox).
End B.
