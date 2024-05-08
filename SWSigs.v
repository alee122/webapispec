From Coq Require Import MSets Arith.
Require Import Coq.MSets.MSetEqProperties.
Require Import BrowserInfoFlow.Url.
Require BrowserInfoFlow.ResponseRecord.

Module Type RESPONSE (u : URL).
  Import ResponseRecord.
  Parameter response : Type.
  Parameter response_url : response -> u.url.
  Parameter cookies : Type.
  Parameter mkResponse : u.url -> response_content -> cookies -> response.
  Parameter content : response -> response_content.
  Parameter eqb : response -> response -> bool.
  Axiom refl : forall rp, eqb rp rp = true.
  Axiom eqb_eq : forall rp1 rp2,
      eqb rp1 rp2 = true <-> rp1 = rp2.
End RESPONSE.

Module Type REQUEST (u : URL).
  Parameter request : Type.
  Parameter unfilled_request : Type.
  Parameter initiator : Type.
  Parameter eqb : request -> request -> bool.
  Parameter u_rq : unfilled_request -> request.
  Parameter u_init : unfilled_request -> initiator.
  Parameter request_url : request -> u.url.
  Axiom refl : forall rq,
      eqb rq rq = true.
  Axiom eqb_eq : forall rq1 rq2,
      eqb rq1 rq2 = true <-> rq1 = rq2.
End REQUEST.

Module Type LABEL (u : URL).
  Module S := UrlSets.S.
  Parameter label : Type.
  Parameter eqb : label -> label -> bool.
  Axiom refl : forall l, eqb l l = true.

  Parameter origin_url : label -> u.url.
  Parameter scripts : label -> S.t.
  Parameter mkLabel : u.url -> S.t -> label.

  Parameter flowb : label -> label -> bool.
  Parameter can_flow : label -> label -> Prop.
  Axiom flowb_can_flow : forall (l1 l2 : label),
      flowb l1 l2 = true <-> can_flow l1 l2.
  
  Axiom flow_transitivity : forall (l1 l2 l3 : label),
      can_flow l1 l2 /\ can_flow l2 l3 -> can_flow l1 l3.
  Axiom flow_reflexivity : forall (l : label),
      can_flow l l.
End LABEL.

Module Type BROWSER (u : URL).
  Declare Module RP : RESPONSE(u).
  Declare Module RQ : REQUEST(u).
  Declare Module L : LABEL(u).
  Parameter browser : Type.
  Parameter cache : Type.
  Parameter unfilled : Type.
  (* Parameter cache_lookup : browser -> RQ.request -> option (RQ.request * RP.response)%type.*)
  Parameter cache_lookup : RQ.request -> cache -> option RP.response.
  Parameter cache_update : browser -> (RQ.request * RP.response) -> browser.
  (* Parameter cache_member : browser -> (RQ.request * RP.response)%type -> Prop.*)
  Parameter cache_member : (RQ.request * RP.response)%type -> cache -> Prop.
  (* Parameter mkBrowser : L.label -> L.label -> cache -> browser. *)
  Parameter inbox_update : browser -> (option RP.response) -> browser.
  Parameter dom_label : browser -> L.label.
  Parameter update_sw : browser -> L.label -> browser.
  Parameter update_cache : browser -> cache -> browser.
  Parameter curr_sw : browser -> L.label.
  Parameter curr_cache : browser -> cache.
  Parameter reduce_outbox : browser -> (browser * (option unfilled)).
  Parameter outbox : browser -> list unfilled.
  Parameter next_rq : browser -> option RQ.request.
  Parameter inbox : browser -> option RP.response.
End BROWSER.
