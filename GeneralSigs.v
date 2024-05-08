From Coq Require Import MSets Arith.
Require Import Coq.MSets.MSetEqProperties.
Require Import BrowserInfoFlow.Url.
Require BrowserInfoFlow.ResponseRecord.
Require BrowserInfoFlow.RequestRecord.

Module Type RESPONSE (u : URL).
  Import ResponseRecord.
  Module S := UrlSets.S.
  Parameter response : Type.
  Parameter response_content : Type.
  Parameter cookies : Type.
  Parameter mkResponse : u.url -> response_content -> cookies -> response.
  Parameter response_url : response -> u.url.
  Parameter rp_content : response -> response_content.
End RESPONSE.

Module Type REQUEST (u : URL).
  Parameter request : Type.
  Parameter initiator : Type.
  Parameter unfilled_request : Type.
  Parameter eqb : request -> request -> bool.
  Parameter u_rq : unfilled_request -> request.
  Parameter urq_init : unfilled_request -> initiator.
  Parameter request_url : request -> u.url.
  Parameter request_origin : request -> option u.url.
  Parameter initiator_object : initiator -> initiator.
  Parameter is_parent : initiator -> initiator -> bool.
  Parameter assign_origin : unfilled_request ->  option u.url -> unfilled_request.
  Axiom eqb_eq : forall (rq1 rq2 : request), eqb rq1 rq2 = true <-> rq1 = rq2.
End REQUEST.

Module Type BROWSER (u : URL).
  Declare Module RP : RESPONSE(u).
  Declare Module RQ : REQUEST(u).
  Parameter browser : Type.
  Parameter unfilled : Type.
  Parameter window : Type.
  Parameter response_content : Type.
  Parameter send_out : browser -> unfilled -> browser.
  Parameter reduce_outbox : browser -> (browser * (option unfilled)).
  Parameter drop_last : browser -> option (list unfilled).
  Parameter last_op : browser -> option unfilled.
  Parameter inbox_update : browser -> (option RP.response) -> browser.
  Parameter outbox : browser -> list unfilled.
  Parameter inbox : browser -> option RP.response.
  Parameter dom : browser -> window.
  Parameter update_dom : browser -> unfilled -> response_content -> option browser.
  Parameter get_unfilled_request : browser -> option unfilled.
  Parameter mark_dom_object_requested : browser -> unfilled -> option browser.
  Parameter origin_of : browser -> RQ.initiator -> option Url.
  Parameter is_parent : RQ.initiator -> RQ.initiator -> bool.
  Parameter redirect_window : browser -> RQ.initiator -> Url -> option browser.
  Parameter redirect_frame : browser -> RQ.initiator -> Url -> option browser.
  Parameter update_in_out_box : browser -> list RQ.unfilled_request -> option RP.response -> browser.
End BROWSER.
