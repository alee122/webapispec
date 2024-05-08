Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.

Require Import BrowserInfoFlow.GeneralSigs.
Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.CookieRecord.
Require BrowserInfoFlow.LabelRecord.
Require BrowserInfoFlow.ResponseRecord.
Require BrowserInfoFlow.RequestRecord.
Require BrowserInfoFlow.BrowserRecord.

From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.

Module RP <: RESPONSE(url).
  Import ResponseRecord.
  Module S := UrlSets.S.
  Definition response := response.
  Definition response_content := response_content.
  Definition cookies := list SetCookie.
  Definition mkResponse := ResponseRecord.mkResponse.
  Definition response_url := ResponseRecord.response_url.
  Definition rp_content := ResponseRecord.content.
End RP.

Module RQ <: REQUEST(url).
  Import RequestRecord.
  Definition request := request.
  Definition initiator := Initiator.
  Definition unfilled_request := unfilled_request.
  Definition urq_init (urq : unfilled_request) := urq.(initiator_rq).
  Definition initiator_object := initiator_object.
  Definition u_rq := u_rq.
  Definition request_url := url__rq.
  Definition request_origin := origin.
  Definition is_parent := is_parent.
  Definition assign_origin := assign_origin.
  Definition eqb := eqb.
  Definition eqb_eq := eqb_eq.  
End RQ.

Module B <: BROWSER(url).
  Import BrowserRecord.
  Import DomRecord.
  Module RP := RP.
  Module RQ := RQ.
  Definition browser := browser_state.
  Definition unfilled := RQ.unfilled_request.
  Definition reduce_outbox := reduce_outbox.
  Definition drop_last b := drop_last (b.(outbox)).
  Definition last_op b := last_op (b.(outbox)).
  Definition response_content := RP.response_content.
  Definition window := Window.
  Definition send_out (b : browser) (ur : unfilled) := add_to_outbox b ur.
  Definition inbox_update b i := mkBrowser (origin b) (dom b) (sw b) (b.(browser_cache)) b.(outbox) i b.(jar).
  Definition inbox b := b.(inbox).
  Definition outbox b := b.(outbox).
  Definition dom b := b.(dom).
  Definition update_dom (b : browser) (urq : unfilled) (rpc : response_content) :=
    match (update_dom b (RQ.urq_init urq) rpc) with
    | Some dom' => Some (mkBrowser (origin b) dom' (sw b) (b.(browser_cache)) (outbox b) (inbox b) (b.(jar)))
    | None => None
    end.
  Definition get_unfilled_request b :=
    (wmake_unfilled_request_object (dom b)).
  Definition mark_dom_object_requested (b : browser) (ur : unfilled) :=
    match (wupdate_loadedness (RQ.urq_init ur) (dom b)) with
    | Some dom' => Some (mkBrowser (origin b) dom' (sw b) (b.(browser_cache)) (ur :: (outbox b)) (inbox b) b.(jar))
    | _ => None
    end.
  Definition origin_of (b : browser) (i : RQ.initiator) := worigin_of i (dom b) (Some (origin b)).
  (* Parameter redirect_window : browser -> RQ.initiator -> Url -> browser. *)
  Definition redirect_window (b : browser) i u :=
    match (redirect_window (dom b) i u) with
    | Some dom' => Some (mkBrowser (origin b) dom' (sw b) (b.(browser_cache)) (outbox b) (inbox b) b.(jar))
    | _ => None
    end.
  Definition redirect_frame (b : browser) i u :=
    match (redirect_frame (dom b) i u) with
    | Some dom' => Some (mkBrowser (origin b) dom' (sw b) (b.(browser_cache)) (outbox b) (inbox b) b.(jar))
    | _ => None
    end.
  Definition is_parent := RQ.is_parent.
  Definition update_in_out_box (b : browser) outbox' inbox' :=
    (mkBrowser (origin b) (dom b) (sw b) (b.(browser_cache)) outbox' inbox' b.(jar)).
End B.
