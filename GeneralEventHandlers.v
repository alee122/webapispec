Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.

Require Import BrowserInfoFlow.GeneralImpl.
Require Import BrowserInfoFlow.Url.

Require Import BrowserInfoFlow.Invariant.

From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.

Ltac unfold_interface :=
  unfold B.drop_last, B.last_op, B.inbox, B.update_dom, B.update_in_out_box,
    B.mark_dom_object_requested, B.outbox, B.redirect_frame, B.redirect_window
    in *.

(* if inbox populated, consume inbox and last outbox and update DOM as needed *)
Program Definition update_dom_with_response (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.drop_last b),(B.last_op b),(B.inbox b) with
  | Some outbox', Some urq, Some rp =>
      if (url.eqb (RQ.request_url (RQ.u_rq urq)) (RP.response_url rp))
      then
        match (B.update_dom (B.update_in_out_box b outbox' None) urq (RP.rp_content rp)) with
        | Some b' => Some (b', t)
        | None => None
        end
      else None
  | _,_,_ => None
  end.
Next Obligation. 
  prelude; unfold_interface.
  - split; intros.
    -- hauto lq: on.
    -- hauto b: on.
  - repeat split; intros.
    -- sfirstorder.
    -- sfirstorder.
    -- destruct b; simpl in *. destruct outbox. inversion Heq_anonymous2.
       erewrite BrowserRecord.drop_last_removelast in Heq_anonymous2 by sfirstorder.
       inversion Heq_anonymous2.
       destruct (BrowserRecord.update_dom
                      {|
                        BrowserRecord.origin := origin;
                        BrowserRecord.dom := dom;
                        BrowserRecord.sw := sw;
                        BrowserRecord.browser_cache := browser_cache;
                        BrowserRecord.outbox := outbox';
                        BrowserRecord.inbox := None;
                        BrowserRecord.jar := jar
                      |} (B.RQ.urq_init urq) (RP.rp_content rp)); inversion Heq_anonymous.
       destruct b'; subst. simpl. 
       simpl. eapply Forall_hold_zip_drop'. eauto.
       sfirstorder.
    -- destruct b; simpl in *. destruct outbox. inversion Heq_anonymous2. 
       erewrite BrowserRecord.drop_last_removelast in Heq_anonymous2 by sfirstorder.
       assert ((length (removelast (u :: outbox))) <= (length (u :: outbox)))%nat by eapply BrowserRecord.removelast_leq_len.
       hauto b: on.
  - sfirstorder.
Qed.

(* search DOM for NotLoaded resource, update requests list and change to requested *)
Program Definition make_unloaded_request (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.get_unfilled_request b) with
  | Some ur =>
      match (B.mark_dom_object_requested b ur) with
      | Some b' => Some (b', (E.EvRequest ur (RQ.request_origin (RQ.u_rq ur))) :: t)
      | _ => None
      end
  | _ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - intros. destruct (BrowserRecord.wupdate_loadedness (B.RQ.urq_init ur) (B.dom b)); inversion Heq_anonymous; split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- hauto b: on.
    -- destruct (BrowserRecord.wupdate_loadedness (B.RQ.urq_init ur) (B.dom b)); inversion Heq_anonymous; simpl.
       unfold B.outbox.
       sfirstorder.
  - sfirstorder.
Qed.

Program Definition respond_to_request (content : RP.response_content) (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  (* let (b', orq) := B.reduce_outbox b in *)
  match (B.reduce_outbox b) with
  | (_, Some urq) => (* don't actually get rid of the request, that's when handling response! *)
      let rp := RP.mkResponse (RQ.request_url (RQ.u_rq urq)) content [] in
      Some (B.inbox_update b (Some rp),
        E.EvResponse rp :: t)
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

(* check that initiator is window? then add to request list? something about changing window url? *)
Program Definition user_request (urq : B.unfilled) (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (RQ.initiator_object (RQ.urq_init urq)) with
  (* why are any new options redundant???*)
  | WindowLocation =>
      Some (B.send_out b urq,
          E.EvRequest urq (RQ.request_origin (RQ.u_rq urq)) :: t)
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

(* check that the script initiator's origin is also the origin of frame loc, then update the url in the frame and whether it's loaded *)
Program Definition handle_js_navigate_frame (script_loc frame_loc : RQ.initiator) (new_u : Url) (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.origin_of b script_loc),(B.origin_of b frame_loc) with
  | Some sorigin, Some forigin =>
      match (B.is_parent script_loc frame_loc) with
      | true =>
          match (B.redirect_frame b frame_loc new_u) with
          | Some b' => Some (b', E.EvJSNavigate script_loc frame_loc :: t) 
          | _ => None
          end
      | false => None
      end
  | _,_ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - destruct (BrowserRecord.redirect_frame (B.dom b) frame_loc new_u) in Heq_anonymous; inversion Heq_anonymous; simpl; split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- destruct (BrowserRecord.redirect_frame (B.dom b) frame_loc new_u) in Heq_anonymous;
         inversion Heq_anonymous.
       sfirstorder.
    -- destruct (BrowserRecord.redirect_frame (B.dom b) frame_loc new_u) in Heq_anonymous;
         inversion Heq_anonymous.
       sfirstorder.
  - sfirstorder.
Qed.

Program Definition handle_js_navigate_window (script_loc window_loc : RQ.initiator) (new_u : Url) (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.origin_of b script_loc),(B.origin_of b window_loc) with
  | Some sorigin, Some forigin =>
      match (B.is_parent script_loc window_loc) with
      | true =>
          match (B.redirect_window b window_loc new_u) with
          | Some b' => Some (b', E.EvJSNavigate script_loc window_loc :: t) 
          | _ => None
          end
      | false => None
      end
  | _,_ => None
  end.
Next Obligation.
  prelude; unfold_interface.
  - destruct (BrowserRecord.redirect_window (B.dom b) window_loc new_u) in Heq_anonymous; inversion Heq_anonymous; simpl; split.
    -- sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- destruct (BrowserRecord.redirect_window (B.dom b) window_loc new_u) in Heq_anonymous;
         inversion Heq_anonymous; simpl.
       sfirstorder.
    -- destruct (BrowserRecord.redirect_window (B.dom b) window_loc new_u) in Heq_anonymous;
         inversion Heq_anonymous; simpl.
       sfirstorder.
  - sfirstorder.
Qed.
