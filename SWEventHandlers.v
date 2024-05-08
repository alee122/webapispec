Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.

Require Import BrowserInfoFlow.SWImpl.
Require Import BrowserInfoFlow.Url.

Require Import BrowserInfoFlow.Invariant.

From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.

Program Definition load_and_activate_sw (sw__new : label) (s : valid) (* initiator *) : option valid := 
  let b := fst s in
  let t := snd s in
  match (L.flowb (B.curr_sw b) sw__new) with
  | true => Some (B.update_sw b sw__new,
               E.EvLoadSW sw__new :: t)
  | _ => Some (B.update_sw (B.update_cache b []) sw__new,
            E.EvLoadSW sw__new :: t)
  end.
Next Obligation.
  prelude.
  - repeat split.
    -- hauto lq: on use: L.flowb_can_flow, L.flow_transitivity unfold: label.
    -- sauto use: L.refl unfold: label.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.
Next Obligation.
  prelude.
  - repeat split.
    -- hauto lq: on use: L.flowb_can_flow, L.flow_transitivity unfold: label.
    -- sauto use: L.refl unfold: label.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.

Program Definition sw_request_response (s : valid) : option valid :=
  let b := fst s in
  let t := snd s in
  match (B.inbox b) with
  | None =>
      match (B.next_rq b) with
        | Some rq =>
            match (B.cache_lookup rq (B.curr_cache b)) with
            | Some rp =>
                Some (B.inbox_update b (Some rp),
                  E.EvSWRequestResponse rq rp :: t)
            | None => None
            end
      | None => None
      end
  | _ => None
  end.
Next Obligation.
  prelude.
  - repeat split.
    -- hauto lq: on use: L.flowb_can_flow, L.flow_transitivity unfold: label.
    -- sauto use: L.refl unfold: label.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.

Program Definition sw_update_cache {l: label} (rq: request) (rp: response)
  (s: valid ) : option valid :=
  let b := fst s in
  let t := snd s in 
  Some ((B.cache_update b (rq, rp)),
      E.EvSWUpdateCache rq rp :: E.EvNewCacheEntry (B.curr_sw b) rq rp :: t).
Next Obligation.
  prelude.
  - repeat split.
    -- intros. destruct H, b. inversion H. subst. rewrite RQ.refl, RP.refl. simpl. 
       unfold B.dom_label. simpl. exists sw.
       sauto use: L.flow_reflexivity.
       case_eq (RequestRecord.eqb rq0 rq && ResponseRecord.eqb rp0 rp); intros. eexists.
       rewrite andb_true_iff in H0. destruct H0. erewrite RQ.eqb_eq in H0. erewrite RP.eqb_eq in H1.
       sauto use: L.flow_reflexivity.
       sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed. 

Program Definition js_dont_update_cache (rq: request) (rp: response)
  (s : valid ) : option valid :=
  None.
Fail Next Obligation.

Program Definition js_update_cache (rq: request) (rp: response)
  (s : valid ) : option valid :=
  let b := fst s in
  let t := snd s in
  match (L.flowb (B.dom_label b) (B.curr_sw b)) with
  | true =>
      Some (B.cache_update b (rq, rp),
          E.EvJSUpdateCache rq rp :: E.EvNewCacheEntry (B.dom_label b) rq rp :: t)
  | _ => None
  end. 
Next Obligation.
  prelude.
  - repeat split.
    -- intros. destruct H, b. inversion H. subst. rewrite RQ.refl, RP.refl. simpl. 
       unfold B.dom_label. simpl. 
       hauto b: on.
       case_eq (RequestRecord.eqb rq0 rq && ResponseRecord.eqb rp0 rp).
       eexists. rewrite andb_true_iff in H0. destruct H0.
       erewrite RQ.eqb_eq in H0. erewrite RP.eqb_eq in H1.
       hauto lq: on.
       sfirstorder.
    -- sfirstorder.
  - repeat split.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
    -- sfirstorder.
  - sfirstorder.
Qed.

Fail Next Obligation.
