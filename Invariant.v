Require Import Coq.Bool.Bool. Import BoolNotations.
Require Import Coq.Lists.List.
Import ListNotations.

(* Require Import BrowserInfoFlow.SWImpl. *)
Require Import BrowserInfoFlow.Events.
Require Import BrowserInfoFlow.BrowserRecord.
Require Import BrowserInfoFlow.RequestRecord.
Require Import BrowserInfoFlow.ResponseRecord.

From Hammer Require Import Hammer Tactics.

Module E := Events.event.

Definition trace := list E.event.
Definition state := (browser_state * trace)%type.

Fixpoint request_has_event (t : trace) (urq : RequestRecord.unfilled_request ) : Prop :=
  match t with
  | [] => False
  | (E.EvRequest urq' _)::es => (RequestRecord.ur_eqb urq urq' = true) \/ (request_has_event es urq)
  | _::es => request_has_event es urq
  end.

Definition corresponding_rq (t : trace) (urq : RequestRecord.unfilled_request ) : option E.event :=
  let corresponding_rq (ev : E.event) :=
    match ev with
    | E.EvRequest urq' _ =>
        RequestRecord.eqb urq.(RequestRecord.u_rq) urq'.(RequestRecord.u_rq)
    | _ => false
    end
  in find corresponding_rq t.

Definition corresponding_most_recent_new (t : trace) (rq : RequestRecord.request ) rp  : option E.event :=
  let corresponding_new (ev : E.event) :=
    match ev with
    | E.EvNewCacheEntry _ new_rq new_rp =>
            RequestRecord.eqb rq new_rq && ResponseRecord.eqb rp new_rp
    | _ => false 
    end
  in find corresponding_new t.

Definition most_recent_SW_load (t : trace) : option E.event :=
  let is_SW_load (ev : E.event) :=
    match ev with
    | E.EvLoadSW _ => true
    | _ => false
    end
  in find is_SW_load t.

Fixpoint zip {A B : Type} l1 l2 : list (A * B) :=
  match l1,l2 with
  | x1::l1', x2::l2' => (x1,x2) :: (zip l1' l2')
  | _,_ => []
  end.

  (* Forall holds over zip if first list have had the last removed *)
Lemma Forall_hold_zip_drop : forall {A B : Type} (P : (A * B) -> Prop) (l1 l1' : list A) (l2 : list B),
    Forall P (zip l1 l2) ->
    Forall P (zip (removelast l1) l2).
Proof.
  induction l1; intros.
  simpl. eapply Forall_nil.
  simpl.
  destruct l2. simpl. destruct l1; simpl; eapply Forall_nil.
  simpl. destruct l1. simpl. eapply Forall_nil. simpl in *.
  eapply Forall_cons_iff in H. destruct H.
  eapply Forall_cons. assumption. apply IHl1. assumption. assumption.
Qed.

Lemma Forall_hold_zip_drop' : forall {A B : Type} (P : (A * B) -> Prop) (l1 l1' : list A) (l2 : list B) a,
    Forall P (zip (a :: l1) l2) ->
    Forall P (zip match l1 with
                | [] => []
                | _ :: _ => a :: removelast l1
                end l2).
Proof.
  intros. eapply Forall_hold_zip_drop in H. eapply H. eauto. 
Qed.

Definition invariant (s : state) : Prop :=
  let b := fst s in
  let t := snd s in
  (* everything in the cache is labeled in trace and can flow into current SW *)
  ((forall rq rp,
       cache_member (rq, rp) b.(browser_cache) ->
       exists l, (corresponding_most_recent_new t rq rp = Some (E.EvNewCacheEntry l rq rp) /\
               LabelRecord.can_flow l b.(sw))) /\
     (* browser SW corresponds with last trace SW_load event if there was one *)
     (match (most_recent_SW_load t) with
      | Some (E.EvLoadSW l) => LabelRecord.eqb b.(sw) l = true 
      | _ => True
      end))
  /\
    ((Forall (fun event => match event with
                        | E.EvJSNavigate script_loc frame_loc => RequestRecord.is_parent script_loc frame_loc = true
                        | _ => True
                        end) t)
     /\
       (Forall (fun e => match e with
                       | (E.EvRequest ur o) => ur.(u_rq).(origin) = o
                       | _ => True
                       end) t)
     /\ (* Invariants between outbox member and corresponding event in the trace *)
       (* probably also needs length, origin matches between urq and trace label *)
       (Forall (fun cmp => match cmp with
                        | (ur__o,(E.EvRequest ur__e o)) => ur__o = ur__e /\ ur__o.(u_rq).(origin) = o
                        | _ => False
                        end)
          (zip (outbox b)
             (filter (fun e =>
                        match e with
                        | E.EvRequest _ _ => true
                        | _ => false
                        end) t)))
     /\ (length (outbox b) <=
          length ((filter (fun e =>
                             match e with
                             | E.EvRequest _ _ => true
                             | _ => false
                             end) t)))%nat
    )
  /\
    (Forall (fun event => match event with
                       | E.EvJSGetCookie scs l =>
                           Forall (fun sc => match sc.(CookieRecord.sc_http_only) with
                                          | true => LabelRecord.S.Empty l.(LabelRecord.scripts)
                                          | _ => True
                                          end) scs
                       | _ => True
                       end) t).

Program Definition valid := { s: state | invariant s }.

Ltac prelude := repeat (match goal with 
                        | [ s : valid |- _ ] => destruct s
                        | [ x : state |- _ ] => destruct x
                        | [ i : invariant (_, _) |- _ ] => unfold invariant in i
                        | [ H : _ /\ _ |- _ ] => destruct H
                        | [ H : Forall _ (_ :: _) |- _ ] => eapply Forall_cons_iff in H; destruct H
                        end); unfold invariant; split; [idtac | split]; simpl in *. 

Theorem new_browser_valid :
  let u := (Url.mkUrl Url.ProtocolHTTP (Url.domain 0) 0) in
  invariant (mkBrowser u (DomRecord.WindowFrame None None DomRecord.NotRequested)
               (LabelRecord.mkLabel u S.empty) [] [] None [], []).
Proof.
  sfirstorder.
Qed.
