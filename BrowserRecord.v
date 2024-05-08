Require Import Coq.Lists.List.
Import ListNotations.

Require Import BrowserInfoFlow.RequestRecord.
Require Import BrowserInfoFlow.ResponseRecord.
Require Import BrowserInfoFlow.LabelRecord.
Require Import BrowserInfoFlow.DomRecord.
Require Import BrowserInfoFlow.CookieRecord.
Require Import BrowserInfoFlow.Url.

From Hammer Require Import Hammer Tactics.

Module S := UrlSets.S.

Fixpoint last_op {A : Type} (l : list A) : option A :=
  match l with
  | [] => None
  | [e] => Some e
  | _::l' => last_op l'
  end.

Lemma last_op_nonempty_last : forall {A} (l : list A) d,
    l <> [] ->
    last_op l = Some (last l d).
Proof.
  induction l; intros; hauto lq: on.
Qed.

Fixpoint drop_last {A : Type} (l : list A) : option (list A) :=
  match l with
  | [] => None
  | [e] => Some []
  | e1::l' => match (drop_last l') with
            | Some l'' => Some (e1::l'')
            | _ => None
            end
  end.

Lemma drop_last_removelast : forall {A} (l : list A),
    l <> [] ->
    drop_last l = Some (removelast l).
Proof.
  induction l; intros; hauto lq: on.
Qed.

Lemma removelast_leq_len : forall {A} (la : list A),
    (length (removelast la) <= length la)%nat.
Proof.
  induction la. sfirstorder. destruct la; sfirstorder.
Qed.

Lemma drop_last_spec : forall {A} (l l' : list A) e,
    last_op l = Some e -> 
    drop_last l = Some l' ->
    l = l' ++ [e].
Proof.
  induction l, l'; hauto b: on.
Qed.

Definition head_op {A : Type} (l : list A) : option A :=
 match l with
  | e :: _ => Some e
  | _ => None
  end.

Definition tail_op {A : Type} (l : list A) : option (list A) :=
  match l with
  | _ :: l' => Some l'
  | _ => None
  end.

Lemma last_op_is_rev_head : forall {A : Type} (l : list A),
    last_op l = head_op (rev l).
Proof.
  intros. induction l; try sfirstorder.
  simpl; destruct l. simpl. reflexivity. simpl.
  assert (forall (l1 l2 : list A) e, head_op ((l1 ++ [e]) ++ l2) = head_op (l1 ++ [e])).
  sauto lq: on. erewrite H. simpl in IHl. assumption.
Qed.

Lemma Forall_hold_after_drop : forall {A : Type} (P : A -> Prop) (l : list A) l',
    Forall P l ->
    drop_last l = Some l' -> 
    Forall P l'.
Proof.
  induction l; intros. simpl in H0. inversion H0.
  erewrite drop_last_removelast in H0. 2: sfirstorder. inversion H0.
  destruct l. inversion H2. eapply Forall_nil.
  eapply Forall_cons_iff in H. destruct H. eapply Forall_cons.  assumption.
  eapply IHl. assumption. erewrite drop_last_removelast. reflexivity. sfirstorder.
Qed.

Lemma last_op_is_first_rev : forall {A : Type} (l : list A) e,
    last_op l = Some e ->
    exists l', rev l = e :: l'.
Proof.
  induction l.
  intros; simpl. inversion H.
  simpl. destruct l. simpl. intros. inversion H. exists []. reflexivity.
  intros. apply IHl in H. inversion H. rewrite H0. simpl. eexists.
  reflexivity.
Qed.

Lemma last_is_first_rev : forall {A : Type} (l l' : list A) e,
    l = l' ++ [e] ->
    rev l = e :: (rev l').
Proof.
  destruct l.
  intros. eapply app_cons_not_nil in H. inversion H.
  intros. rewrite H. apply rev_app_distr.
Qed.

Lemma non_empty_list_has_last : forall {A} (l : list A) a,
  exists e', last_op (a :: l) = Some e'.
Proof.
  induction l; intros.
  eexists. reflexivity.
  specialize (IHl a). inversion IHl. exists x.
  simpl in *. rewrite H. reflexivity.
Qed.

Lemma non_empty_list_can_drop : forall {A} (l : list A) a,
  exists l', drop_last (a :: l) = Some l'.
Proof.
  induction l. simpl. intros.
  eexists. reflexivity.
  intros. specialize (IHl a). inversion IHl. exists (a0 :: x).
  inversion H. simpl. destruct l.
  inversion H1. reflexivity.
  simpl in *. rewrite H1. reflexivity.
Qed.

Lemma empty_list_has_no_last : forall {A : Type},
    @last_op A [] = None.
Proof.
  eauto.
Qed.

Lemma non_empty_list_cant_drop : forall {A : Type},
  @drop_last A [] = None.
Proof.
  eauto.
Qed.

(* Cache operations *)
Definition cache := list (request * response).

Definition cache_member (entry : request * response) (c : cache) : Prop :=
  In entry c.

Fixpoint cache_lookup (rq : request) (c : cache) : option response :=
  match c with 
  | (rq', rp) :: c' => if RequestRecord.eqb rq rq' then Some rp else cache_lookup rq c'
  | [] => None
  end.

Record browser_state := mkBrowser { origin : Url ; dom : Window; sw : label ; browser_cache: cache ; outbox : list unfilled_request ; inbox : option response ; jar : CookieJar}. 

Definition add_to_outbox b ur :=
  mkBrowser b.(origin) b.(dom) b.(sw) b.(browser_cache) (ur::b.(outbox)) b.(inbox) b.(jar).

Definition reduce_outbox b :=
  match (drop_last b.(outbox)),(last_op b.(outbox)) with
  | Some outbox', Some urq =>  
      (mkBrowser b.(origin) b.(dom) b.(sw) b.(browser_cache) (outbox') b.(inbox) b.(jar), Some urq)
  | _,_ => (b, None)
  end.

Fixpoint rp_to_elem (rc : response_content) : Element :=
  match rc with
  | RpStatic => Static
  | RpScript u => Script u Loaded
  | RpiFrame u => iFrame u NotRequested (WindowFrame None None NotRequested)
  | RpPair rc1 rc2 => Pair (rp_to_elem rc1) (rp_to_elem rc2)
  end.

(* use initiator to put in the right place *)
Fixpoint eupdate_dom (i : Initiator) (edom : Element) (rp : response_content) : option Element :=
  match i,edom,rp with
  | ScriptLocation, Script du Requested, RpScript ru =>
      if (url.eqb du ru)
      then Some (Script du Loaded)
      else None
  | iFrameLocation, iFrame _ _ _, RpiFrame u => Some (iFrame u NotRequested (WindowFrame None None NotRequested))
  (* is the above correct? where do you put response to iframe request?? *)
  | iFrameContainer i', iFrame u s w,_ =>
      match (wupdate_dom i' w rp) with
      | Some w' => Some (iFrame u s w')
      | None => None
      end
  | PairFirst i', Pair e1 e2,_ => eupdate_dom i' e1 rp
  | PairSecond i', Pair e1 e2,_ => eupdate_dom i' e2 rp
  | _,_,_ => None
  end
with
wupdate_dom (i : Initiator) (dom : Window) (rp : response_content) : option Window :=
  match i,dom with
  | WindowContainer i', WindowFrame ou (Some e) s => Some (WindowFrame ou (eupdate_dom i' e rp) s)
  | WindowLocation, WindowFrame ou _ _ => Some (WindowFrame ou (Some (rp_to_elem rp)) Loaded)
  | _,_ => None
  end.

Definition update_dom b i rp := wupdate_dom i b.(dom) rp.

Fixpoint eupdate_loadedness (i : Initiator) (e : Element) : option Element :=
  match i,e with
  | ScriptLocation, Script u NotRequested => Some (Script u Requested)
  | iFrameLocation, iFrame u NotRequested w => Some (iFrame u Requested w)
  | iFrameContainer i', iFrame u Loaded w =>
      match (wupdate_loadedness i' w) with
      | Some w' => Some (iFrame u Loaded w')
      | None => None
      end
  | PairFirst i', Pair e1 e2 =>
      match (eupdate_loadedness i' e1) with
      | Some e1' => Some (Pair e1' e2)
      | _ => None
      end
  | PairSecond i', Pair e1 e2 =>
      match (eupdate_loadedness i' e2) with
      | Some e2' => Some (Pair e1 e2')
      | _ => None
      end
  | _,_ => None
  end
with
wupdate_loadedness (i : Initiator) (w : Window) : option Window :=
  match i,w with
  | WindowLocation, WindowFrame ou oe NotRequested => Some (WindowFrame ou oe Requested)
  | WindowContainer i', WindowFrame ou (Some e) Loaded =>
      match (eupdate_loadedness i' e) with
      | Some e' => Some (WindowFrame ou (Some e') Loaded)
      | None => None
      end
  | _,_ => None
  end.

Fixpoint redirect_window (w : Window) (window_loc : Initiator) (new_u : Url) : option Window :=
  match window_loc,w with
  | WindowLocation, WindowFrame _ e _ => Some (WindowFrame (Some new_u) e NotRequested)
  | WindowContainer i', WindowFrame ou (Some e) s =>
      match (eredirect_window e i' new_u) with
      | Some e' => Some (WindowFrame ou (Some e') s)
      | _ => None
      end
  | _,_ => None
  end
with
eredirect_window (e : Element) (window_loc : Initiator) (new_u : Url) : option Element :=
  match window_loc,e with
  | iFrameContainer i', iFrame u s w =>
      match (redirect_window w i' new_u) with
      | Some w' => Some (iFrame u s w')
      | _ => None
      end
  | PairFirst i', Pair e1 e2 =>
      match (eredirect_window e1 i'  new_u) with
      | Some e1' => Some (Pair e1' e2)
      | _ => None
      end
  | PairSecond i', Pair e1 e2 => 
      match (eredirect_window e2 i'  new_u) with
      | Some e2' => Some (Pair e1 e2')
      | _ => None
      end
  | _,_ => None
  end.

Fixpoint redirect_frame (w : Window) (frame_loc : Initiator) (new_u : Url) : option Window :=
  match frame_loc,w with
  | WindowContainer i', WindowFrame ou (Some e) s =>
      match (eredirect_frame e i' new_u) with
      | Some e' => Some (WindowFrame ou (Some e') s)
      | _ => None
      end
  | _,_ => None
  end
with
eredirect_frame (e : Element) (frame_loc : Initiator) (new_u : Url) : option Element :=
  match frame_loc,e with
  | iFrameLocation, iFrame u _ w => Some (iFrame new_u NotRequested w)
  | iFrameContainer i', iFrame u s w =>
      match (redirect_frame w i' new_u) with
      | Some w' => Some (iFrame u s w')
      | _ => None
      end
  | PairFirst i', Pair e1 e2 =>
      match (eredirect_frame e1 i'  new_u) with
      | Some e1' => Some (Pair e1' e2)
      | _ => None
      end
  | PairSecond i', Pair e1 e2 => 
      match (eredirect_frame e2 i'  new_u) with
      | Some e2' => Some (Pair e1 e2')
      | _ => None
      end
  | _,_ => None
  end.

Fixpoint eorigin_of (i : Initiator) (e : Element) (origin : option Url) : option Url :=
  match i,e with
  | ScriptLocation, Script _ _ => origin
  | iFrameLocation, iFrame _ _ _ => origin
  | iFrameContainer i', iFrame _ _ w => worigin_of i' w origin
  | PairFirst i', Pair e1 _ => eorigin_of i' e1 origin
  | PairSecond i', Pair _ e2 => eorigin_of i' e2 origin
  | _,_ => None
  end
with
worigin_of (i : Initiator) (w : Window) (origin : option Url) : option Url :=
  match i,w with
  (* | WindowLocation, WindowFrame _ _ NotRequested  (* should this actually be the containing window's origin? *) *)
  | WindowLocation, WindowFrame _ _ Requested => origin (* should this actually be the containing window's origin? *)
  | WindowContainer i', WindowFrame (Some u) (Some e) _ => eorigin_of i' e (Some u)
  | _,_ => None
  end.

Fixpoint eorigin_of' (i : Initiator) (e : Element) (origin : Url) : option Url :=
  match i,e with
  | ScriptLocation,Script u NotRequested => Some origin
  | iFrameLocation,iFrame u NotRequested _ => Some origin
  | iFrameContainer i',iFrame _ Requested w => worigin_of' i' w origin
  | PairFirst i',Pair e1 e2 => eorigin_of' i' e1 origin
  | PairSecond i',Pair e1 e2 => eorigin_of' i' e2 origin
  | _,_ => None 
  end
with
worigin_of' (i : Initiator) (w : Window) (origin : Url) : option Url :=
  match i,w with
  | WindowLocation,(WindowFrame (Some u) (Some _) NotRequested) => Some u
  | WindowLocation,WindowFrame (Some u) None _ => Some u
  | WindowContainer i',WindowFrame (Some u) (Some e) Loaded => eorigin_of' i' e u
  | _,_ => None 
  end.

Fixpoint emake_unfilled_request_object (e : Element) (origin : Url) : option unfilled_request :=
  match e with
  | Script u NotRequested => Some (mkUnfilledRequest ScriptLocation (mkRequest u (Some origin) MethodGet None []))
  | iFrame u NotRequested _ => Some (mkUnfilledRequest iFrameLocation (mkRequest u (Some origin) MethodGet None []))
  | iFrame _ Requested w =>
      match (wmake_unfilled_request_object w) with
      | Some ur => Some (mkUnfilledRequest (iFrameContainer ur.(initiator_rq)) ur.(u_rq))
      | None => None
      end
  | Pair e1 e2 =>
      match (emake_unfilled_request_object e1 origin) with
      | Some ur => Some (mkUnfilledRequest (PairFirst ur.(initiator_rq)) ur.(u_rq))
      | None => match (emake_unfilled_request_object e2 origin) with
               | Some ur => Some (mkUnfilledRequest (PairSecond ur.(initiator_rq)) ur.(u_rq))
               | _ => None
               end
      end
  | _ => None 
  end
with
wmake_unfilled_request_object (w : Window) : option unfilled_request :=
  match w with
  | WindowFrame (Some u) (Some _) NotRequested => Some (mkUnfilledRequest WindowLocation (mkRequest u (Some u) MethodGet None []))
  | WindowFrame (Some u) None _ => Some (mkUnfilledRequest WindowLocation (mkRequest u (Some u) MethodGet None []))
  | WindowFrame (Some u) (Some e) Loaded =>
      match (emake_unfilled_request_object e u) with
      | Some ur => Some (mkUnfilledRequest (WindowContainer ur.(initiator_rq)) ur.(u_rq))
      | None => None
      end
  | _ => None
  end.

Definition parent_window_url (i : Initiator) (d : Window) : option Url :=
  match (initiator_for_parent_window i) with
  | Some i' => match (winitiator_get_window d i') with
              | Some (WindowFrame u _ _) => u
              | _ => None
              end
  | _ => None
  end.

Definition dom_label_initiator (b : Window) i :=
  match (initiator_for_parent_window i) with
  | Some i' => 
      match (DomRecord.winitiator_get_window b i') with
      | Some (WindowFrame (Some u) e s) => 
          Some (mkLabel u (DomRecord.dom_label (WindowFrame (Some u) e s)))
      | _ => None
      end
  | _ => None
  end.
