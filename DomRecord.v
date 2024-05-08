Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import BrowserInfoFlow.Url.
Require Import BrowserInfoFlow.RequestRecord.

From Hammer Require Import Hammer.

Module S := UrlSets.S.

Inductive RequestState :=
| NotRequested
| Requested
| Loaded.

Definition rq_state_eqb r1 r2:=
  match r1,r2 with
  | NotRequested,NotRequested
  | Requested,Requested
  | Loaded, Loaded => true
  | _,_ => false 
  end.

Lemma rq_state_eqb_eq : forall r1 r2,
    rq_state_eqb r1 r2 = true -> r1 = r2.
Proof.
  sauto lq: on.
Qed.

Lemma rq_state_eqb_refl : forall r,
    rq_state_eqb r r = true.
Proof.
  sauto lq: on.
Qed.

Inductive Element :=
| Static : Element
| Script : Url -> RequestState -> Element
| iFrame : Url -> RequestState -> Window -> Element
| Pair : Element -> Element -> Element
with Window :=
| WindowFrame : option Url -> option Element -> RequestState -> Window.

Scheme
  window_mut := Induction for Window Sort Prop
    with
    element_mut := Induction for Element Sort Prop
.

Fixpoint eloaded_scripts (e : Element) (origin : Url) : S.t :=
  match e with
  | Script u Loaded => S.singleton u
  | Static
  | Script _ _ => S.empty
  | iFrame _ _ w => wloaded_scripts w origin
  | Pair e1 e2 => S.union (eloaded_scripts e1 origin) (eloaded_scripts e2 origin)
  end
with 
wloaded_scripts (w : Window) (origin : Url) : S.t :=
  match w with
  | WindowFrame (Some u) (Some e) _ =>
      if (url.eqb u origin)
      then eloaded_scripts e origin
      else S.empty
  | _ => S.empty
  end.

Definition dom_label w :=
  match w with
  | WindowFrame (Some u) _ _ => wloaded_scripts w u
  | _ => S.empty
  end.

Fixpoint is_parent (i1 i2 : Initiator) : bool :=
  match i1, i2 with
  (* Navigation through the tree: *)
  | PairFirst i1',PairFirst i2' => is_parent i1' i2'
  | PairSecond i1',PairSecond i2' => is_parent i1' i2'
  | iFrameContainer i1',iFrameContainer i2' => is_parent i1' i2'
  (* After finding the specific script, with a non-empty path to a frame *)
  | ScriptLocation,_ => true                                                      
  | _,_ => false
  end.

Fixpoint initiator_for_parent_window i : option Initiator :=
  match i with
  | WindowLocation => Some WindowLocation
  | WindowContainer i' =>
      match (initiator_for_parent_window i') with
      | Some wi => Some (WindowContainer wi)
      | None => Some WindowLocation
      end
  | PairFirst i' =>
      match (initiator_for_parent_window i') with
      | Some wi => Some (PairFirst wi)
      | _ => None
      end
  | PairSecond i' => 
      match (initiator_for_parent_window i') with
      | Some wi => Some (PairSecond wi)
      | _ => None
      end
  | iFrameContainer i' => 
      match (initiator_for_parent_window i') with
      | Some wi => Some (iFrameContainer wi)
      | _ => None
      end
  | _ => None
  end.

Fixpoint einitiator_for (e : Element) (elem_select : Element -> bool) (win_select : Window -> bool) : option Initiator :=
  match e with
  | Script _ _ => if (elem_select e) then Some ScriptLocation else None
  | iFrame _ _ w => if (elem_select e) then Some iFrameLocation else
                     match (winitiator_for w elem_select win_select) with
                     | Some i' => Some (iFrameContainer i')
                     | _ => None
                     end
  | Pair e1 e2 => match (einitiator_for e1 elem_select win_select) with
                 | Some i' => Some (PairFirst i')
                 | None =>
                     match (einitiator_for e2 elem_select win_select) with
                     | Some i' => Some (PairSecond i')
                     | _ => None
                     end
                 end
  | _ => None
  end
with
winitiator_for (w : Window) (elem_select : Element -> bool) (win_select : Window -> bool) : option Initiator :=
  if (win_select w)
  then Some WindowLocation
  else match w with
       | WindowFrame _ (Some e) _ =>
           match (einitiator_for e elem_select win_select) with
           | Some i' => Some (WindowContainer i')
           | None => None
           end
       | _ => None
       end.

Fixpoint einitiator_get_elem (e : Element) (i : Initiator) : option Element :=
  match e,i with 
  | Script _ _, ScriptLocation => Some e
  | iFrame _ _ w, iFrameLocation => Some e
  | iFrame _ _ w, iFrameContainer i' => winitiator_get_elem w i'
  | Pair e1 _, PairFirst i' => einitiator_get_elem e1 i'
  | Pair _ e2, PairSecond i' => einitiator_get_elem e2 i'
  | _,_ => None
  end
with
winitiator_get_elem (w : Window) (i : Initiator) : option Element :=
  match w,i with
  | WindowFrame _ (Some e) _, WindowContainer i' => einitiator_get_elem e i'
  | WindowFrame _ (Some e) _, WindowLocation => Some e
  | _, _ => None
  end.

Fixpoint einitiator_change_elem (i : Initiator) (e : Element) (update : Element -> Element) : option Element :=
  match e,i with 
  | Script _ _, ScriptLocation => Some (update e)
  | iFrame u s w, iFrameContainer i' =>
      match (winitiator_change_elem i' w update) with
      | Some w' => Some (iFrame u s w')
      | _ => None
      end
  | Pair e1 e2, PairFirst i' =>
      match (einitiator_change_elem i' e1 update) with
      | Some e1' => Some (Pair e1' e2)
      | _ => None
      end
  | Pair e1 e2, PairSecond i' => 
      match (einitiator_change_elem i' e2 update) with
      | Some e2' => Some (Pair e1 e2')
      | _ => None
      end
  | _,_ => None
  end
with
winitiator_change_elem (i : Initiator) (w : Window) (update : Element -> Element) : option Window :=
  match w,i with
  | WindowFrame u (Some e) Requested, WindowLocation => Some (WindowFrame u (Some (update e)) Loaded)
  | WindowFrame u (Some e) s, WindowContainer i' =>
      match (einitiator_change_elem i' e update) with
      | Some e'' => Some (WindowFrame u (Some e'') s)
      | _ => None
      end
  | _, _ => None
  end.

Fixpoint einitiator_set_window (i : Initiator) (e : Element) (w' : Window) : option Element :=
  match e,i with 
  | iFrame u s w, iFrameLocation => Some (iFrame u s w')
  | iFrame u s w, iFrameContainer i' =>
      match (winitiator_set_window i' w w') with
      | Some w' => Some (iFrame u s w')
      | _ => None
      end
  | Pair e1 e2, PairFirst i' =>
      match (einitiator_set_window i' e1 w') with
      | Some e1' => Some (Pair e1' e2)
      | _ => None
      end
  | Pair e1 e2, PairSecond i' =>
      match (einitiator_set_window i' e2 w') with
      | Some e2' => Some (Pair e1 e2')
      | _ => None
      end
  | _,_ => None
  end
with
winitiator_set_window (i : Initiator) (w w' : Window) : option Window :=
  match w,i with
  | WindowFrame u (Some e) s, WindowContainer i' =>
      match (einitiator_set_window i' e w') with
      | Some e'' => Some (WindowFrame u (Some e'') s)
      | _ => None
      end
  | _, _ => None
  end.

Definition einitiator_set_rqstate (i : Initiator) (e : Element) (s' : RequestState) : option Element :=
  einitiator_change_elem i e (fun x => match x with
                                    | Script u _ => Script u Loaded
                                    | _ => x
                                    end).

Definition winitiator_set_rqstate (i : Initiator) (w : Window) (s' : RequestState) : option Window :=
  winitiator_change_elem i w (fun x => match x with
                                    | Script u _ => Script u Loaded
                                    | _ => x
                                    end).
Fixpoint einitiator_get_window (e : Element) (i : Initiator) : option Window :=
  match e,i with
  | iFrame _ _ w, iFrameContainer i' => winitiator_get_window w i'
  | Pair e1 _, PairFirst i' => einitiator_get_window e1 i'
  | Pair _ e2, PairSecond i' => einitiator_get_window e2 i'
  | _,_ => None
  end
with
winitiator_get_window (w : Window) (i : Initiator) : option Window :=
  match w,i with
  | WindowFrame _ (Some e) _, WindowContainer i' => einitiator_get_window e i'
  | WindowFrame _ _ _, WindowLocation => Some w
  | _, _ => None
  end.

