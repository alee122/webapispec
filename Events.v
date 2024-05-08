(* Trace *)
Require BrowserInfoFlow.ResponseRecord.
Require BrowserInfoFlow.RequestRecord.
Require BrowserInfoFlow.LabelRecord.
Require Import BrowserInfoFlow.CookieRecord.
Require Import BrowserInfoFlow.Url.

Module event.

  Inductive event :=
  (* General Events *)
  | EvRequest : RequestRecord.unfilled_request -> option url.url -> event
  | EvResponse : ResponseRecord.response -> event
  | EvJSNavigate : RequestRecord.Initiator -> RequestRecord.Initiator -> event
  (* SW Events *)
  | EvLoadSW : LabelRecord.label -> event
  | EvNewCacheEntry : LabelRecord.label -> RequestRecord.request -> ResponseRecord.response -> event
  | EvSWRequestResponse : RequestRecord.request -> ResponseRecord.response -> event
  | EvSWUpdateCache : RequestRecord.request -> ResponseRecord.response -> event
  | EvJSUpdateCache : RequestRecord.request -> ResponseRecord.response -> event
  (* Cookie Events *)
  | EvJSGetCookie : list SetCookie -> LabelRecord.label -> event
  | EvHTTPGetCookie : SetCookie -> event
  | EvJSSetCookie : Domain -> SetCookie -> event
  | EvHTTPSetCookie : Domain -> list SetCookie -> event.

  Definition trace := list event.
End event.
