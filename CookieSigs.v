From Coq Require Import MSets Arith.
Require Import BrowserInfoFlow.Url.

Module Type COOKIE(u : URL).
  Parameter cookie_name : Type.
  Parameter cookie_name_eqb : cookie_name -> cookie_name -> bool.
  Axiom cookie_name_eqb_refl : forall cn, cookie_name_eqb cn cn = true. 
  Axiom cookie_name_eqb_eq : forall cn1 cn2, cookie_name_eqb cn1 cn2 = true <-> cn1 = cn2.
  Parameter cookie_mapping : Type.
  Parameter same_site : Type.
  Parameter ss_eqb : same_site -> same_site -> bool.
  Axiom ss_eqb_refl : forall cn, ss_eqb cn cn = true. 
  Axiom ss_eqb_eq : forall cn1 cn2, ss_eqb cn1 cn2 = true <-> cn1 = cn2.
  Parameter set_cookie : Type.
  Parameter sc_name : set_cookie -> cookie_name.
  Parameter sc_http_only : set_cookie -> bool.
  Parameter sc_eqb : set_cookie -> set_cookie -> bool.
  Axiom sc_eqb_refl : forall cn, sc_eqb cn cn = true. 
  Axiom sc_eqb_eq : forall cn1 cn2, sc_eqb cn1 cn2 = true <-> cn1 = cn2.
  Parameter set_to_mapping : set_cookie -> cookie_mapping.
  Parameter domain : set_cookie -> option Domain.
  Parameter is_valid_setcookie : u.url -> set_cookie -> bool.
End COOKIE.

Module Type RESPONSE (u : URL).
  Parameter response : Type.
  Parameter rp_cookies : Type.
  Parameter rp_domain : Type.
  Parameter get_rp_cookies : response -> rp_cookies.
  Parameter get_rp_domain : response -> rp_domain.
  Parameter get_rp_url : response -> u.url.
End RESPONSE.

Module Type REQUEST (u : URL).
  Parameter request : Type.
  Parameter unfilled_request : Type.
  Parameter cookies : Type.
  Parameter initiator : Type.
  Parameter populate_cookies : unfilled_request -> cookies -> unfilled_request.
  Parameter destination : unfilled_request -> url.url.
  Parameter origin : unfilled_request -> option url.url.
  Parameter urq_eqb : unfilled_request -> unfilled_request -> bool.
End REQUEST.

Module Type LABEL (u : URL).
  Module S := UrlSets.S.
  Parameter label : Type.
  Parameter can_flow : label -> label -> bool.
  Parameter no_scripts : u.url -> label.
  Parameter mkLabel : u.url -> S.t -> label.
End LABEL.

Module Type BROWSER (u : URL).
  Declare Module RP : RESPONSE(u).
  Declare Module RQ : REQUEST(u).
  Declare Module L : LABEL(u).
  Declare Module C : COOKIE(u).
  Parameter browser : Type.
  Parameter add_to_jar : browser -> (list (Domain * C.set_cookie)) -> browser.
  Parameter inbox : browser -> option RP.response.
  Parameter most_recent_urq : browser -> option RQ.unfilled_request.
  Parameter update_most_recent_rq_cookies : browser -> list C.cookie_mapping -> option browser.
  Parameter cookie_mapping_for_origin : browser -> url.url -> list C.cookie_mapping.
  Parameter find_cookie : browser -> C.cookie_name -> option C.set_cookie.
  Parameter find_cookies : browser -> u.url -> list C.set_cookie.
  Parameter dom_label : browser -> L.label.
  Parameter origin : browser -> u.url.
  Parameter is_valid_setcookie : u.url -> C.set_cookie -> bool.
  Parameter initiator_window_url : browser -> RQ.initiator -> option u.url.
  Parameter dom_label_initiator : browser -> RQ.initiator -> option L.label.
End BROWSER.
