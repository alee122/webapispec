Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Import BoolNotations.
Require Import Coq.Arith.Arith.

Require Import BrowserInfoFlow.CookieSigs.
Require Import BrowserInfoFlow.Url.
Require BrowserInfoFlow.CookieRecord.
Require BrowserInfoFlow.DomRecord.
Require BrowserInfoFlow.LabelRecord.
Require BrowserInfoFlow.ResponseRecord.
Require BrowserInfoFlow.RequestRecord.
Require BrowserInfoFlow.BrowserRecord.

From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.

Module C <: COOKIE(url).
  Import CookieRecord.
  Definition cookie_name := CookieName.
  Definition cookie_name_eqb := cookie_name_eqb.
  Definition cookie_name_eqb_refl := cookie_name_eqb_refl.
  Definition cookie_name_eqb_eq := cookie_name_eqb_eq.
  
  Definition cookie_mapping := CookieMapping.

  Definition same_site := SameSite.
  Definition ss_eqb := ss_eqb.
  Definition ss_eqb_refl := ss_eqb_refl.
  Definition ss_eqb_eq := ss_eqb_eq.

  Definition set_cookie := SetCookie.
  Definition sc_eqb := sc_eqb.
  Definition sc_eqb_refl := sc_eqb_refl.
  Definition sc_eqb_eq := sc_eqb_eq.
  Definition set_to_mapping sc := mkCookieMapping sc.(sc_name) sc.(sc_value).
  Definition sc_name := sc_name.
  Definition sc_http_only := sc_http_only.
  Definition domain := sc_domain.
  Definition is_valid_setcookie := is_valid_setcookie.
End C.

Module RP <: RESPONSE(url).
  Import ResponseRecord.
  Definition response := response.
  Definition rp_cookies := CookieRecord.ResponseCookies.
  Definition rp_domain := Domain.
  Definition get_rp_cookies rp := rp.(cookies).
  Definition get_rp_domain rp := rp.(response_url).(host).
  Definition get_rp_url rp := rp.(response_url).
End RP.

Module RQ <: REQUEST(url).
  Import RequestRecord.
  Definition request := request.
  Definition unfilled_request := unfilled_request.
  Definition initiator := Initiator.
  Definition cookies := list C.cookie_mapping.
  Definition populate_cookies urq (cm : cookies) :=
    let rq := urq.(u_rq) in 
    mkUnfilledRequest urq.(initiator_rq) (mkRequest rq.(url__rq) rq.(origin) rq.(method) rq.(body__rq) cm).
  Definition destination urq := urq.(u_rq).(url__rq).
  Definition origin urq := urq.(u_rq).(origin).
  Definition urq_eqb := ur_eqb.
End RQ.

Module L <: LABEL(url).
  Module S := UrlSets.S.
  Import LabelRecord.
  Definition label := LabelRecord.label.
  Definition can_flow := LabelRecord.flowb.
  Definition no_scripts o := mkLabel o S.empty.
  Definition mkLabel := mkLabel.
End L.

Module B <: BROWSER(url).
  Import BrowserRecord.
  Module RP := RP.
  Module RQ := RQ.
  Module L := L.
  Module C := C.
  Definition browser := browser_state.
  Definition add_to_jar (b : browser) j :=
    mkBrowser b.(origin) b.(dom) b.(sw) b.(browser_cache) b.(outbox) b.(inbox) (j ++ (jar b)).
  Definition cjar := CookieRecord.CookieJar.
  Definition mapping := CookieRecord.CookieMapping.
  Definition most_recent_urq b := match (b.(outbox)) with
                                  | urq :: _ => Some urq
                                  | _ => None
                                  end.
  Fixpoint update_last outbox (cs : list C.cookie_mapping) :=
    match outbox with
    | [] => []
    | [urq] => [RQ.populate_cookies urq cs]
    | urq1 :: outbox' => urq1 :: (update_last outbox' cs)
    end.
  Definition update_most_recent_rq_cookies b (cs : list C.cookie_mapping) :=
    match (outbox b) with
    | [] => None
    | urq :: outbox' =>
        Some (mkBrowser b.(origin) b.(dom) b.(sw) b.(browser_cache)
                                                      ((RQ.populate_cookies urq cs) :: outbox')
                                                      b.(inbox) b.(jar))
    end.
  Definition inbox b := b.(inbox).
  Definition cookie_mapping_for_origin b o :=
    map
      (fun p => match p with
             | (_, sc) => C.set_to_mapping sc
             end)
      (filter (fun dsc =>
                 match dsc with
                 | (d,sc) => 
                     (match (C.domain sc) with
                      | Some d' => sub_or_eq_domain d' o.(host)
                      | None => domain_eqb d o.(host)
                      end)
                 end)
         b.(jar)).

  Definition find_cookie b cn :=
    match (filter (fun sc => C.cookie_name_eqb (C.sc_name (snd sc)) cn) (jar b)) with
    | (_,sc') :: _ => Some sc'
    | [] => None
    end.
  Definition find_cookies b o :=
    map
      (fun p => match p with
             | (_, sc) => sc
             end)
      (filter (fun dsc =>
                 match dsc with
                 | (d,sc) => 
                     (match (C.domain sc) with
                      | Some d' => sub_or_eq_domain d' o.(host)
                      | None => domain_eqb d o.(host)
                      end)
                 end)
         b.(jar)).
  Definition dom_label (b : browser) := L.mkLabel b.(origin) (DomRecord.dom_label b.(dom)).

  Definition dom_label_initiator (b : browser) i := dom_label_initiator b.(dom) i.
  Definition origin b := b.(origin).
  Definition is_valid_setcookie := CookieRecord.is_valid_setcookie.
  Definition initiator_window_url b i := parent_window_url i b.(dom).
End B.
