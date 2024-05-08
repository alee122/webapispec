Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
  
Module Type MAP.
  Parameter Map : Type -> Type -> Type.
  Parameter empty : forall A B, Map A B.
  Parameter lookup : forall A B, Map A B -> A -> option B.
  Parameter add : forall A B, Map A B -> A -> B -> Map A B.

  Notation "$0" := (empty _ _).
  Notation "m $+ ( k , v )" := (add m k v) (at level 50, left associativity).
  Infix "$?" := lookup (at level 50, no associativity).

  Axiom lookup_empty : forall A B k, empty A B $? k = None.

  Parameter Forall_map : forall A B, Map A B -> ((A * B) -> Prop) -> Prop.

  Axiom Forall_map_forall : forall A B inv (m : Map A B),
      Forall_map m inv ->
      (forall k v, m $? k = Some v -> inv (k, v)).

  Axiom Forall_for_new_P : forall A B (inv : (A * B) -> Prop) (m : Map A B) k v,
      Forall_map m inv ->
      inv (k, v) ->
      Forall_map (m $+ (k, v)) inv.
End MAP.

(* Module FM <: MAP. *)
(*   Definition Map (A B : Type) := A -> option B. *)
(*   Definition empty A B : Map A B := fun _ => None. *)
(*   Section decide. *)
(*     Variable P : Prop. *)
(*     Lemma decided : inhabited (sum P (~P)). *)
(*     Proof. *)
      
(*   Definition add A B (m : Map A B) (k : A) (v : B) : Map A B := *)
(*     fun k' => if decide (k' = k) then Some v else m k'. *)

(* Module M <: MAP. *)
(*   Definition Map (A B : Type) := list (A * B). *)
(*   Definition empty (A B : Type) := [] : list (A * B). *)
(*   Definition lookup  *)
(* End M. *)
(*   Definition fmap (A B : Type)  *)
  

(*   Definition cache := list (nat * (list (request * response))). *)
(*   Definition empty := nil : cache. *)
(*   Definition add (c : cache) (e := e :: c. *)
(* End SC. *)
