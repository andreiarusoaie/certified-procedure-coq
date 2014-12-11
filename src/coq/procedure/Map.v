Require Import List.
Require Import ZArith.

(* Maps as lists of pairs *)
Definition Map (T1 : Type) (T2 : Type) := list (T1 * T2).

(* The following functions behave as expected only for consistent maps,
   that is, keys appear only once in the map. *)

(* public: retrieve the value for a given key *)
Fixpoint get (T1 T2 : Type) (M : Map T1 T2) (key : T1) 
             (eq : T1 -> T1 -> bool) :=
  match M with
    | nil => None
    | hd :: tl => match hd with
                    | (k, v) => if (eq k key) 
                                then Some v 
                                else get T1 T2 tl key eq
                  end
  end.

(*
Eval compute in get nat ((3, 4) :: (4, 5) :: nil) 3 beq_nat .
Eval compute in get nat nil 3 beq_nat .
*)

(* public: delete *all* occurences of a given key *)
Fixpoint delete (T1 T2 : Type) (M : Map T1 T2) (key : T1) 
                (eq : T1 -> T1 -> bool) :=  
  match M with
    | nil => nil
    | hd :: tl => match hd with
                    | (k, v) => if (eq k key)
                                then delete T1 T2 tl key eq
                                else hd :: delete T1 T2 tl key eq
                  end
  end.

(*
Eval compute in delete nat ((3, 4) :: (4, 5) :: (3, 6) :: nil) 3  beq_nat .
*)


(* public: updates the *value* of *key* in the map or appends (key, value) 
           in the map if key is not present apriori *)
Fixpoint put (T1 T2 : Type) (M : Map T1 T2) (key : T1) 
             (value : T2) (eq : T1 -> T1 -> bool) :=  
  match M with
    | nil => (key, value) :: nil
    | hd :: tl => match hd with
                    | (k, v) => if (eq k key)
                                then (key, value) ::  tl
                                else hd :: put T1 T2 tl key value eq
                  end
  end.


(*
Eval compute in put nat ((3, 4) :: (4, 5) :: nil) 0 7  beq_nat .
Eval compute in put nat ((3, 4) :: (4, 5) :: nil) 4 7  beq_nat .
*)

(* put-clean *)
(* 
Fixpoint add (T : Type) (M : Map T) (key value : T) (eq : T -> T -> bool) :=  
  (key, value) :: delete T M key eq. 
*)