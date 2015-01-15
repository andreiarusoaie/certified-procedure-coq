Require Import logic.
Require Import List .

(* paths -> Coinductive lists?*)

(* Parameter Path : Set .*)

Definition Path := nat -> option Model.


(*
Definition PathTo (tau : Path) (n : nat) : Path :=
  fun i : nat => if (i > n) then None
           else tau i . 
*)
Parameter PathTo : Path -> nat -> Path .
Parameter PathFrom : Path -> nat -> Path .
Parameter nth : Path -> nat -> Model .

(* TODO: prefix? -> needed for def of complete execution paths *)
Parameter Path_eq_dec : Path -> Path -> Prop .
Definition isPrefix (p : Path) (P : Path) := exists i, Path_eq_dec (PathTo P i) p .

(* proper prefix! *)
Definition complete (P : Path) := forall p : Path, not (isPrefix P p) .

Definition StartsFrom (tau : Path) (rho : Valuation) (phi : MLFormula) :=
  Satisfies (nth tau 0) rho phi .


(* All Paths Reachability Satisfaction *)

Inductive APRLFormula := rl : MLFormula -> MLFormula -> APRLFormula .
Notation "L ==> R" := (rl L R) (at level 100).
Fixpoint Lhs (r : APRLFormula) := match r with (L ==> _) => L end . 
Fixpoint Rhs (r : APRLFormula) := match r with (_ ==> R) => R end . 

Parameter isInfinite : Path -> Prop .
Parameter infiniteIsComplete : forall p : Path, isInfinite p -> complete p .


(* (tau, rho) |= phi ==> phi' *)
Definition entails (tau : Path) (rho : Valuation) (F : APRLFormula) :=
  (StartsFrom tau rho (Lhs F)) ->
  (or (exists i, Satisfies (nth tau i) rho (Rhs F))
      (isInfinite tau)).

(* =>S |= phi ==> phi' *)
Definition entailsTS (TS : RLSystem -> Model -> Model -> Prop) (F : APRLFormula)
  := forall (tau : Path), forall (rho : Valuation),
       (StartsFrom tau rho (Lhs F)) -> (entails tau rho F) .


(* Semantics for phi ==> phi' *)
Definition sem (F: APRLFormula) :=
  { tau : Path & (exists (rho : Valuation), entails tau rho F) } .


(* S-Derivative *)
Definition SDerivative (phi phi' phi1 : MLFormula) :=
  forall (tau1 : Path), forall (rho : Valuation),
    (entails tau1 rho (phi1 ==> phi')) ->
    (exists (tau : Path),
       entails tau rho (phi ==> phi') /\ (Path_eq_dec tau1 (PathFrom tau 1))).

(* Proper S-Derivative *)
Definition ProperSDerivative (phi phi' phi1 : MLFormula) :=
  SDerivative phi phi' phi1 /\ not (Empty_set = sem (phi ==> phi')).

(* S-Derivable *)
Definition SDerivable (F : APRLFormula) :=
  exists (phi1 : MLFormula), ProperSDerivative (Lhs F) (Rhs F) phi1 .

(* Complete *)
(*
Definition complete (Delta : Set) := 
 *)

(* FOL encoding *)
Definition fol (phi : MLFormula) := 