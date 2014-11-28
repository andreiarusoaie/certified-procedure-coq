Require Import ZArith.

(* These are language dependent *)
Parameter Term : Set .
Parameter Id : Set .

(* Variables - I'm not sure this is the best solution now *)
Inductive Var : Set := varF : Z -> Var .

(* Matching logic formulas *)
Inductive Formula : Set :=
  | basic_pattern : Term -> Formula
  | andF : Formula -> Formula -> Formula
  | orF : Formula -> Formula -> Formula
  | notF : Formula -> Formula
  | impliesF : Formula -> Formula -> Formula 
  | existsF : Var -> Formula -> Formula
.

(* Rules = Reachability Logic formulas *)
Inductive Rule : Set := rule : Formula -> Formula -> Rule .
Notation "L => R" := (rule L R) (at level 100).

(* Reachability rules system *)
Definition System := Rule -> Prop .
