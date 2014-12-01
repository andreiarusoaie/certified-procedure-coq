Require Import ZArith.
Require Import FMapPositive.


Module Type TERM .
  Parameter Term : Type .
End TERM. 


Module MLFormula (M : TERM).
  Import M.
  
  (* Variables - ??? *)
  Inductive Var : Set := varF : Z -> Var .

  (* Matching logic formulas *)
  Inductive Formula : Type :=
    | bp : Term -> Formula
    | T : Formula 
    | andF : Formula -> Formula -> Formula
    | orF : Formula -> Formula -> Formula
    | notF : Formula -> Formula
    | impliesF : Formula -> Formula -> Formula 
    | existsF : Var -> Formula -> Formula
  .

  (* Rules = Reachability Logic formulas *)
  Inductive Rule : Type := rule : Formula -> Formula -> Rule .
  Notation "L => R" := (rule L R) (at level 100).
  
  (* Reachability rules system *)
  Definition System := Rule -> Prop .
End MLFormula.
