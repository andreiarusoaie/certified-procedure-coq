Require Import term.
Require Import fol.


Parameter Cfg : Type .

Parameter CfgToTerm : Cfg -> Term .
Coercion CfgToTerm : Cfg >-> Term .

(* helpers *)
Parameter isVariable : Term -> Prop .
Parameter Cfg_eq_dec : Cfg -> Cfg -> Prop .


(* Matching Logic Formulas = MLFormula *)
Inductive MLFormula :=
  | T : MLFormula
  | Bp : Cfg -> MLFormula
  | Fol : FOLFormula -> MLFormula 
  | Not : MLFormula -> MLFormula
  | And : MLFormula -> MLFormula -> MLFormula
  | Or : MLFormula -> MLFormula -> MLFormula
  | Implies : MLFormula -> MLFormula -> MLFormula
  | Exists : Var -> MLFormula -> MLFormula
.

(* Model and Valuation *)
Parameter Model : Type .
Parameter Valuation : Type (* Var -> Model *) .


(* Satisfaction relation*)
Parameter Satisfies : Model -> Valuation -> MLFormula -> Prop .


(* Reachability Logic Formulas = RLFormula *)

Definition RLFormula := (MLFormula * MLFormula)%type .
Notation "L => R" := (L, R) (at level 100).
Notation lhs := fst.
Notation rhs := snd.

Definition RLSystem := RLFormula -> Prop .

(* Transition system *)
Definition TS (S : RLSystem) (gamma : Model) (gamma' : Model) :=
  exists F : RLFormula, exists rho : Valuation,
                          (S F /\ Satisfies gamma rho (lhs F) /\ Satisfies gamma' rho (rhs F)).
