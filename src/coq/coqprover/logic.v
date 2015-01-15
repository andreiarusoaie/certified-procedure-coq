
Parameter Var : Set .

Parameter CfgTerm : Set .

Parameter VarToTerm : Var -> Term.

Coercion VarToTerm : Var >-> Term.


(* helpers *)
Parameter isVariable : Term -> Prop .

(* Variables *)
(* Definition Var := { x : Term & (isVariable x) }. *)


(* Matching Logic Formulas = MLFormula *)
Inductive MLFormula :=
  | T : MLFormula
  | Bp : Term -> MLFormula
  | Not : MLFormula -> MLFormula
  | And : MLFormula -> MLFormula -> MLFormula
  | Or : MLFormula -> MLFormula -> MLFormula
  | Implies : MLFormula -> MLFormula -> MLFormula
  | Exists : Var -> MLFormula -> MLFormula
.

(* Model and Valuation *)
Parameter Model : Set .
Parameter Valuation : Set (* Var -> Model *) .


(* Satisfaction relation*)
Parameter Satisfies : Model -> Valuation -> MLFormula -> Prop .


(* Reachability Logic Formulas = RLFormula *)

Definition RLFormula := (MLFormula * MLFormula)%type .

Notation "L => R" := (L, R) (at level 100).

Definition RLSystem := RLFormula -> Prop .

(* Transition system *)
Definition TS (S : RLSystem) (gamma : Model) (gamma' : Model) :=
  exists F : RLFormula, exists rho : Valuation,
                          (S F /\ Satisfies gamma rho (fst F) /\ Satisfies gamma' rho (snd F)).
