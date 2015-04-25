Require Import List.

Module Type Formulas.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Definition Valuation : Type := Var -> Model .


  (* FOL *)
  Parameter FOLFormula : Type .
  Parameter TrueFOL : FOLFormula .
  Parameter NotFOL : FOLFormula -> FOLFormula .
  Parameter AndFOL : FOLFormula -> FOLFormula -> FOLFormula .
  Parameter ExistsFOL : list Var -> FOLFormula -> FOLFormula .

  (* FOL satisfaction *)
  Parameter SatFOL : Valuation -> FOLFormula -> Prop .
  
  (* ML *)
  Parameter MLFormula : Type .
  Parameter TrueML : MLFormula .
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter NotML : MLFormula -> MLFormula.
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .
  Definition ImpliesML (phi phi' : MLFormula) : MLFormula :=
    NotML (AndML phi (NotML phi')) .

  (* ML satisfaction *)
  Parameter SatML : State -> Valuation -> MLFormula -> Prop .
  Definition ValidML (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.
  
  (* Free variables *)
  Parameter FreeVars : list MLFormula -> list Var .
  
  (* encoding: ML -> FOL *)
  Parameter encoding : MLFormula -> FOLFormula .

  (* FOL as ML *)
  Parameter injectFOL : FOLFormula -> MLFormula .
    
End Formulas.
