Require Import List.

Module Type Formulas.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Definition Valuation : Type := Var -> Model .


  (* FOL *)
  (*
  Parameter FOLFormula : Type .
  Parameter TrueFOL : FOLFormula .
  Parameter NotFOL : FOLFormula -> FOLFormula .
  Parameter AndFOL : FOLFormula -> FOLFormula -> FOLFormula .
  Parameter ExistsFOL : list Var -> FOLFormula -> FOLFormula .

  Definition OrFOL (phi phi' : FOLFormula) : FOLFormula :=
    NotFOL (AndFOL (NotFOL phi) (NotFOL phi')) .

  Definition BigOrFOL (l : list FOLFormula) : FOLFormula :=
    fold_left OrFOL l (NotFOL TrueFOL) .
   *)
  (* FOL satisfaction *)
  (*
  Parameter SatFOL : Valuation -> FOLFormula -> Prop .
  Definition ValidFOL (phi : FOLFormula) : Prop :=
    forall rho, SatFOL rho phi.
  Definition SatisfiableFOL (phi : FOLFormula) : Prop :=
    exists rho, SatFOL rho phi .
  *)
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
  Definition SatisfiableML (phi : MLFormula) : Prop :=
    exists gamma rho, SatML gamma rho phi .

  (* Free variables *)
  Parameter FreeVars : list MLFormula -> list Var .
  
  (* encoding: ML -> FOL *)
  (* Parameter encoding : MLFormula -> FOLFormula . *)
  Parameter encoding : MLFormula -> MLFormula .

  (* encoding properties *)
  (* Axiom SatFOL_iff_SatML :
    forall phi rho,
      SatFOL rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
   *)

  Axiom enc_sat :
    forall gamma rho phi,
      SatML gamma rho (encoding phi) <->
      SatML gamma rho phi.
  
  (* FOL as ML *)
  (* Parameter injectFOL : FOLFormula -> MLFormula . *)
    
End Formulas.
