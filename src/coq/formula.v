Require Import List.

Module Type Formulas.
  Import ListNotations.

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

  Axiom SatML_Exists :
    forall phi gamma rho V,
      SatML gamma rho (ExistsML V phi) <->
      exists rho',
        (forall v, ~In v V -> rho v = rho' v) /\
        SatML gamma rho' phi.

  Axiom SatML_And :
    forall gamma rho phi phi',
      SatML gamma rho (AndML phi phi') <->
      SatML gamma rho phi /\ SatML gamma rho phi'.

  Axiom SatML_Not :
    forall gamma rho phi,
      SatML gamma rho (NotML phi) <-> ~ SatML gamma rho phi.
  
  Definition ValidML (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.
  Definition SatisfiableML (phi : MLFormula) : Prop :=
    exists gamma rho, SatML gamma rho phi .

  (* Free variables *)
  Parameter FreeVars : list MLFormula -> list Var .

  
  Definition modify_val_on_set :
    Valuation -> Valuation -> list Var -> Valuation .
  Admitted.
  Axiom modify_1 :
    forall x V rho rho',
      In x V -> (modify_val_on_set rho rho' V) x = rho' x.
  Axiom modify_2 :
    forall x V rho rho',
      ~ In x V -> (modify_val_on_set rho rho' V) x = rho x.
  Axiom modify_Sat1 :
    forall gamma rho rho' phi V,
      SatML gamma rho' phi ->
      (forall x, In x (FreeVars [phi]) -> In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Axiom modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (FreeVars [phi]) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.

  Axiom in_FreeVars_iff :
    forall x phi tl,
      In x (FreeVars (phi::tl)) <-> In x (FreeVars [phi]) \/ In x (FreeVars tl).

  
  (* encoding: ML -> FOL *)
  (* Parameter encoding : MLFormula -> FOLFormula . *)
  Parameter encoding : MLFormula -> MLFormula .

  (* encoding properties *)
  (* 
    The following proposition, looks cleaner when 
    working with both FOL and ML:
    Axiom SatFOL_iff_SatML :
    forall phi rho,
      SatFOL rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
   *)
  Axiom Proposition1 :
    forall gamma' phi rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.

  
  
  Axiom enc_sat :
    forall gamma rho phi,
      SatML gamma rho (encoding phi) <->
      SatML gamma rho phi.
  
  (* FOL as ML *)
  (* Parameter injectFOL : FOLFormula -> MLFormula . *)
    
End Formulas.
