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
(*  Definition SatisfiableML (phi : MLFormula) : Prop :=
    exists gamma rho, SatML gamma rho phi . *)

  (* Free variables *)
  Parameter getFreeVars : MLFormula -> list Var .
  
  
  Parameter modify_val_on_set :
    Valuation -> Valuation -> list Var -> Valuation .
  
  Axiom modify_1 :
    forall x V rho rho',
      In x V -> (modify_val_on_set rho rho' V) x = rho' x.
  Axiom modify_2 :
    forall x V rho rho',
      ~ In x V -> (modify_val_on_set rho rho' V) x = rho x.

  Axiom modify_Sat1 :
    forall gamma rho rho' phi V,
      SatML gamma rho' phi ->
      (forall x, In x (getFreeVars phi) -> In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Axiom modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.



    (* renaming *)
  Parameter rename_var : Var -> Var -> MLFormula -> MLFormula.
  Axiom renamed_removed :
    forall x y phi,
      ~ In x (getFreeVars (rename_var x y phi)).

  Axiom rename_sat :
    forall gamma rho phi x y,
      SatML gamma rho phi <->
      SatML gamma rho (rename_var x y phi) .

  Axiom free_rename:
    forall z x y phi,
      In z (getFreeVars (rename_var x y phi)) ->
      y = z \/ (x <> z /\ In z (getFreeVars phi)).
  
  
  Fixpoint rename_vars (X Y : list Var)
           (phi : MLFormula) : MLFormula :=
    match X, Y with
      | x :: Xs, y :: Ys =>
        rename_var x y (rename_vars Xs Ys phi)
      | _, _ => phi
    end.

  Lemma rename_sat_Set :
    forall gamma rho phi X Y,
      SatML gamma rho phi <->
      SatML gamma rho (rename_vars X Y phi) .
  Admitted.

  Axiom rename_And :
    forall phi phi' X Y,
      rename_vars X Y (AndML phi phi') =
      (AndML (rename_vars X Y phi) (rename_vars X Y phi')).

  Axiom rename_Not :
    forall phi X Y,
      rename_vars X Y (NotML phi) =
      (NotML (rename_vars X Y phi)).

  
  Parameter generate_var_not_in_set : Var -> list Var -> Var .
  Axiom new_var_not_in_set :
    forall X x,
       ~ In (generate_var_not_in_set x X) X.

  Fixpoint generate_vars (Vs X : list Var) : list Var :=
    match Vs with
      | nil => nil
      | v :: V =>
        (generate_var_not_in_set v X) :: generate_vars V X
    end.

  Axiom rename_exists_sat :
    forall X Y gamma rho phi,
      SatML gamma rho (ExistsML X phi) <->
      SatML gamma rho (ExistsML (generate_vars X Y)
                                (rename_vars X (generate_vars X Y) phi)).

  Lemma generated_free :
    forall Y x phi,
      In x (getFreeVars (rename_vars (getFreeVars phi) Y phi)) ->
      In x Y .
    Admitted.
  
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
  

  Axiom rename_encoding :
    forall phi X Y,
      rename_vars X Y (encoding phi) =
      (encoding (rename_vars X Y phi)).

  
End Formulas.
