Require Import List.
Require Import Classical.
Require Import Omega.

Module Type Formulas.
  Import ListNotations.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Definition Valuation : Type := Var -> Model .

  Parameter var_eq : Var -> Var -> bool .
  Axiom var_eq_true : forall x y, var_eq x y = true <-> x = y .
  Axiom var_eq_false : forall x y, var_eq x y = false <-> x <> y .
  Axiom var_eq_refl : forall x, var_eq x x = true .
  
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


  
  (* Free variables *)
  Parameter getFreeVars : MLFormula -> list Var .

  Axiom freeVars_ExistsML :
    forall phi x X,
      In x (getFreeVars (ExistsML X phi)) <->
      In x (getFreeVars phi) /\ ~ In x X .

  Axiom freeVars_AndML :
    forall phi phi' x,
      In x (getFreeVars (AndML phi phi')) <->
      In x (getFreeVars phi) \/ In x (getFreeVars phi').

  
  (* Modify valuation on set *)
  Definition modify_val_on_var(rho rho' : Valuation) (x : Var) : Valuation :=
    fun z => if (var_eq x z) then rho' x else rho z .

  Fixpoint modify_val_on_set(rho rho' : Valuation) (X : list Var) : Valuation :=
    match X with
      | [] => rho
      | x :: Xs => modify_val_on_var (modify_val_on_set rho rho' Xs) rho' x
    end.
  
  Lemma modify_in :
    forall V x rho rho',
      In x V -> (modify_val_on_set rho rho' V) x = rho' x.
  Proof.
    induction V; intros.
    - contradiction.
    - simpl in *.
      destruct H as [H | H].
      + subst a.
        unfold modify_val_on_var.
        rewrite var_eq_refl.
        reflexivity.
      + unfold modify_val_on_var.
        case_eq (var_eq a x); intros H'.
        * apply var_eq_true in H'.
          subst a.
          reflexivity.
        * apply IHV; trivial.
  Qed.
    
  
  Lemma modify_not_in :
    forall V x rho rho',
      ~ In x V -> (modify_val_on_set rho rho' V) x = rho x.
  Proof.
    induction V; intros.
    - simpl.
      reflexivity.
    - simpl in *.
      apply not_or_and in H.
      destruct H as (H & H').
      unfold modify_val_on_var.
      case_eq (var_eq a x); intros H''.
      + apply var_eq_true in H''.
        subst a.
        contradict H.
        reflexivity.
      + apply IHV; trivial.
  Qed.

  
  Lemma modify_Sat1 :
    forall phi V gamma rho rho',
      SatML gamma rho' phi ->
      incl (getFreeVars phi) V ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Proof.
  Admitted.
  
  Lemma modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Admitted.
  
  
  
  (* encoding: ML -> FOL *)
  (* Parameter encoding : MLFormula -> FOLFormula . *)
  Parameter encoding : MLFormula -> MLFormula .

  Axiom freeVars_encoding :
    forall phi x,
      In x (getFreeVars (encoding phi)) <-> In x (getFreeVars phi) .
    
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
  
End Formulas.
