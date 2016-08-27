Require Import List.
Require Import Classical.
Require Import Omega.

Module Type Formulas.
  Import ListNotations.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Var : Type .
  Definition Valuation : Type := Var -> Model .

  (* variable equalitiy *)
  Parameter var_eq : Var -> Var -> bool .
  Axiom var_eq_true : forall x y, var_eq x y = true <-> x = y .
  Axiom var_eq_false : forall x y, var_eq x y = false <-> x <> y .
  Axiom var_eq_refl : forall x, var_eq x x = true .
  
  (* ML syntax - axiomatisation *)
  Parameter MLFormula : Type .
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .
  Parameter ImpliesML : MLFormula -> MLFormula ->  MLFormula.

  (* ML semantics - axiomatisation *)
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

  Axiom SatML_Implies :
    forall gamma rho phi phi',
      SatML gamma rho (ImpliesML phi phi') <->
      (SatML gamma rho phi -> SatML gamma rho phi').

  (* Validity in ML *)
  Definition ValidML (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.

  
  (* Free variables *)
  Parameter getFreeVars : MLFormula -> list Var .

  (* existential closure *)
  Definition EClos (phi : MLFormula) :=
    (ExistsML (getFreeVars phi) phi).

  (* Encoding *)
  Parameter encoding : MLFormula -> MLFormula .
  
  (* Encoding main property *)
  Axiom Proposition1 :
    forall phi gamma' rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.

  
  
  (* Modify valuation on set *)
  Definition modify_val_on_var(rho rho' : Valuation) (x : Var) : Valuation :=
    fun z => if (var_eq x z) then rho' x else rho z .
  Fixpoint modify_val_on_set(rho rho' : Valuation) (X : list Var) : Valuation :=
    match X with
      | nil => rho
      | cons x Xs => modify_val_on_var (modify_val_on_set rho rho' Xs) rho' x
    end.

  (* helper *)
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
    

  (* helper *)
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

  
  Axiom modify_Sat1 :
    forall phi V gamma rho rho',
      SatML gamma rho' phi ->
      incl (getFreeVars phi) V ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  
  Axiom modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
    
End Formulas.
