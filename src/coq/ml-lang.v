Require Import ml.
Require Import symbolic.
Require Import lang.
Require Import String.
Require Import Classical.

Module LangML <: Formulas.
  Import Lang.
  Import Symbolic.
  
 (* Definition State : Type := _cfg.*)
  Inductive Model :Type := 
  | s_nat : _nat -> Model 
  | s_bool : _bool -> Model
  | s_mapitem : _mapitem -> Model
  | s_map : _map -> Model
  | s_cfg : _cfg -> Model
  | s_stmt : _stmt -> Model
.

  Definition Var := (string * Type)%type.

  Definition Valuation : Type := Var -> Model. 

  Definition var_eq (X Y : Var) : bool := if (string_dec X Y) then true else false .

  Lemma var_eq_true : 
    forall x y, var_eq x y = true <-> x = y .
  Proof.
    intros x y.
    split; intros H.
    - unfold var_eq in H.
      case_eq (string_dec x y); intros H' He; rewrite He in *; trivial.
      inversion H.
    - rewrite H.
      clear H.
      unfold var_eq.
      induction y.
      + simpl; trivial.
      + case_eq (string_dec (String a y) (String a y)).
        * intros e He; trivial.
        * intros n Hn.
          contradiction n; trivial.
  Qed.

  Lemma var_eq_false : 
    forall x y, var_eq x y = false <-> x <> y .
  Proof.
    intros x y.
    split; intros H.
    - intros H'.
      contradict H.
      rewrite <- var_eq_true in H'.
      rewrite H'.
      intros H''.
      inversion H''.
    - unfold var_eq.
      case_eq (string_dec x y).
      + intros e He.
        contradiction.
      + intros e He; trivial.
  Qed.
        
  Lemma var_eq_refl : 
    forall x, var_eq x x = true .  
  Proof.
    intros x; apply var_eq_true; trivial.
  Qed.

  Inductive MLFormulaHelper : Type :=
    | pattern: Cfg -> MLFormulaHelper 
    | pred: BExp -> MLFormulaHelper
    | notML : MLFormulaHelper -> MLFormulaHelper 
    | AndML : MLFormulaHelper -> MLFormulaHelper -> MLFormulaHelper 
    | ExistsML : MLFormulaHelper -> MLFormulaHelper .
  Definition MLFormula : Type := MLFormulaHelper .



  Fixpoint applyVal (rho : Valuation) (phi : MLFormula) : State := 
    match phi with 
      | 

  Inductive SatML (gamma : State) (rho : Valuation) (phi : MLFormula) : Prop :=
  | satML : rho phi = gamma -> SatML gamma rho phi .
  
End LangML.