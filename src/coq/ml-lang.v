Require Import ml.
Require Import symbolic.
Require Import lang.
Require Import String.
Require Import Classical.
Require Import List.

Module LangML <: Formulas.
  Import Lang.
  Import Symbolic.
  
 (* Definition State : Type := _cfg.*)
  Inductive Model :Type := 
  | _nat_to_m : _nat -> Model 
  | _bool_to_m : _bool -> Model
  | _mapitem_to_m : _mapitem -> Model
  | _map_to_m : _map -> Model
  | _cfg_to_m : _cfg -> Model
  | _stmt_to_m : _stmt -> Model.

  Definition Var := string.

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
    | T : MLFormulaHelper
    | pattern: Cfg -> MLFormulaHelper 
    | pred: BExp -> MLFormulaHelper
    | notML : MLFormulaHelper -> MLFormulaHelper 
    | AndML : MLFormulaHelper -> MLFormulaHelper -> MLFormulaHelper 
    | ExistsML : list Var -> MLFormulaHelper -> MLFormulaHelper.
  Definition MLFormula : Type := MLFormulaHelper.

  Eval compute in T .
  Open Scope string_scope.
  Eval compute in (ExistsML (cons "a" nil) (pred (le (id "a") (id "b")))).

  Definition varTo_nat (v : Var) : _nat := s_nat (v ++ "_gen").

  Fixpoint varsTo_nat (Vs : list Var) : list _nat :=
    match Vs with 
      | nil => nil
      | v :: vs => (varTo_nat v) :: (varsTo_nat vs)
    end.

  Eval compute in varsTo_nat (cons "a" nil).

  Fixpoint substBoundedAExp (v : Var) (A : AExp) : AExp :=
    match A with 
      | aexp_var v' => if (var_eq v v') then sval (varTo_nat v) else (aexp_var v')
      | plus E E' => plus (substBoundedAExp v E) (substBoundedAExp v E')
      | div E E' => div (substBoundedAExp v E) (substBoundedAExp v E')
      | mod E E' => mod (substBoundedAExp v E) (substBoundedAExp v E')
      | E => E
    end.

  Eval compute in var_eq "a" "a" .
  Eval compute in var_eq "a" "b" .
  Eval compute in substBoundedAExp "a" (plus (aexp_var "a") (id "b")) .

  Fixpoint substBoundedBExp (v : Var) (B : BExp) : BExp := 
    match B with 
      | le A A' => le (substBoundedAExp v A)  (substBoundedAExp v A') 
      | leq A A' => leq  (substBoundedAExp v A)  (substBoundedAExp v A') 
      | B' => B'
    end.

  Eval compute in substBoundedBExp "a" (le (plus (aexp_var "a") (id "b")) (sval ($ "a"))).

  Fixpoint substBoundedStmt (v : Var) (St : Stmt) : Stmt := 
    match St with 
      | assign X AE => assign X (substBoundedAExp v AE)
      | ifelse B S1 S2 => ifelse (substBoundedBExp v B) (substBoundedStmt v S1) (substBoundedStmt v S2) 
      | while B S1 => while (substBoundedBExp v B) (substBoundedStmt v S1)
      | seq S1 S2 => seq (substBoundedStmt v S1) (substBoundedStmt v S2)
      | stmt_var Ss => stmt_var Ss 
    end.

  Eval compute in substBoundedStmt "a" (assign "x" (plus (aexp_var "a") (id "b"))).

  Fixpoint substBoundedMapItem (v : Var) (m : MapItem) : MapItem :=
    match m with
      | (X, A) => (X, substBoundedAExp v A)
    end.

  Fixpoint substBoundedMap (v : Var) (M : Mem) : Mem :=
    match M with
      | nil => nil 
      | m :: ms => (substBoundedMapItem v m) :: (substBoundedMap v ms) 
    end.


  Fixpoint substBounded (v : Var) (F : MLFormula) : MLFormula := 
    match F with 
      | T => T 
      | pattern (St, M) => pattern ((substBoundedStmt v St), (substBoundedMap v M))
      | pred B => pred (substBoundedBExp v B)
      | notML F' => notML (substBounded v F') 
      | AndML F1 F2 => AndML (substBounded v F1) (substBounded v F2)
      | ExistsML Vs F' => if (in_dec string_dec  v Vs) then (ExistsML Vs F') else (ExistsML Vs (substBounded v F')) 
    end.

  Fixpoint substBoundedVs (vs : list Var) (F : MLFormula) : MLFormula := 
    match vs with 
      | nil => F 
      | x :: xs => substBoundedVs xs (substBounded x F)
    end.

  Eval compute in substBounded "a" T .
  Check pattern ("a" ::= (sval (# 10)) , cons ("a" |-> (sval (# 12))) nil) .
  Eval compute in substBounded "x" (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "x")) nil)) .
  Eval compute in substBounded "x" (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "x")) nil))) .  
  Eval compute in substBounded "y" (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "y")) nil))) .
  Eval compute in substBounded "x" (AndML 
                                      (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "x")) nil)))
                                      (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "y")) nil)))) .
  Eval compute in substBounded "y" (AndML 
                                      (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "x")) nil)))
                                      (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "y")) nil)))) .
  Eval compute in substBoundedVs ("x"::"y"::nil) (AndML 
                                      (ExistsML (cons "x" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "y")) nil)))
                                      (ExistsML (cons "z" nil) (pattern ("a" ::= (aexp_var "x") , cons ("a" |-> (aexp_var "y")) nil)))) .


  Parameter applyValToBExp : Valuation -> BExp -> _bool.
  Parameter applyValToStmt : Valuation -> Stmt -> _stmt.
  Parameter applyValToMem : Valuation -> Mem-> _map.

  Fixpoint applyVal (rho : Valuation) (phi : MLFormula) : Model := 
    match phi with 
      | T => (_bool_to_m (c_bool true))
      | pattern (St, M) => _cfg_to_m ((applyValToStmt rho St), (applyValToMem rho M))
      | pred B => _bool_to_m (applyValToBExp rho B)
      | notML F => match (applyVal rho F) with 
                     | _bool_to_m B' =>  (_bool_to_m (_not  B'))
                     | _ => (_bool_to_m (c_bool false))
                   end
      | AndML F F' => match (applyVal rho F), (applyVal rho F') with
                        | _bool_to_m B1, _bool_to_m B2 => (_bool_to_m (_and B1 B2))
                        | _, _ => (_bool_to_m (c_bool false))
                      end
      | ExistsML Vs F => match (applyVal rho (substBoundedVs Vs F)) with
                           | _bool_to_m B' => (_bool_to_m (_exists (varsTo_nat Vs) B'))
                           | _ => (_bool_to_m (c_bool false))
                         end
    end.


  Fixpoint applyValToBExp (rho : Valuation) (B : BExp) : Model :=
    match B with 
      | bexp_var v => rho v
      | not B' => not (
    end.

  Fixpoint applyValToAExp (rho : Valuation) (A : AExp) : _nat :=
    match A with 
      | aexp_var v => rho v
      | _ => (c_nat 0)
    end.



  Inductive SatML (gamma : State) (rho : Valuation) (phi : MLFormula) : Prop :=
  | satML : rho phi = gamma -> SatML gamma rho phi .
  
End LangML.