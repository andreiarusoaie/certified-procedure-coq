Require Import ml.
Require Import symbolic.
Require Import lang.
Require Import String.
Require Import Classical.
Require Import List.

Module LangML <: Formulas.
  Import Lang.
  Import Symbolic.
  
  Definition State : Type := _cfg.
  Inductive Model : Type := 
    | to_m_f : _f -> Model 
    | to_m_bool : _bool -> Model
    | to_m_nat : _nat -> Model
    | to_m_map : _map -> Model
    | to_m_mapitem : _mapitem -> Model
    | to_m_cfg : _cfg -> Model.

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
    | NotML : MLFormulaHelper -> MLFormulaHelper 
    | AndML : MLFormulaHelper -> MLFormulaHelper -> MLFormulaHelper 
    | ExistsML : list Var -> MLFormulaHelper -> MLFormulaHelper
    | enc : MLFormulaHelper -> MLFormulaHelper .
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
      | aexp_var v' => if (var_eq v v') then val (varTo_nat v) else (aexp_var v')
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

  Eval compute in substBoundedBExp "a" (le (plus (aexp_var "a") (id "b")) (val ($ "a"))).

  Fixpoint substBoundedStmt (v : Var) (St : Stmt) : Stmt := 
    match St with 
      | assign X AE => assign X (substBoundedAExp v AE)
      | ifelse B S1 S2 => ifelse (substBoundedBExp v B) (substBoundedStmt v S1) (substBoundedStmt v S2) 
      | while B S1 => while (substBoundedBExp v B) (substBoundedStmt v S1)
      | seq S1 S2 => seq (substBoundedStmt v S1) (substBoundedStmt v S2)
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
      | NotML F' => NotML (substBounded v F') 
      | AndML F1 F2 => AndML (substBounded v F1) (substBounded v F2)
      | ExistsML Vs F' => if (in_dec string_dec  v Vs) then (ExistsML Vs F') else (ExistsML Vs (substBounded v F')) 
      | enc F' => enc (substBounded v F')
    end.

  Fixpoint substBoundedVs (vs : list Var) (F : MLFormula) : MLFormula := 
    match vs with 
      | nil => F 
      | x :: xs => substBoundedVs xs (substBounded x F)
    end.

  Eval compute in substBounded "a" T .
  Check pattern ("a" ::= (val (# 10)) , cons ("a" |-> (val (# 12))) nil) .
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

  Eval compute in "a" ::= plus (id "a")  (val (c_nat 3)).


  Fixpoint applyValToAExp (rho : Valuation) (A : AExp) : option _nat :=
    match A with
      | aexp_var v => match (rho v) with 
                        | to_m_nat n => Some n
                        | _ => None
                      end
      | id s => Some (s_nat s)
      | val s => Some s
      | plus A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with
                        | Some a1, Some a2 => Some (_plus a1 a2)
                        | _, _ => None
                      end
      | div A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with
                        | Some a1, Some a2 => Some (_div a1 a2)
                       | _, _ => None
                     end
      | mod A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with
                        | Some a1, Some a2 => Some (_mod a1 a2)
                       | _, _ => None
                     end
      end.


  Definition testVal (v : Var) : Model :=
    if var_eq v "x" then to_m_nat (c_nat 2) else to_m_nat (c_nat 0).

  Eval compute in applyValToAExp testVal ( plus (aexp_var "x")  (aexp_var "y")) .

  Fixpoint applyValToBExp (rho : Valuation) (B:BExp) : option _bool := 
    match B with 
      | bval B' => Some B'
      | not B' => match (applyValToBExp rho B') with 
                    | Some b => Some (_not b)
                    | _ => None 
                  end
      | and B1 B2 => match applyValToBExp rho B1, applyValToBExp rho B2 with
                       | Some b1, Some b2 => Some (_and b1 b2)
                       | _, _ => None
                     end
      | le A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with 
                      | Some a1, Some a2 => Some (_le a1 a2)
                      | _, _ => None
                    end
      | leq A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with 
                       | Some a1, Some a2 => Some (_leq a1 a2)
                       | _, _ => None
                     end
      | eq A1 A2 => match applyValToAExp rho A1, applyValToAExp rho A2 with 
                      | Some a1, Some a2 => Some (_eq a1 a2)
                      | _, _ => None
                    end
    end.

  Eval compute in applyValToBExp testVal ( leq (aexp_var "x")  (aexp_var "y")) .

  Fixpoint applyValToMemItem (rho : Valuation) (M : MapItem) : option _mapitem :=
    match M with
      | (X, A) => match (applyValToAExp rho A) with 
                    | Some e =>  Some (X, e)
                    | None => None 
                  end
    end.

  Fixpoint applyValToMem (rho : Valuation) (M : Mem) : option _map :=
    match M with
      | nil => Some nil
      | x :: xs => match (applyValToMemItem rho x), (applyValToMem rho xs) with 
                     | Some e, Some es => Some (e :: es)
                     | _, _ => None 
                   end
    end.

  Eval compute in applyValToMem testVal (( "y" |-> (aexp_var "x")  ) :: nil) .
  Eval compute in applyValToMem testVal (( "y" |-> (aexp_var "z")  ) :: nil) .

  Fixpoint applyValToStmt (rho : Valuation) (St :  Stmt) : option _stmt :=
    match St with 
      | assign s e => match applyValToAExp rho e with
                        | Some v => Some (_assign s v)
                        | _ => None
                      end
      | ifelse b s1 s2 => match applyValToBExp rho b, 
                                applyValToStmt rho s1, 
                                applyValToStmt rho s2 with
                            | Some b', Some s1', Some s2' => 
                              Some (_ifelse b' s1' s2')
                            | _, _, _ => None
                          end
      | while b s => match applyValToBExp rho b, applyValToStmt rho s with
                       | Some b', Some s' => Some (_while b' s')
                       | _, _ => None
                     end
      | seq s1 s2 => match applyValToStmt rho s1, applyValToStmt rho s2 with
                       | Some s1', Some s2' => Some (_seq s1' s2')
                       | _, _ => None 
                     end 
    end.

  
  Eval compute in "i" ::= plus (id "i") (val (c_nat 1)) .
  Eval compute in "s" ::= plus (id "s") (id "i") .
  Eval compute in seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i")). 
  Eval compute in (leq (id "i") (id "n")).
  Eval compute in while (leq (id "i") (id "n"))
                        (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i"))).
  Definition testVal' (v : Var) : Model :=
    if var_eq v "n" then to_m_nat (c_nat 10) else to_m_nat (c_nat 0).

  Eval compute in applyValToStmt testVal' 
                           (while (leq (id "i") (id "n"))
                        (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i")))).

  Eval compute in applyValToStmt testVal' 
                           (while (leq (id "i") (aexp_var "n"))
                        (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i")))).


  Fixpoint size (F : MLFormula) : nat := 
    match F with
      | NotML F' => Datatypes.S (size F')
      | AndML F1 F2 => (size F1) + (size F2)
      | ExistsML Vs F' => Datatypes.S (size F')
      | _ => 1
    end.
                     


  Fixpoint applyVal (n : nat) (rho : Valuation) (phi : MLFormula) : option _f := 
    match n with
      | 0 => None
      | S n' =>
        match phi with 
          | T => Some _f_t
          | pattern (St, M) => 
            match (applyValToStmt rho St), (applyValToMem rho M) with 
              | Some s, Some m => Some (_f_cfg (s, m))
              | _, _ => None 
            end
          | pred B => match (applyValToBExp rho B) with 
                        | Some b => Some (_f_pred b)
                        | _ => None
                      end
          | NotML F => match (applyVal n' rho F) with
                         | Some f => Some (_f_not f)
                         | _ => None
                       end
          | AndML F F' => match (applyVal n' rho F), (applyVal n' rho F') with
                            | Some f, Some f' => Some (_f_and f f')
                            | _, _ => None 
                          end
          | ExistsML Vs F => let (F', vs) := ((substBoundedVs Vs F), (varsTo_nat Vs)) in 
                             match (applyVal n' rho F') with 
                               | Some f => Some (_f_exists vs f)
                               | _ => None
                             end
          | enc F => match (applyVal n' rho F) with
                            | Some f => Some (_f_not f)
                            | _ => None
                          end
        end
    end.
  
  Fixpoint SatML (gamma : State)(rho : Valuation)(phi : MLFormula) : Prop :=
    match phi with
      | T => True
      | pattern (St, M) => applyVal (size phi) rho phi = Some (_f_cfg gamma)
      | pred B => applyValToBExp rho B = Some (c_bool true)
      | NotML phi' => ~ SatML gamma rho phi'
      | AndML phi1 phi2 => SatML gamma rho phi1 /\ SatML gamma rho phi2
      | ExistsML V phi' =>  exists rho', (forall v, ~In v V -> rho v = rho' v) /\ SatML gamma rho' phi'
      | enc phi' => exists gamma', SatML gamma' rho phi'
  end.

  Lemma SatML_Exists :
    forall phi gamma rho V,
      SatML gamma rho (ExistsML V phi) <->
      exists rho',
        (forall v, ~In v V -> rho v = rho' v) /\
        SatML gamma rho' phi.
  Proof.
  intros; split; intros.
  - simpl in H.
    destruct H as (rho' & (H1 & H2)).
    exists rho'.
    split; trivial.
  - simpl.
    destruct H as (rho' & (H1 & H2)).
    exists rho'.
    split; trivial.
  Qed.

  Lemma SatML_And :
    forall gamma rho phi phi',
      SatML gamma rho (AndML phi phi') <->
      SatML gamma rho phi /\ SatML gamma rho phi'.
  Proof.
    intros;split;intros;split;intros;
    unfold SatML in H;
    fold SatML in H;
    destruct H as (H & H');
    trivial.
  Qed.
  
  Lemma SatML_Not :
    forall gamma rho phi,
      SatML gamma rho (NotML phi) <-> ~ SatML gamma rho phi.
  Proof.
    intros; split; intros;
    unfold SatML in H;
    fold SatML in H;
    trivial.
  Qed.


  Fixpoint in_list (x : Var) (l : list Var) : bool :=
    match l with
      | nil => false 
      | a :: l' => if (string_dec x a) 
                   then true 
                   else in_list x l' 
   end.

  Fixpoint append (l1 l2 : list Var) : list Var :=
    match l1 with 
      | nil => l2
      | x :: l1' => if (in_list x l2) 
                    then append l1' l2
                    else append l1' (cons x l2)
    end.

  Fixpoint getFreeVarsAExp (a : AExp) : list Var :=
    match a with
      | aexp_var v => cons v nil
      | plus a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | div a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | mod a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | _ => nil
    end. 

  Eval compute in  plus (aexp_var "i") (aexp_var "i") .
  Eval compute in getFreeVarsAExp (plus (aexp_var "i") (aexp_var "i")) .
  Eval compute in getFreeVarsAExp (plus (aexp_var "i") (aexp_var "j")) .
  Eval compute in getFreeVarsAExp (plus (id "i") (aexp_var "j")) .
  


  Fixpoint getFreeVarsBExp (b : BExp) : list Var := 
    match b with
      | not b' => getFreeVarsBExp b'
      | and b1 b2 => append (getFreeVarsBExp b1) (getFreeVarsBExp b2)
      | le a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | leq a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | eq a1 a2 => append (getFreeVarsAExp a1) (getFreeVarsAExp a2) 
      | _ => nil
    end.

  Eval compute in getFreeVarsBExp (le (id "i") (aexp_var "j")) .

  Fixpoint getFreeVarsStmt (s : Stmt) : list Var :=
    match s with
      | assign s a => getFreeVarsAExp a 
      | ifelse b s1 s2 => append (getFreeVarsBExp b)
                                 (append (getFreeVarsStmt s1)
                                         (getFreeVarsStmt s2))
      | while b s' => append (getFreeVarsBExp b) (getFreeVarsStmt s') 
      | seq s1 s2 => append (getFreeVarsStmt s1) (getFreeVarsStmt s2)
    end.
  
  Eval compute in  (while (leq (id "i") (aexp_var "n"))
                          (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i")))).
  Eval compute in  getFreeVarsStmt ((while (leq (id "i") (aexp_var "n"))
                          (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (id "i"))))).
  Eval compute in  getFreeVarsStmt ((while (leq (id "i") (aexp_var "n"))
                                           (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (aexp_var "i"))))).

  Fixpoint getFreeVarsMapItem (mi : MapItem) : list Var :=
    match mi with
      | (s , a) => getFreeVarsAExp a 
    end.
  
  Eval compute in ("i" |-> (aexp_var "n")) .
  Eval compute in getFreeVarsMapItem ("i" |-> (aexp_var "n")) .

  Fixpoint getFreeVarsMem (m : Mem) : list Var := 
    match m with
      | nil => nil
      | mi :: m' => append (getFreeVarsMapItem mi) (getFreeVarsMem m') 
    end.

  Eval compute in (cons ("i" |-> (aexp_var "n")) 
                        (cons ("i" |-> (aexp_var "n"))(cons ("i" |-> (aexp_var "n")) nil))).
  Eval compute in getFreeVarsMem 
                    (cons ("i" |-> (aexp_var "n")) 
                        (cons ("i" |-> (aexp_var "n"))(cons ("i" |-> (aexp_var "n")) nil))).

  Fixpoint getFreeVarsCfg (c : Cfg) : list Var :=
    match c with
      | (s, m) => append (getFreeVarsStmt s) (getFreeVarsMem m) 
    end.
  
  Eval compute in (((while (leq (id "i") (aexp_var "n"))
                           (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (aexp_var "i")))))  ,
                   (cons ("i" |-> (aexp_var "n")) 
                         (cons ("i" |-> (aexp_var "n"))(cons ("i" |-> (aexp_var "n")) nil))))  .
  Eval compute in getFreeVarsCfg (((while (leq (id "i") (aexp_var "n"))
                           (seq ("i" ::= plus (id "i") (val (c_nat 1))) ("s" ::= plus (id "s") (aexp_var "i")))))  ,
                   (cons ("i" |-> (aexp_var "n")) 
                         (cons ("i" |-> (aexp_var "n"))(cons ("i" |-> (aexp_var "i")) nil))))  .


  Fixpoint list_diff (l1 l2 : list Var) : list Var :=
    match l2 with
      | nil => l1
      | x :: l2' => if (in_list x l1) 
                    then list_diff (remove string_dec x l1) l2'
                    else list_diff l1 l2'
    end.

  Fixpoint getFreeVars (phi : MLFormula) : list Var :=
    match phi with
      | T => nil 
      | pattern pi => getFreeVarsCfg pi
      | pred b => getFreeVarsBExp b 
      | NotML phi' => getFreeVars phi'
      | AndML phi1 phi2 => append (getFreeVars phi1) (getFreeVars phi2)
      | ExistsML vs phi' => list_diff (getFreeVars phi') vs
      | enc phi' => getFreeVars phi'
    end.

  Definition encoding (F : MLFormula) : MLFormula := enc F.

  Lemma Proposition1 :
    forall gamma' phi rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
  Proof.
    intros; split; intros.
    - simpl in *.
      destruct H as (gamma'' & H).
      exists gamma''. trivial.
    - simpl.
      destruct H as (gamma'' & H).
      exists gamma''. trivial.
  Qed.



End LangML.