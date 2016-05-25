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
(*    | to_m_f : _f -> Model 
    | to_m_bool : _bool -> Model *)
    | to_m_nat : _nat -> Model
(*    | to_m_map : _map -> Model
    | to_m_mapitem : _mapitem -> Model
    | to_m_cfg : _cfg -> Model *).

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

  Definition varTo_nat_val (v : Var) : Model :=
    to_m_nat (varTo_nat v).

  Eval compute in varsTo_nat (cons "a" nil).
  Eval compute in varTo_nat_val "a".

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


  Fixpoint applyValToAExp (rho : Valuation) (A : AExp) : _nat :=
    match A with
      | aexp_var v => match (rho v) with 
                        | to_m_nat n =>  n
                      end
      | id s => (s_nat s)
      | val s => s
      | plus A1 A2 => _plus (applyValToAExp rho A1) (applyValToAExp rho A2)
      | div A1 A2 => _div (applyValToAExp rho A1) (applyValToAExp rho A2)
      | mod A1 A2 => _mod (applyValToAExp rho A1) (applyValToAExp rho A2) 
    end.

  Definition testVal (v : Var) : Model :=
    if var_eq v "x" then to_m_nat (c_nat 2) else to_m_nat (c_nat 0).

  Eval compute in applyValToAExp testVal ( plus (aexp_var "x")  (aexp_var "y")) .

  Fixpoint applyValToBExp (rho : Valuation) (B:BExp) : _bool := 
    match B with 
      | bval B' =>  B'
      | not B' => _not (applyValToBExp rho B') 
      | and B1 B2 => _and (applyValToBExp rho B1) (applyValToBExp rho B2)
      | le A1 A2 => _le (applyValToAExp rho A1) (applyValToAExp rho A2)
      | leq A1 A2 => _leq (applyValToAExp rho A1) (applyValToAExp rho A2) 
      | eq A1 A2 => _eq (applyValToAExp rho A1) (applyValToAExp rho A2)
    end.

  Eval compute in applyValToBExp testVal ( leq (aexp_var "x")  (aexp_var "y")) .

  Fixpoint applyValToMemItem (rho : Valuation) (M : MapItem) : _mapitem :=
    let (X, A) :=  M in (X, applyValToAExp rho A).

  Fixpoint applyValToMem (rho : Valuation) (M : Mem) : _map :=
    match M with
      | nil => nil
      | x :: xs => (applyValToMemItem rho x) :: (applyValToMem rho xs) 
    end.

  Eval compute in applyValToMem testVal (( "y" |-> (aexp_var "x")  ) :: nil) .
  Eval compute in applyValToMem testVal (( "y" |-> (aexp_var "z")  ) :: nil) .

  Fixpoint applyValToStmt (rho : Valuation) (St :  Stmt) : _stmt :=
    match St with 
      | assign s e => _assign s (applyValToAExp rho e)
      | ifelse b s1 s2 => _ifelse (applyValToBExp rho b) (applyValToStmt rho s1) (applyValToStmt rho s2)
      | while b s => _while (applyValToBExp rho b) (applyValToStmt rho s)
      | seq s1 s2 => _seq (applyValToStmt rho s1) (applyValToStmt rho s2) 
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




  Fixpoint applyVal (rho : Valuation) (phi : MLFormula) : _f := 
    match phi with 
      | T =>  _f_t
      | pattern (St, M) => _f_cfg ((applyValToStmt rho St), (applyValToMem rho M))
      | pred B => _f_pred (applyValToBExp rho B)
      | NotML F => _f_not (applyVal rho F)
      | AndML F F' => _f_and (applyVal rho F) (applyVal rho F') 
      | ExistsML Vs F => _f_exists (varsTo_nat Vs) (applyVal (modify_val_on_set rho varTo_nat_val Vs) F) 
      | enc F => _f_not (applyVal rho F)
    end.






  
  Fixpoint SatML (gamma : State)(rho : Valuation)(phi : MLFormula) : Prop :=
    match phi with
      | T => True
      | pattern (St, M) => applyVal rho phi = (_f_cfg gamma)
      | pred B => applyValToBExp rho B = (c_bool true)
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

  Fixpoint getFreeVarsMapItem (mi : MapItem) : list Var := let (_, a) := mi in getFreeVarsAExp a .
    
  
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
    let (s, m) := c in append (getFreeVarsStmt s) (getFreeVarsMem m) .
  
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








  (* encoding and Proposition 1*)
  Definition encoding (F : MLFormula) : MLFormula := enc F.

  Lemma Proposition1 :
    forall gamma' phi rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
  Proof.
    intros; split; intros; simpl in *;
      destruct H as (gamma'' & H);
      exists gamma''; trivial.
  Qed.











  Lemma no_vars : 
    forall gamma rho phi,
      (exists rho', SatML gamma rho' phi) ->
      (getFreeVars phi = nil) ->
      SatML gamma rho phi.
  Admitted.


  Lemma incl_nil :
    forall l : list Var,
      incl l nil -> l = nil.
  Proof.
    induction l; trivial; intros.
    assert (H0 : In a (a :: l)); simpl; try left; trivial.
    unfold incl in H.
    assert (H1 : In a nil); try apply H; trivial.
    contradict H1.
  Qed.





  Lemma apply_val_aexp : 
    forall a V rho rho',
      incl (getFreeVarsAExp a) V ->
      applyValToAExp (modify_val_on_set rho rho' V) a = applyValToAExp rho' a.
  Proof.
    induction a; intros; simpl; trivial.
    - rewrite IHa1, IHa2; trivial.
      + 

  Admitted.

  Lemma apply_val_stmt : 
    forall V rho rho' s,
      incl (getFreeVarsStmt s) V ->
      applyValToStmt (modify_val_on_set rho rho' V) s = applyValToStmt rho' s.
  Admitted.
  
  Lemma apply_val_mem : 
    forall V rho rho' s,
      incl (getFreeVarsMem s) V ->
      applyValToMem (modify_val_on_set rho rho' V) s = applyValToMem rho' s.
  Admitted.


  Lemma apply_val_bexp : 
    forall V rho rho' s,
      incl (getFreeVarsBExp s) V ->
      applyValToBExp (modify_val_on_set rho rho' V) s = applyValToBExp rho' s.
  Admitted.
  

  Lemma append_incl_r : 
    forall A B X,
      incl (append A B) X -> incl B X.
  Proof.
    induction A; intros; simpl in *; trivial.
    case_eq (in_list a B); intros; rewrite H0 in H.
    - apply IHA; trivial.
    - apply IHA in H.
      unfold incl; intros a' Ha'.
      unfold incl in H.
      apply H.
      simpl; right; trivial.
  Qed.
  
  Lemma in_list_In : 
    forall l a,
      in_list a l = true -> In a l.
  Proof.
    induction l; intros.
    - simpl in H.
      inversion H.
    - simpl in *.
      case_eq (string_dec a0 a); intros; rewrite H0 in H.
      + left; subst a; reflexivity.
      + right. apply IHl; trivial.
  Qed.
  
  Lemma append_incl_l : 
    forall A B X,
      incl (append A B) X -> incl A X.
  Proof.
    induction A; intros; simpl in *.
    - unfold incl; intros. 
      contradict H0.
    - case_eq (in_list a B); intros; rewrite H0 in H.
      + unfold incl; intros a' Ha'.
        assert (H' : (incl (append A B) X)); trivial.
        apply IHA in H'.
        unfold incl in H'.
        simpl in Ha'.
        destruct Ha'.
        * apply append_incl_r in H.
          unfold incl in H.
          apply H.
          apply in_list_In; subst; trivial.
        * apply H'; trivial.
      + unfold incl; intros a' Ha'.
        assert (H' : incl (append A (a :: B)) X); trivial.
        apply append_incl_r in H'.
        simpl in Ha'.
        destruct Ha'.
        * unfold incl in H'.
          apply H'.
          simpl; left; trivial.
        * apply IHA in H.
          unfold incl in H.
          apply H; trivial.
  Qed.


  Lemma applyExists : 
    forall l phi V rho rho',
      incl (getFreeVars (ExistsML l phi)) V ->
      applyVal (modify_val_on_set rho rho' V) (substBoundedVs l phi) = 
      applyVal rho' (substBoundedVs l phi).
  Proof.
        admit.
  Qed.


  Lemma subst_nil :
    forall phi,
      substBoundedVs nil phi = phi.
  Proof.
    simpl. trivial.
  Qed.

  Lemma modify_reduction : 
    forall phi rho rho' rho0 V,
      applyVal rho phi = applyVal rho' phi ->
      applyVal (modify_val_on_set rho rho0 V) phi = 
      applyVal (modify_val_on_set rho' rho0 V) phi.
  Proof.
    admit.
  Qed.



  Lemma in_append_iff_r :
    forall A B a,
      In a (append A B) -> In a A \/ In a B.
  Proof.
    induction A; intros.
    - simpl in *.
      right; trivial.
    - simpl in *.
      case_eq (in_list a B); intros.
      + rewrite H0 in H.
        apply IHA in H.
        destruct H.
        * left. right; trivial.
        * right; trivial.
      + rewrite H0 in H.
        apply IHA in H.
        destruct H.
        * left. right. trivial.
        * simpl in H.
          destruct H.
          left. left. trivial.
          right. trivial.
  Qed.

  Lemma in_append_iff_l :
    forall A B a,
      In a A \/ In a B -> In a (append A B).
  Proof.
    induction A.
    - simpl.
      intros.
      destruct H; trivial.
      contradict H.
    - intros.
      simpl.
      case_eq (in_list a B); intros H'.
      apply IHA.
      apply in_list_In in H'; trivial.
      destruct H.
      + simpl in H.
        destruct H.
        * subst a.
          right. trivial.
        * left. trivial.
      + right. trivial.
      + apply IHA.
        simpl in *.
        destruct H.
        * destruct H.
          subst a. right. left. trivial.
          left. trivial.
        * right. right. trivial.
  Qed.

  Lemma in_append_incl_l :
    forall X Y a,
      In a X -> In a (append X Y).
  Proof.
    induction X.
    - intros.
      contradict H.
    - intros Y a0 H'.
      simpl.
      case_eq (in_list a Y); intros.
      + simpl in H'.
        destruct H'.
        assert (H' : In a Y).
        apply in_list_In; trivial.
        apply in_append_iff_l.
        subst a.
        right. trivial.
        apply in_append_iff_l.
        left. trivial.
      + apply in_append_iff_l.
        simpl.
        destruct H'.
        * right. left. trivial.
        * left. trivial.
  Qed.

  Lemma in_append_incl_r :
    forall X Y a,
      In a Y -> In a (append X Y).
  Proof.
    induction X.
    - intros.
      simpl; trivial.
    - intros.
      simpl.
      case_eq (in_list a Y); intros.
      + apply IHX; trivial.
      + apply IHX.
        simpl.
        right. trivial.
  Qed.
  
  Lemma in_append_iff :
    forall X Y a,
      In a (append X Y) -> In a X \/ In a Y.
  Proof.
    induction X.
    - simpl. intros. right. trivial.
    - intros.
      simpl in *.
      case_eq (in_list a Y); intros.
      + rewrite H0 in H.
        apply IHX in H.
        destruct H as [H | H].
        * left. right. trivial.
        * right. trivial.
      + rewrite H0 in H.
        apply IHX in H.
        destruct H as [H | H].
        * left. right. trivial.
        * simpl in H.
          destruct H as [H | H].
          left. left. trivial.
          right. trivial.
  Qed.
    


  Lemma applyVal_stmt_var : 
    forall s a rho rho',
      applyValToStmt rho s = applyValToStmt rho' s -> 
      applyValToStmt (modify_val_on_var rho varTo_nat_val a) s = applyValToStmt (modify_val_on_var rho' varTo_nat_val a) s.
  Proof.
    admit.
  Qed.

  Lemma applyVal_mem_var : 
    forall m a rho rho',
      applyValToMem rho m = applyValToMem rho' m ->
      applyValToMem (modify_val_on_var rho varTo_nat_val a) m = applyValToMem (modify_val_on_var rho' varTo_nat_val a) m.
  Proof.
    admit.
  Qed.

  Lemma applyVal_aexp_var : 
    forall ae a rho rho',
      applyValToAExp rho ae = applyValToAExp rho' ae ->
      applyValToAExp (modify_val_on_var rho varTo_nat_val a) ae = applyValToAExp (modify_val_on_var rho varTo_nat_val a) ae.
  Proof.
    admit.
  Qed.

  Lemma applyVal_bexp_var : 
    forall be a rho rho',
      applyValToBExp rho be = applyValToBExp rho' be ->
      applyValToBExp (modify_val_on_var rho varTo_nat_val a) be = applyValToBExp (modify_val_on_var rho' varTo_nat_val a) be.
  Proof.
    admit.
  Qed.

(*
  Lemma rev_modify_r :
    forall l phi rho rho' a,
      applyVal (modify_val_on_var (modify_val_on_set rho rho' l) rho' a) phi = 
      applyVal (modify_val_on_set rho rho' (a::l)) phi.
  Proof.
    induction l; intros.
    - simpl. trivial.
    - simpl.

  Lemma rev_modify_l :
    forall l phi rho rho' a,
      applyVal (modify_val_on_set (modify_val_on_var rho rho' a) rho' l) phi = 
      applyVal (modify_val_on_set rho rho' (a::l)) phi.
  Proof.
*)

  Lemma rev_modify :
    forall l phi rho rho' a,
      applyVal (modify_val_on_set (modify_val_on_var rho rho' a) rho' l) phi = 
      applyVal (modify_val_on_var (modify_val_on_set rho rho' l) rho' a) phi.
  Proof.
    induction l; intros.
    - simpl; trivial.
    - simpl.
      rewrite <- IHl.

    admit.
  Qed.


  Lemma rev_modify_var_aexp : 
    forall ae rho a b,
      applyValToAExp (modify_val_on_var (modify_val_on_var rho varTo_nat_val a) varTo_nat_val b) ae =
      applyValToAExp (modify_val_on_var (modify_val_on_var rho varTo_nat_val b) varTo_nat_val a) ae.
  Proof.
    induction ae; intros.
    - simpl; trivial.
    - simpl; trivial.
    - simpl. 
      rewrite IHae1.
      rewrite IHae2.
      trivial.
    - simpl.
      rewrite IHae1.
      rewrite IHae2.
      trivial.
    - simpl.
      rewrite IHae1.
      rewrite IHae2.
      trivial.
    - simpl.


  Lemma rev_modify_var_stmt : 
    forall s rho rho' a b,
      applyValToStmt (modify_val_on_var (modify_val_on_var rho rho' a) rho' b) s =
      applyValToStmt (modify_val_on_var (modify_val_on_var rho rho' b) rho' a) s.
  Proof.

  Lemma rev_modify_var_mem : 
    forall m rho rho' a b,
      applyValToMem (modify_val_on_var (modify_val_on_var rho rho' a) rho' b) m =
      applyValToMem (modify_val_on_var (modify_val_on_var rho rho' b) rho' a) m.
  Proof.

  Lemma rev_modify_var_bexp : 
    forall be rho rho' a b,
      applyValToBExp (modify_val_on_var (modify_val_on_var rho rho' a) rho' b) be =
      applyValToBExp (modify_val_on_var (modify_val_on_var rho rho' b) rho' a) be.
  Proof.




  Lemma rev_modify_var : 
    forall phi rho rho' a b,
      applyVal (modify_val_on_var (modify_val_on_var rho rho' a) rho' b) phi =
      applyVal (modify_val_on_var (modify_val_on_var rho rho' b) rho' a) phi.
  Proof.

      admit.
Qed.
  

  Lemma modify_val : 
    forall phi rho rho' a,
      applyVal rho phi = applyVal rho' phi ->
      applyVal (modify_val_on_var rho varTo_nat_val a) phi = applyVal (modify_val_on_var rho' varTo_nat_val a) phi.
  Proof.
    induction phi; intros.
    - simpl; trivial.
    - destruct c.
      simpl in *.
      rewrite applyVal_stmt_var with (rho' := rho').
      rewrite applyVal_mem_var with (rho' := rho').
      trivial.
      case_eq (applyValToStmt rho s); intros;
      try rewrite H0 in H; try inversion H.
      case_eq (applyValToStmt rho' s); intros;
      rewrite H1 in *;
      try rewrite H1 in H;
      try inversion H.
      case_eq (applyValToMem rho m); intros;
      rewrite H2 in *; trivial.
      trivial.
      case_eq (applyValToMem rho' m); intros;
      rewrite H1 in *; trivial.
      case_eq (applyValToMem rho m); intros;
      rewrite H2 in *; trivial.
      inversion H; trivial.
    - inversion H.
      simpl.
      rewrite applyVal_bexp_var with (rho' := rho'); trivial.
    - simpl in *.
      inversion H.
      rewrite IHphi with (rho' := rho'); trivial.
    - simpl in *.
      inversion H.
      rewrite IHphi1 with (rho' := rho'), IHphi2 with (rho' := rho'); trivial.
    - simpl in *.
      rewrite rev_modify.
      rewrite rev_modify.
      rewrite IHphi with (rho' := (modify_val_on_set rho' varTo_nat_val l)); trivial.
      inversion H; trivial.
    - simpl in *.
      inversion H.
      rewrite IHphi with (rho' := rho'); trivial.
  Qed.



  Lemma apply_val : 
    forall phi V rho rho',
      incl (getFreeVars phi) V ->
      applyVal (modify_val_on_set rho rho' V) phi = applyVal rho' phi.
  Proof.
    admit.
  Qed.
        
      
  Lemma diff_incl : 
    forall A B C,
      incl (list_diff A B) C -> incl A (append B C) .
  Proof.
    admit.
  Qed.

  Lemma val_overlap :
    forall l V rho rho' eta z,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V) z=
      modify_val_on_set (modify_val_on_set rho rho' V) eta l z.
  Proof.
    induction l; intros.
    - simpl.
      induction V.
      + simpl; trivial.
      + simpl in H.
        unfold modify_val_on_var.
        case_eq (var_eq a z).
        * intros. simpl.
          assert (rho' a = eta a). 
          apply H. 
          unfold Coq.Init.Logic.not.
          intros.
          trivial.
          unfold modify_val_on_var.
          rewrite H0.
          rewrite H1.
          trivial.
        * intros.
          simpl.
          unfold modify_val_on_var.
          rewrite H0.
          rewrite <- IHV.
          admit.
        
      
    - admit.
  Qed.


  Lemma aexp_overlap : 
    forall a l V rho rho' eta,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      (applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta l) a) =
      (applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) a).
  Proof.
    induction a; intros.
    - simpl; trivial.
    - simpl; trivial.
    - simpl.
      rewrite IHa1; trivial.
      rewrite IHa2; trivial.
    - simpl.
      rewrite IHa1; trivial.
      rewrite IHa2; trivial.
    - simpl.
      rewrite IHa1; trivial.
      rewrite IHa2; trivial.
    - simpl.
      case_eq (in_dec string_dec s l).
      + case_eq (in_dec string_dec s V); intros.
        * rewrite modify_in; trivial.
          rewrite modify_in; trivial.
          apply in_append_incl_l; trivial.
        * rewrite modify_in; trivial.
          rewrite modify_in; trivial.
          apply in_append_incl_l; trivial.
      + case_eq (in_dec string_dec s V); intros.
        * rewrite modify_not_in; trivial.
          rewrite modify_in; trivial.
          rewrite modify_in.
          assert (H'' : ~ In s l); trivial.
          apply H in H''.
          rewrite H''; trivial.
          apply in_append_incl_r; trivial.
        * rewrite modify_not_in; trivial.
          rewrite modify_not_in; trivial.
          rewrite modify_not_in.
          rewrite modify_not_in; trivial.
          unfold Coq.Init.Logic.not in *.
          intros.
          apply in_append_iff in H2.
          destruct H2 as [H2 | H2].
          apply n0; trivial.
          apply n; trivial.
  Qed.

  Lemma bexp_overlap : 
    forall b l V rho rho' eta,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      (applyValToBExp (modify_val_on_set (modify_val_on_set rho rho' V) eta l) b) =
      (applyValToBExp (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) b).
  Proof.
    induction b; intros.
    - simpl. trivial.
    - simpl.
      rewrite IHb; trivial.
    - simpl.
      rewrite IHb1; trivial.
      rewrite IHb2; trivial.
    - simpl.
      rewrite aexp_overlap; trivial.
      assert (H0:  applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta l) a0 = applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) a0). rewrite aexp_overlap; trivial.
      rewrite H0.
      trivial.
    - simpl.
      rewrite aexp_overlap; trivial.
      assert (H0:  applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta l) a0 = applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) a0). rewrite aexp_overlap; trivial.
      rewrite H0.
      trivial.
    - simpl.
      rewrite aexp_overlap; trivial.
      assert (H0:  applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta l) a0 = applyValToAExp (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) a0). rewrite aexp_overlap; trivial.
      rewrite H0.
      trivial.
  Qed.

  Lemma mem_overlap : 
    forall m l V rho rho' eta,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      applyValToMem (modify_val_on_set (modify_val_on_set rho rho' V) eta l) m =
      applyValToMem (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) m.
  Proof.
    induction m; intros.
    - simpl. trivial.
    - simpl.
      induction a.
      + simpl.
        rewrite aexp_overlap; trivial.
        rewrite IHm; trivial.
  Qed.
    
                                       
  Lemma stmt_overlap : 
    forall s l V rho rho' eta,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      applyValToStmt (modify_val_on_set (modify_val_on_set rho rho' V) eta l) s = 
      applyValToStmt (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) s.
    Proof.
      induction s; intros.
      - simpl.
        rewrite aexp_overlap; trivial.
      - simpl.
        rewrite bexp_overlap; trivial.
        rewrite IHs1; trivial.
        rewrite IHs2; trivial.
      - simpl.
        rewrite bexp_overlap; trivial.
        rewrite IHs; trivial.
      - simpl.
        rewrite IHs1; trivial.
        rewrite IHs2; trivial.
    Qed.




  Lemma var_overlap_sat : 
    forall phi l V rho rho' eta gamma,
      (forall v : Var, ~ In v l -> rho' v = eta v) ->
      SatML gamma eta phi ->
      SatML gamma (modify_val_on_set (modify_val_on_set rho rho' V) eta (append l V)) phi ->
      SatML gamma (modify_val_on_set (modify_val_on_set rho rho' V) eta l) phi.
  Proof.
    induction phi; intros.
    - simpl. trivial.
    - destruct c.
      simpl.
      simpl in H1.
      destruct gamma.
      inversion H1.
      rewrite stmt_overlap; trivial.
      rewrite mem_overlap; trivial.
    - simpl in *.
      rewrite <- H1.
      apply bexp_overlap; trivial.
    - simpl in *.
      admit.
    - simpl in *.
      destruct H0 as (H0 & H0').
      destruct H1 as (H1 & H1').
      split.
      apply IHphi1; trivial.
      apply IHphi2; trivial.
    - simpl in *.
      destruct H1 as (mu & H1 & H1').
      destruct H0 as (mu' & H0 & H0').
      exists mu.
      split; trivial.
      intros.
      rewrite <- H1; trivial.
      admit.
    - simpl in *.
      admit.
  Qed.      
      



  Lemma modify_Sat1 :
    forall phi V gamma rho rho',
      SatML gamma rho' phi ->
      incl (getFreeVars phi) V ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Proof.
    unfold SatML.
    induction phi; intros.
    - trivial.
    - destruct c.
      simpl.
      unfold SatML in H.
      rewrite apply_val_stmt.
      rewrite apply_val_mem.
      simpl in H; trivial; simpl in H0.
      apply append_incl_r with (A := (getFreeVarsStmt s)); trivial.
      apply append_incl_l with (B := (getFreeVarsMem m)); trivial.
    - unfold SatML in H.
      rewrite apply_val_bexp; trivial.
    - admit.
    - fold SatML in *.
      destruct H as (H & H').
      split.
      + apply IHphi1; trivial.
        simpl in H0.
        apply append_incl_l with (B := (getFreeVars phi2)); trivial.
      + apply IHphi2; trivial.
        apply append_incl_r with (A := (getFreeVars phi1)); trivial.
    - fold SatML in *.
      destruct H as (eta & H & H').
      exists (modify_val_on_set (modify_val_on_set rho rho' V) eta l).
      split.
      + intros.
        assert (In v V \/ ~ In v V).
        apply classic.
        destruct H2 as [H2 | H2].
        * rewrite modify_in; trivial.
          rewrite modify_not_in; trivial.
          rewrite modify_in; trivial.
        * rewrite modify_not_in; trivial.
          rewrite modify_not_in; trivial.
          rewrite modify_not_in; trivial.
      + simpl in H0.
        apply diff_incl in H0.
        apply IHphi with (gamma := gamma) (rho := (modify_val_on_set rho rho' V)) (rho' := eta) in H0; trivial.
        apply var_overlap_sat; trivial.
    - fold SatML in *.
      simpl in H0.
      destruct H as (gamma' & H).
      exists gamma'.
      apply IHphi; trivial.
  Qed.
      
      
        




End LangML.