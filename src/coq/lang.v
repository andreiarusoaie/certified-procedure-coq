Require Import ml.
Require Import String.
Require Import List.
Require Import Classical.

Module Lang <: Formulas.

(*  Inductive Var : Type := var : string -> string -> Var. *)
  Open Scope string_scope.

  (* syntax *)
  Inductive ExpVar : Type := exp_v : string -> ExpVar.
  Inductive Exp : Type := 
  | exp_var : ExpVar -> Exp
  | id : string -> Exp
  | val : nat -> Exp
  | plus : Exp -> Exp -> Exp.
  

  Eval compute in (exp_var (exp_v "a")).
  Eval compute in (plus (id "a") (exp_var (exp_v "a"))).
  Eval compute in (plus (id "a") (val 4)).

  Inductive StmtVar : Type := stmt_v : string -> StmtVar.
  Inductive Stmt : Type :=
  | stmt_var : StmtVar -> Stmt 
  | assign : string -> Exp -> Stmt
  | seq : list Stmt -> Stmt.

  Eval compute in (assign "a" (val 10)).
  Eval compute in (assign "a" (plus (id "a") (val 10))).
  Eval compute in 
      assign "a" (plus (id "a") (val 10)) :: (assign "a" (val 10)) :: nil.

  (* configuration *)
  Inductive MapItemVar : Type := mi_v : string -> MapItemVar.
  Inductive MapItem := 
  | mapitem_var : MapItemVar -> MapItem
  | item : string -> Exp -> MapItem.

  Inductive CfgVar : Type := cfg_v : string -> CfgVar.
  Inductive Cfg := 
  | cfg : Stmt -> list MapItem -> Cfg
  | cfg_var : CfgVar -> Cfg.

  Notation "A |-> B" := (item A B) (at level 100).
  Eval compute in (cfg 
                     (assign "a" (plus (id "a") (val 10))) 
                     (("a" |-> (exp_var (exp_v "A"))) :: nil)).

  (* Var *)
  Inductive Var : Type :=
  | var_exp : ExpVar -> Var
  | var_stmt : StmtVar -> Var
  | var_mapitem : MapItemVar -> Var 
  | var_cfg : CfgVar -> Var.

  
  (* model and state *)
  Inductive _exp : Type :=
    | _nat : nat -> _exp
    | _plus : _exp -> _exp -> _exp
    | _id : string -> _exp.
  
  Inductive _stmt : Type := 
    | _assign : string -> _exp -> _stmt
    | _seq : list _stmt -> _stmt.
   
  Definition _map_item := (string * nat)%type.
  Definition State : Type := (_stmt * _map_item)%type. 
  Inductive Model : Type := 
    | to_m_nat : nat -> Model
    | to_m_stmt : _stmt -> Model
    | to_m_map_item : _map_item -> Model
    | to_m_state : State -> Model.



  (* var equality *)
  Definition var_eq_exp (X Y : ExpVar) : bool := 
    match X, Y with 
      | exp_v x, exp_v y => if string_dec x y then true else false
    end.
  Definition var_eq_stmt (X Y : StmtVar) : bool := 
    match X, Y with 
      | stmt_v x, stmt_v y => if string_dec x y then true else false
    end.
  Definition var_eq_mapitem (X Y : MapItemVar) : bool := 
    match X, Y with 
      | mi_v x, mi_v y => if string_dec x y then true else false
    end.
  Definition var_eq_cfg (X Y : CfgVar) : bool := 
    match X, Y with 
      | cfg_v x, cfg_v y => if string_dec x y then true else false
    end.


  Definition var_eq (X Y : Var) : bool :=
    match X, Y with
      | var_exp x, var_exp y => var_eq_exp x y
      | var_stmt x, var_stmt y => var_eq_stmt x y
      | var_mapitem x, var_mapitem y => var_eq_mapitem x y
      | var_cfg x, var_cfg y => var_eq_cfg x y
      | _, _ => false
    end.

  Lemma var_eq_true : 
    forall a b, var_eq a b = true <-> a = b.
  Proof.
    intros a b.
    split; intros H.
    - case_eq a; intros v Hv; case_eq b; intros v' Hv'; unfold var_eq in H; subst; try inversion H.
      + unfold var_eq_exp in H.
        case_eq v; intros v0 Hv0; subst.
        case_eq v'; intros v0' Hv0'; subst.
        case_eq (string_dec v0 v0'); intros; subst; trivial.
        rewrite H0 in H.
        inversion H.
      + unfold var_eq_stmt in H.
        case_eq v; intros v0 Hv0; subst.
        case_eq v'; intros v0' Hv0'; subst.
        case_eq (string_dec v0 v0'); intros; subst; trivial.
        rewrite H0 in H.
        inversion H.
      + unfold var_eq_mapitem in H.
        case_eq v; intros v0 Hv0; subst.
        case_eq v'; intros v0' Hv0'; subst.
        case_eq (string_dec v0 v0'); intros; subst; trivial.
        rewrite H0 in H.
        inversion H.
      + unfold var_eq_cfg in H.
        case_eq v; intros v0 Hv0; subst.
        case_eq v'; intros v0' Hv0'; subst.
        case_eq (string_dec v0 v0'); intros; subst; trivial.
        rewrite H0 in H.
        inversion H.
    - subst.
      unfold var_eq.
      case_eq b; intros e He.
      + unfold var_eq_exp; case_eq e; intros s Hs; case_eq (string_dec s s); intros; trivial.
        contradiction n; trivial.
      + unfold var_eq_stmt; case_eq e; intros s Hs; case_eq (string_dec s s); intros; trivial.
        contradiction n; trivial.
      + unfold var_eq_mapitem; case_eq e; intros s Hs; case_eq (string_dec s s); intros; trivial.
        contradiction n; trivial.
      + unfold var_eq_cfg; case_eq e; intros s Hs; case_eq (string_dec s s); intros; trivial.
        contradiction n; trivial.
  Qed.

  Lemma var_eq_false:
    forall a b, var_eq a b = false <-> a <> b.
  Proof.
    intros a b.
    split; intros H.
    - unfold not.
      intros H'.
      apply var_eq_true in H'.
      rewrite H in H'.
      inversion H'.
    - assert (H' : var_eq a b = false \/ ~ var_eq a b = false ).
      apply classic.
      destruct H' as [H' | H']; trivial.
      case_eq (var_eq a b); intros Hv; trivial.
      rewrite var_eq_true in Hv.
      contradict H; trivial.
 Qed.

  Lemma var_eq_refl : 
    forall x, var_eq x x = true.
  Proof.
    intros x; apply var_eq_true; trivial.
  Qed.






  (* MLFormula *)
  Inductive MLFormulaHelper : Type :=
    | T : MLFormulaHelper
    | pattern: Cfg -> MLFormulaHelper 
    | NotML : MLFormulaHelper -> MLFormulaHelper 
    | AndML : MLFormulaHelper -> MLFormulaHelper -> MLFormulaHelper 
    | ExistsML : list Var -> MLFormulaHelper -> MLFormulaHelper
    | enc : MLFormulaHelper -> MLFormulaHelper .

  Definition MLFormula : Type := MLFormulaHelper.


  Eval compute in pattern (cfg (assign "a" (plus (id "a") (val 10))) nil).
  Eval compute in pattern 
                    (cfg 
                       (assign "a" (plus (id "a") (val 10))) 
                       (("a" |-> (exp_var (var "A" "exp"))) :: nil)).
  Eval compute in AndML T
                        ( pattern 
                            (cfg 
                               (assign "a" (plus (id "a") (val 10))) 
                               (("a" |-> (exp_var (var "A" "exp"))) :: nil))).
  
 



  (* Sat ML *)
  


End Lang.  

      
                       