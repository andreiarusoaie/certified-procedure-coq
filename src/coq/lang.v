Require Import ml.
Require Import String.
Require Import List.

Module Lang <: Formulas.

  Inductive Var : Type := var : string -> string -> Var.
  Open Scope string_scope.

  (* syntax *)
  Inductive Exp : Type := 
  | exp_var : Var -> Exp
  | id : string -> Exp
  | val : nat -> Exp
  | plus : Exp -> Exp -> Exp.

  Eval compute in (exp_var (var "a" "exp")).
  Eval compute in (plus (id "a") (exp_var (var "a" "exp"))).
  Eval compute in (plus (id "a") (val 4)).

  Inductive Stmt : Type :=
  | assign : string -> Exp -> Stmt
  | seq : list Stmt -> Stmt
  | stmt_var : Var -> Stmt.

  Eval compute in (assign "a" (val 10)).
  Eval compute in (assign "a" (plus (id "a") (val 10))).
  Eval compute in 
      assign "a" (plus (id "a") (val 10)) :: (assign "a" (val 10)) :: nil.
                   
  

  (* configuration *)
  Inductive MapItem := item : string -> Exp -> MapItem.
  Inductive Cfg := 
  | cfg : Stmt -> list MapItem -> Cfg
  | cfg_var : Var -> Cfg.

  Notation "A |-> B" := (item A B) (at level 100).
  Eval compute in (cfg 
                     (assign "a" (plus (id "a") (val 10))) 
                     (("a" |-> (exp_var (var "A" "exp"))) :: nil)).





  
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
  Definition var_eq (X Y : Var) : bool :=
    match X, Y with
      | var x xsort, var y ysort =>
                     if (string_dec x y) 
                     then if (string_dec xsort ysort)
                          then true
                          else false
                     else false
    end.

  Lemma var_eq_true : 
    forall a b, var_eq a b = true <-> a = b.
  Proof.
    intros a b.
    split; intros H.
    - unfold var_eq in H.
      case_eq a; intros aname asort Ha.
      subst a.
      case_eq b; intros bname bsort Hb.
      subst b.
      case_eq (string_dec aname bname); intros e He; subst; rewrite He in *.
      + case_eq (string_dec asort bsort); intros e' He'; subst; rewrite He' in *.
        * trivial.
        * inversion H.
      + inversion H.
    - rewrite H.
      unfold var_eq.
      case_eq b; intros bname bsort Hb.
      case_eq (string_dec bname bname); intros H' H''.
      + case_eq (string_dec bsort bsort); intros H0 H1; trivial.
        contradict H1; unfold not in *; intros; apply H0; trivial.
      + contradict H''; unfold not in *; intros; apply H'; trivial.
  Qed.

  Lemma var_eq_false:
    forall a b, var_eq a b = false <-> a <> b.
  Proof.
    intros a b; split; intros H.
    - unfold var_eq in *.
      case_eq a; intros aname asort Ha.
      case_eq b; intros bname bsort Hb.
      rewrite Ha, Hb in H.
      case_eq (string_dec aname bname); intros e He; subst; rewrite He in *.
      + case_eq (string_dec asort bsort); intros e He'; subst; rewrite He' in *.
        * inversion H.
        * unfold not in *; intros; apply e.
          inversion H0; trivial.
      + unfold not in *; intros; apply e.
        inversion H0; trivial.
    - case_eq a; intros aname asort Ha.
      case_eq b; intros bname bsort Hb.
      subst.
      unfold var_eq.
      case_eq (string_dec aname bname); intros e He; subst; trivial.
      case_eq (string_dec asort bsort); intros e He'; subst; trivial.
      contradict H.
      apply var_eq_true.
      simpl.
      rewrite He, He'; trivial.
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

      
                       