(* Imports *)
Require Import ZArith String Bool .
Require Import List.
Require Import Formula .
Require Import Model .
Require Import ProofSystem .

Open Scope Z_scope.
Import ImpModel.

(* Instantiate Terms with IMP syntax *)
Module ImpSyntax <: TERM .
  
  (* Arithmetic expressions *)
  Inductive AExp :=
    | aexpSymInt : SymInt -> AExp                  
    | aexpId : string -> AExp 
    | aexpDiv : AExp -> AExp -> AExp 
    | aexpMult : AExp -> AExp -> AExp 
    | aexpPlus : AExp -> AExp -> AExp 
    | aexp : AExp -> AExp .

  (* Boolean expressions *)
  Inductive BExp :=
    | bexpBool : SymBool -> BExp
    | bexpNeg : BExp -> BExp 
    | bexpLeq : AExp -> AExp -> BExp 
    | bexpAnd : BExp -> BExp -> BExp
    | bexp : BExp -> BExp .

  (* Stmts *)
  Inductive Stmt :=
    | stmtAssign : string -> AExp -> Stmt
    | stmtIfElse : BExp -> Stmt -> Stmt -> Stmt 
    | stmtWhile : BExp -> Stmt -> Stmt 
    | stmtList : Stmt -> Stmt -> Stmt 
    | stmtSkip : Stmt .
  

  Fixpoint evalAexp (s : State) (e : AExp) :=
    match e with
      | aexpSymInt x => Some x
      | aexpId x => lookup x s
      | aexpDiv e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symDiv v1 v2) 
                           | _, _ => None                           
                         end
      | aexpMult e1 e2 => match evalAexp s e1, evalAexp s e2 with
                            | Some v1, Some v2 => Some (symMult v1 v2)
                            | _, _ => None                           
                          end
      | aexpPlus e1 e2 => match evalAexp s e1, evalAexp s e2 with
                            | Some v1, Some v2 => Some (symPlus v1 v2)
                            | _, _ => None                           
                          end
      | aexp e => evalAexp s e
    end.

  
  (*
Open Scope string_scope.
Eval compute in (eval_aexp (("c", 10)::("b", 5)::nil) (aexp_id "a")) .
Eval compute in (eval_aexp nil (aexp_int 5)).
Eval compute in (eval_aexp nil (aexp_plus (aexp_int 5) (aexp_int 2))).
Eval compute in (eval_aexp nil (aexp_div (aexp_int 5) (aexp_int 2))).
Eval compute in (eval_aexp nil (aexp_div (aexp_int 5) (aexp_int 0))).
Eval compute in (eval_aexp (("c", 10)::("b", 5)::nil) (aexp (aexp_id "c"))).
   *)

  Fixpoint evalBexp (s : State) (be : BExp) :=
    match be with
      | bexpBool b => Some b
      | bexpNeg b => match evalBexp s b with
                       | Some v => Some (symNeg v)
                       | _ => None
                     end
      | bexpLeq e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symLeInt v1 v2)
                           | _, _ => None
                         end
      | bexpAnd b1 b2 => match evalBexp s b1, evalBexp s b2 with
                           | Some v1, Some v2 => Some (symAnd v1 v2)
                           | _, _ => None
                         end
      | bexp b => evalBexp s b
    end.


  (*
Open Scope string_scope.
Eval compute in (eval_bexp (("c", 10)::("b", 5)::nil) (bexp_leq (aexp_id "e") (aexp_id "b"))).
   *)

  

  (* K specific definitions *)
  Inductive KSequence :=
    | kra : Stmt -> KSequence -> KSequence 
    | kdot : KSequence .
  Notation "K ~> K'" := (kra K K') (at level 99).


  (* Configuration *)
  Inductive Cfg : Type := cfg : KSequence -> State -> Cfg .

  (* Finally, the terms *)
  Definition Term : Type := Cfg .

End ImpSyntax.


Module Import F := MLFormula (ImpSyntax) .


(* Semantics *)
Inductive S : System :=
  | stepAssign : forall Env Env' X E V P K,
                   evalAexp Env E = Some V -> update X V Env = Some Env' ->
                   S (rule
                        (andF (bp (cfg (kra (stmtAssign X E) K) Env)) P)
                        (andF (bp (cfg (kra stmtSkip K) Env')) P))
(*  | stepIfElse1 : forall St1 St2 Env B K P V,
                    evalBexp Env B = Some V -> V = true ->
                    S (andF (bp (cfg (kra (stmtIfElse B St1 St2) K) Env)) P)
                      (andF (bp (cfg (kra St1 K) Env)) P)
  | stepIfElse2 : forall St1 St2 Env B K P V,
                    evalBexp Env B = Some V -> V = false ->
                    S (andF (bp (cfg (kra (stmtIfElse B St1 St2) K) Env)) P)
                      (andF (bp (cfg (kra St2 K) Env)) P)
*)
  (*
| stepIfElse1 : forall St1 St2 Env B K P,
                  S (andF (bp (cfg (stmtIfElse B St1 St2 ~> K) Env)) P)
                    (andF (bp (cfg (St1 ~> K) Env)) (andF P (bExpF B)))
| stepIfElse2 : forall St1 St2 Env B K P,
                  S (andF (bp (cfg (stmtIfElse B St1 St2 ~> K) Env)) P)
                    (andF (bp (cfg (St2 ~> K) Env)) (andF P (notF (bExpF B))))
   *)
  | stepWhile : forall St Env B K P,
                  S (rule
                       (andF (bp (cfg (kra (stmtWhile B St) K) Env)) P)
                       (andF (bp (cfg (kra (stmtIfElse B (stmtList St (stmtWhile B St)) stmtSkip) K) Env)) P))
  | stepList : forall St1 St2 Env K P,
                 S (rule
                      (andF (bp (cfg (kra (stmtList St1 St2) K) Env)) P)
                      (andF (bp (cfg (kra St1 (kra St2 K)) Env)) P))
  | stepSkip : forall Env K P,
                 S (rule
                      (andF (bp (cfg (kra stmtSkip K) Env)) P)
                      (andF (bp (cfg K Env)) P)) .





Module Import PS := ProofSystem.ProofSystem (ImpSyntax) .
Open Scope string_scope .

Inductive G : System :=
  | circularity : forall N S I, 
                    G (rule (andF
                               (bp
                                  (cfg
                                     (kra (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                                     (stmtList (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                                               (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)) ))))
                                          kdot)
                                     (("n", N)::("i", I)::("s", S)::nil) ))
                               (symF (symAnd
                                        (symLeInt (symZ 0) N)
                                        (symEqInt S (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))
                                     ))
                            )
                            (andF (bp (cfg (kra stmtSkip kdot)
                                           (("n", N)::("i", (symPlus I (symZ 1)))::("s", (symDiv (symMult (symPlus I (symZ 1)) (symPlus I (symZ 2))) (symZ 2)))::nil))) T)) .

Print System .
Print F.System.
Print Rule .
Print F.Rule .
Print Formula .
Print F.Formula .

Lemma sum : PS S G (andF
                      (bp
                         (cfg
                            (kra (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                            (stmtList (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                                      (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)) ))))
                                 kdot)
                            (("n", N)::("i", I)::("s", S)::nil) ))
                      (symF (symAnd
                               (symLeInt (symZ 0) N)
                               (symEqInt S (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))
                            ))
                   )
               (andF (bp (cfg (kra stmtSkip kdot)
                              (("n", N)::("i", (symPlus I (symZ 1)))::("s", (symDiv (symMult (symPlus I (symZ 1)) (symPlus I (symZ 2))) (symZ 2)))::nil))) T) .
  
