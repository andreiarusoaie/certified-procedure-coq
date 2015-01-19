Require Import List .
Require Import String .
Require Import ZArith.

Parameter Sort : Type .
Parameter OpSymbol : Type . (* QIds as in Maude? *)
Parameter Var : Type .

(* Many-sorted signature *)
Record Signature :=
  sig {
      sorts : list Sort; (* really needed? *)
      ops : list (OpSymbol * ((list Sort) * Sort))
    } .

(* Terms *)
Inductive Term : Type :=
| tcst : OpSymbol -> Term
| tvar : Var -> Term
| tcom : OpSymbol -> list Term -> Term .


(* TODO: Well-formed sigma terms *)
(*
Fixpoint wf (Σ : Signature) (t : Term) : bool := TODO
*)

(*
Variables a b c : Sort .
Variables s t : OpSymbol .
Eval compute in sig (a :: b :: nil)
                    ((s, ((a :: c :: nil), b)) ::
                    (t, ((a :: nil), c)) :: nil) .
Definition S := sig (a :: b :: nil)
                    ((s, ((a :: c :: nil), b)) ::
                                               (t, ((a :: nil), c)) :: nil) .

Eval compute in ops S .

(*

Inductive AExp :=
| int : Z -> AExp
| id : string -> AExp
| add : AExp -> AExp -> AExp .

Inductive BExp :=
| bl : bool -> BExp
| less : AExp -> AExp -> BExp 
| and : BExp -> BExp -> BExp 
| not : BExp -> BExp .

Inductive Stmt :=
| skip : Stmt
| ifStmt : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| stmts : Stmt -> Stmt -> Stmt .



(* Semantics of sorts and operations *)
Parameter sortSem : list Sort -> Type .
Parameter opsSem : list (Symbol * ((list Sort) * Sort)) -> Type .

(* ΣAlgebra *)
Record ΣAlgebra (sigma : Signature) : Type :=
  alg {
      carrierSets : (sortSem (sorts sigma));
      functions : (opsSem (operations sigma))
    } .



*)*)