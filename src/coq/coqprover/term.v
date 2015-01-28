Require Import List .
Require Import String .
Require Import ZArith.
Require Import ListSet.

Inductive Sort : Type :=
| Bool : Sort
| Int : Sort
| String : Sort
(*
| Float : SortName
| Map : SortName
| List : SortName
| Bag : SortName
| Array : SortName
*)
.

Inductive Operation : Type :=
| plus : Operation
| land : Operation
. 

Definition opSort (o : Operation) : (list Sort) * Sort :=
  match o with
    | plus => ((Int :: Int :: nil), Int) 
    | land => ((Bool :: Bool :: nil), Bool) 
  end.
    
Record Var :=
  var {
      vName : string;
      vSort : Sort
    }.

Scheme Equality for Var .

(* Signature *)
Definition Signature := list Operation .

(* Terms := x | f(t1, ..., tn)  where n >= 0 *)
Inductive Term : Type :=
| tVar : Var -> Term
| term : Operation -> list Term -> Term
.


Definition string_eq (s1 s2 : string) :=
  andb (prefix s1 s2) (prefix s2 s1) .


Section Semantics.

  Definition sortSem (s : Sort) : Type :=
    match s with
      | Int => Z
      | Bool => bool
      | String =>  string
    end.

  
  
  Fixpoint operationSemType  (inputs : list Sort)(output : Sort) :
    Type := match inputs with
              | nil => sortSem output
              | i :: is' => sortSem i -> operationSemType is' output
            end.

  Definition operationSem (o : Operation) :
    operationSemType (fst (opSort o)) (snd (opSort o)) :=
    match o with
      | plus => Zplus
      | land => andb
    end.

  Compute operationSem plus 2%Z 5%Z .
  
  Fixpoint termSemType (term : Term) : Type :=
    match term with
      | tVar v => sortSem (vSort v)
      | term o _ => operationSemType (fst (opSort o)) (snd (opSort o))
    end.

  (*
Definition    TermSem (rho : forall (x : Var), sortSem (vSort x)) (term : Term) : termSemType term.
Proof.
  destruct term.
Show Proof.

Defined.
*)

  
  Fixpoint TermSem (rho : forall (x : Var), sortSem (vSort x)) (term : Term) : termSemType term :=
    match term  as t return (termSemType t) with
      | tVar v => rho v
      | term o args => operationSem o (map (TermSem rho) args)
    end.
End Semantics.


(* Functions *)
Record Fun : Type :=
  func {
      fname : string;
      ftype : Type;
      fargs : list Set
    }.

(* Algebra *)
Parameter Algebra : list Fun .

  

Definition f := func "+Int" Z (Z :: Z :: nil).
Definition zero := func "0" Z nil.

Eval compute in (f :: zero :: nil).


(* don't go below yet *)

(* Isn't this already defined? *)
Definition string_eq (s1 s2 : string) :=
  andb (prefix s1 s2) (prefix s2 s1) .

Fixpoint list_string_eq (l1 l2 : list string) : bool :=
  match l1, l2 with
    | nil, nil => true
    | a :: l, a' :: l' => andb (string_eq a a') (list_string_eq l l')
    | _, _ => false
  end.

Fixpoint getListOfTermsSorts (l : list Term) : list string :=
  match l with
    | a :: rest => (getSort a) ::
                               (getListOfTermsSorts rest)
    | nil => nil
  end.

(*
Open Scope string_scope.
Eval compute in prefix "a" "a".

Eval compute in list_string_eq ("a" :: "ab" :: nil ) (nil) .
Eval compute in list_string_eq ("a" :: "ab" :: nil ) ("a" :: "b" :: nil) .
Eval compute in list_string_eq ("a" :: "ab" :: nil ) ("a" :: "ab" :: nil) .


(* Well-formed terms 
TODO: fix recursive
*)
Fixpoint wft (T : Term) : bool :=
  match T with
    | tvar v => true
    | term o args => (list_string_eq (opargs o)
                           (getListOfTermsSorts args))
  end.


Definition x := var "x" "BExp" .
Eval compute in getSort (tvar x).

Definition zero := op "zero" "AExp" nil .
Definition plus := op "+" "AExp" ("AExp"::"AExp"::nil) .
Eval compute in getSort (term zero nil).
Eval compute in getSort (term plus ((term zero nil)::(tvar x)::nil)).

Eval compute in wft (term plus ((term zero nil)::(tvar x)::nil)).



(*
(* Many-sorted signature *)
Record Signature :=
  sig {
      sorts : list Sort; (* really needed? *)
      ops : list (OpSymbol * ((list Sort) * Sort))
    } .

(* Σ-Terms *)
Inductive Term : Type :=
| tcst : OpSymbol -> Term
| tvar : Var -> Term
| tcom : OpSymbol -> list Term -> Term .


(* TODO: Σ-Algebra ? *)
Record Algebra :=
  alg {
      carriers: list Set;
      functions: list Type
    }.





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
*)*)