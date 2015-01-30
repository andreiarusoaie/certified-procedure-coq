Require Import JMeq .
Require Import List .
Require Import String .
Require Import ZArith.
Require Import ListSet.


Inductive Sort : Type :=
| Bool : Sort
| String : Sort
| Int : Sort
.

(*
Inductive Sort : Type :=
| Bool : Sort
| String : Sort
| Int : Sort
| Id : Sort 
| AExp : Sort
| BExp : Sort
| Stmt : Sort
.
*)

Inductive Operation : Type :=
| plus : Operation
| land : Operation
| int : Z -> Operation
. 


(*
Inductive Operation : Type :=
| plus : Operation
| div : Operation
| leq : Operation
| land : Operation
| lnot : Operation
| assgn : Operation
| ifthenelse : Operation
| while : Operation
| stmtlist : Operation
. 
 *)

Import ListNotations.

Definition opSort (o : Operation) : (list Sort) * Sort :=
  match o with
    | plus => ([Int; Int], Int) 
    | land => ([Bool; Bool], Bool)
    | int z => ([], Int)
  end.
(*
Definition opSort (o : Operation) : (list Sort) * Sort :=
  match o with
    | plus => ([AExp; AExp], AExp) 
    | div => ([AExp; AExp], AExp) 
    | leq => ([AExp; AExp], BExp)
    | lnot => ([BExp], BExp)
    | land => ([BExp; BExp], BExp)
    | assgn => ([Id; AExp], Stmt)
    | ifthenelse => ([BExp; Stmt; Stmt], Stmt)
    | while => ([BExp; Stmt], Stmt)
    | stmtlist => ([Stmt; Stmt], Stmt)
  end.
 *)  
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

Inductive WellTyped : Term -> Sort -> Type :=
| wt_var : forall v, WellTyped (tVar v) (vSort v)
| wt_term : forall lt o,
    WellTyped_list lt (fst (opSort o)) ->
    WellTyped (term o lt) (snd (opSort o)) with

WellTyped_list : list Term -> list Sort -> Type :=
| wt_nil : WellTyped_list nil nil
| wt_cons : forall t ts s ss,
              WellTyped t s -> WellTyped_list ts ss -> WellTyped_list (t::ts) (s::ss).
                          
Definition string_eq (s1 s2 : string) :=
  andb (prefix s1 s2) (prefix s2 s1) .


Section Semantics.

  Definition sortSem (s : Sort) : Type :=
    match s with
      | Int => Z
      | Bool => bool
      | String => string
    end.  
  
  Fixpoint operationSemType' (inputs : list Sort) :
    Type := match inputs with
              | nil => unit
              | i :: is' => (sortSem i * operationSemType' is')%type
            end.

  Definition operationSemType  (inputs : list Sort)(output : Sort) : Type :=
    operationSemType' inputs -> sortSem output.

Compute operationSemType' (fst (opSort plus)).
  
  (* semantics for each operation *)
  Definition operationSem (o : Operation) :
    operationSemType (fst (opSort o)) (snd (opSort o)) :=
    match o  as o0 return (operationSemType (fst (opSort o0)) (snd (opSort o0)))with
      | plus => fun xy : Z*(Z*unit) => Zplus (fst xy) (fst (snd xy))
      | land => fun xy : bool*(bool*unit) => andb (fst xy) (fst (snd xy))
      | int z => fun _:unit => z
    end.

  Eval compute in operationSemType (fst (opSort plus)) (snd (opSort plus)).

  Compute operationSem plus (2%Z, (5%Z, tt)) .
  
  Fixpoint termSemType (term : Term) : Type :=
    match term with
      | tVar v => sortSem (vSort v)
(*      | term o _ => operationSemType (fst (opSort o)) (snd (opSort o)) *)
      | term o _ => sortSem (snd (opSort o))
    end.

  Eval compute in termSemType (tVar (var "x" Int)) .
  Eval compute in sortSem (vSort (var "x" Int)).
  Check term (int 1) nil.

  Check operationSem (int 1) tt.
  
  
  Eval compute in termSemType (term plus ((term (int 1) nil)::(term (int 2) nil) ::nil )) .

(*  
Definition    TermSem (rho : forall (x : Var), sortSem (vSort x)) (term : Term) : termSemType term.
Proof.
  destruct term.
Show Proof.

Defined.
*)


  Definition termSort (term : Term) : Sort :=
    match term with
      | tVar v => vSort v
      | term o _ => snd (opSort o)
    end.

Print WellTyped.
  
Program Fixpoint termSem (rho : forall (x : Var), sortSem (vSort x))
        (term : Term)(s : Sort)(wt : WellTyped term s(*termSort term*)) :
  termSemType term := match wt with
                        | wt_var v => rho v
                        | wt_term lt o wt' => operationSem o (termSem_list rho o lt wt')

                      end

with termSem_list
       (rho : forall (x : Var), sortSem (vSort x))
       (o : Operation) (terms : list Term)
       (wt' : WellTyped_list terms (fst (opSort o)))
     :
       operationSemType' (fst (opSort o)) :=
       match wt' in (WellTyped_list l0 l1) return (operationSemType' l1) with
         | wt_nil => tt
         | wt_cons t' ts' _ _ wt1 wts2 => (
             termSem rho t' _ wt1,
             (termSem_list rho o ts' wts2) )
       end.

Next Obligation of termSem_list.
apply (termSem rho t' wt1).

  destruct wt'.
  Show Proof.
  apply tt.
  
  revert rho o .
inversion wt'.
Show Proof.  
simpl in *.
intros rho o.
apply tt.
Qed.


End Semantics.
