Require Import symbolic.
Require Import List.
Require Import String.

(* k-style-with-eval *)

Module Lang.  
  Import Symbolic .


  (* syntax *)
  Inductive AExp : Type := 
  | id : string -> AExp
  | val : _nat -> AExp
  | plus : AExp -> AExp -> AExp
  | div : AExp -> AExp -> AExp 
  | mod : AExp -> AExp -> AExp
  | aexp_var : string -> AExp .

  Inductive BExp : Type :=
  | bval : _bool -> BExp 
  | not : BExp -> BExp 
  | and : BExp -> BExp -> BExp 
  | le  : AExp -> AExp -> BExp 
  | leq : AExp -> AExp -> BExp
  | eq  : AExp -> AExp -> BExp.

  Inductive Stmt : Type :=
  | assign : string -> AExp -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt 
  | seq : Stmt -> Stmt -> Stmt .

  Notation "X ::= A" := (assign X A) (at level 99). 
  
         
  (* configuration *)
  Definition MapItem := (string * AExp)%type .
  Notation "X |-> A" := (X, A) (at level 100).

  Definition Mem := list MapItem.
  Definition Cfg := (Stmt * Mem)%type .
  Notation "< S > < M >" := (S, M) (at level 101).

(*

  (* lookup *)
  Fixpoint lookup (I : string) (M : State) : option snat := 
    match M with
      | nil => None 
      | (X |-> Y) :: M' => if (string_dec X I) then Some Y else (lookup I M') 
    end.

  Fixpoint evalAExp (A : AExp) (M : State) : option snat := 
    match A with
      | (id X) => match (lookup X M) with None => None | Some V => Some V end 
      | (sval X) => Some X
      | (plus A B) => match (evalAExp A M), (evalAExp B M) with
                        | Some V, Some V' => Some (V +nat V')
                        | _, _ => None 
                      end
      | (div A B) => match (evalAExp A M), (evalAExp B M) with
                       | Some V, Some V' => Some (V /nat V')
                       | _, _ => None 
                     end
      | (mod A B) => match (evalAExp A M), (evalAExp B M) with
                       | Some V, Some V' => Some (V %nat V')
                       | _, _ => None 
                     end
    end.
  
  Fixpoint evalBExp (B : BExp) (M : State) : option sbool :=
    match B with 
      | (bval X) =>  Some X
      | (not X)  =>  match (evalBExp X M) with
                       | Some V => Some (!bool V)
                       | _ => None 
                     end
      | (and X Y) => match (evalBExp X M), (evalBExp Y M) with
                       | Some V, Some V' => Some (V &&bool V')
                       | _, _ => None 
                     end
      | (le X Y) => match (evalAExp X M), (evalAExp Y M) with
                      | Some V, Some V' => Some (V <nat V')
                      | _, _ => None 
                    end
      | (leq X Y) => match (evalAExp X M), (evalAExp Y M) with
                      | Some V, Some V' => Some (V <=nat V')
                      | _, _ => None 
                     end
    end.

  (* update *)
  Fixpoint update (I : string) (A : AExp) (M : State) : State := 
    match M with
      | nil => match (evalAExp A M) with
                 | Some V => (I |-> V) :: nil
                 | None => nil
               end
      | (X |-> Y) :: M' => if (string_dec X I) 
                           then match (evalAExp A M) with
                                  | Some V => (X |-> V) :: M' 
                                  | None => M 
                                end
                           else (X |-> Y) :: (update  I A M') 
    end.

   (* statements *)
  Fixpoint exec (S : Stmt) (M : State) : State :=
    match S with 
      | 
  
  



  Eval compute in (id "a") .
*)
End Lang.