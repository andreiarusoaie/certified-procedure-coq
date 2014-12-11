Require Import ZArith .
Require Import List .
Require Import Model .
Require Import Map .
Require Import String .
Import ImpModel .


  (* Arithmetic expressions *)
  Inductive AExp :=
    | aExpSymInt : SymInt -> AExp                  
    | aExpId : string -> AExp 
    | aExpDiv : AExp -> AExp -> AExp 
    | aExpMult : AExp -> AExp -> AExp 
    | aExpPlus : AExp -> AExp -> AExp 
    | aExp : AExp -> AExp .


Notation "A + B" := (aExpPlus A B) .



  (* Boolean expressions *)
  Inductive BExp :=
    | bExpBool : SymBool -> BExp
    | bExpNeg : BExp -> BExp 
    | bExpLeq : AExp -> AExp -> BExp 
    | bExpAnd : BExp -> BExp -> BExp
    | bExp : BExp -> BExp .


  Scheme Equality for BExp .
  
  
  (* Stmts *)
  Inductive Stmt :=
    | stmtAssign : string -> AExp -> Stmt
    | stmtIfElse : BExp -> Stmt -> Stmt -> Stmt 
    | stmtWhile : BExp -> Stmt -> Stmt 
    | stmtList : Stmt -> Stmt -> Stmt 
    | stmtSkip : Stmt .

Scheme Equality for Stmt.
  Print Stmt_beq.

  (* K sequence *)
  Inductive KSequence :=
    | kra : Stmt -> KSequence -> KSequence 
    | kdot : KSequence .
  Notation "K ~> K'" := (kra K K') (at level 99).

  (* Configuration *)
  Inductive Cfg : Type := cfg : KSequence -> State -> Cfg .

  (* Finally, the terms *)
  Definition Term : Type := Cfg .











  

Inductive Var : Type := varF : Z -> Var .
(* Matching logic formulas *)
Inductive Formula : Type :=
  | bp : Term -> Formula
  | T : Formula 
  | notF : Formula -> Formula
  | andF : Formula -> Formula -> Formula
  | orF : Formula -> Formula -> Formula
  | impliesF : Formula -> Formula -> Formula 
  | existsF : Var -> Formula -> Formula
  | symF : SymBool -> Formula 
.

(* Rules = Reachability Logic formulas *)
Inductive Rule : Type := rule : Formula -> Formula -> Rule .
Notation "L => R" := (rule L R) (at level 100) .



(* TODO: either implement this correctly or search for a different solution *)
Fixpoint beqFormula (F1 : Formula) (F2 : Formula) : bool :=
  match F1, F2 with
    | bp pi, bp pi' => true (* TODO: fix this *)
    | T, T => true
    | notF F11, notF F22 => beqFormula F11 F22
    | andF F11 F12, andF F21 F22
      => andb (beqFormula F11 F21) (beqFormula F21 F22)
    | orF F11 F12, andF F21 F22
      => orb (beqFormula F11 F21) (beqFormula F21 F22)
    | impliesF F11 F12, andF F21 F22
      => implb (beqFormula F11 F21) (beqFormula F21 F22)
    | existsF V1 F11, existsF V2 F22
      => beqFormula F11 F22 (* TODO: fix this *)
    | symF _, symF _ => true (* TODO: fix this *)
    | _, _ => false 
  end.

(* TODO: why not using strings as keys for maps ? *)
Fixpoint beqRule (R1 : Rule) (R2 : Rule) : bool :=
  match R1, R2 with
    | (phi1 => phi1'), (phi2 => phi2') =>
      andb (beqFormula phi1 phi2) (beqFormula phi1' phi2')
  end.

Fixpoint beqListRule (L1 : list Rule) (L2 : list Rule) : bool :=
  match L1, L2 with
    | nil, nil => true
    | r1 :: tl1, r2 :: tl2 => andb (beqRule r1 r2) (beqListRule tl1 tl2)
    | _, _ => false
  end.

Fixpoint bGetFromMap (M : Map Formula bool) (phi : Formula) : bool :=
  match (Map.get Formula bool M phi beqFormula) with
    | None => false
    | Some v => v
  end.



Fixpoint delta (r : Rule) (R : list Rule)
         (M : Map Rule (Map (list Rule) (list Rule))) :=
  match Map.get Rule (Map (list Rule) (list Rule)) M r beqRule with
    | Some v => match Map.get (list Rule) (list Rule) v R beqListRule with
                  | Some l => l
                  | None => nil
                end
    | None => nil
  end.



Eval compute in ((1,2) :: nil) ++ ((2,3) ::nil).

Fixpoint prove (n : nat) (G0 G S : list Rule)
               (Valid : Map Formula bool)
               (DerivableS : Map Formula bool) (* TODO : S parameter *)
               (DeltaS : Map Rule (Map (list Rule) (list Rule))) (* TODO : S parameter *)
               (DeltaCirc : Map Rule (Map (list Rule) (list Rule))) (* TODO : Circ parameter *)
               (ChooseCirc : Map Formula Rule) :=
  match n with
    | 0 => false
    | S m => match G with
               | nil => true
               | (phi => phi') :: Rest =>
                 if (bGetFromMap Valid (impliesF phi phi'))
                 then prove m G0 Rest S Valid DerivableS DeltaS DeltaCirc ChooseCirc
                 else
                   match Map.get Formula Rule ChooseCirc phi beqFormula  with
                     | Some circ => prove m G0
                                          ((delta (phi => phi') (circ :: nil)
                                                  DeltaCirc) ++ Rest)
                                          S Valid DerivableS DeltaS DeltaCirc ChooseCirc
                                            
                     | None => if (bGetFromMap DerivableS phi)
                               then prove m G0
                                          ((delta (phi => phi') S DeltaS) ++ Rest)
                                          S Valid DerivableS DeltaS DeltaCirc ChooseCirc
                               else false
                   end
             end
  end.

Extraction prove .


(* Testing *)

(*
Definition DeltaS : Map Formula Formula := nil .
Definition DeltaCirc : Map Formula Formula := nil .
Definition Valid : Map Formula bool := nil .
Definition Derivable : Map Formula bool := nil .

Definition Valid1 : Map Formula bool :=
  (symF (symB true), true) :: nil.

Open Scope string_scope.
Definition G :=
  ((bp (cfg
         ((stmtAssign "n" (aExpSymInt (symZ 2))) ~> kdot)
         (("n", symZ 4) :: nil)
      ))
  =>
  (bp (cfg
         (kdot)
         (("n", symZ 2) :: nil)
      )))
    :: nil.

Eval compute in (prove 10 G G Valid1 Derivable DeltaS) .

*)