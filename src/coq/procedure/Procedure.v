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
  Notation "A / B" := (aExpDiv A B) .
  Notation "A * B" := (aExpMult A B) .
  Notation "$ A" := (aExpId A) (at level 40).

  (* Boolean expressions *)
  Inductive BExp :=
    | bExpBool : SymBool -> BExp
    | bExpNeg : BExp -> BExp 
    | bExpLeq : AExp -> AExp -> BExp 
    | bExpLe  : AExp -> AExp -> BExp 
    | bExpEq  : AExp -> AExp -> BExp 
    | bExpAnd : BExp -> BExp -> BExp
    | bExp : BExp -> BExp .

  Notation "! B" := (bExpNeg B) (at level 75) .
  Notation "A && B" := (bExpAnd A B) .
  Notation "A <= B" := (bExpLeq A B) .
  Notation "A = B" := (bExpEq A B) .
  
  (* Stmts *)
  Inductive Stmt :=
    | stmtAssign : string -> AExp -> Stmt
    | stmtIfElse : BExp -> Stmt -> Stmt -> Stmt 
    | stmtWhile : BExp -> Stmt -> Stmt 
    | stmtList : Stmt -> Stmt -> Stmt
    | stmtSkip : Stmt .
  
  Notation "S1 ; S2" := (stmtList S1 S2) (at level 89, left associativity).
(*  Notation "A := B" := (stmtAssign A B) (at level 88, right associativity). *)
  
  (* K sequence *)
  Inductive KSequence :=
    | kra : Stmt -> KSequence -> KSequence 
    | kdot : KSequence .
  Notation "K ~> K'" := (kra K K') (at level 91, left associativity).

  (* Configuration *)
  Inductive Cfg : Type := cfg : KSequence -> State -> Cfg .

  (* Finally, the terms *)
  Definition Term : Type := Cfg .

  Scheme Equality for KSequence.
  Scheme Equality for SymInt.
  Scheme Equality for SymBool.

  
  Definition Term_beq (T1 T2 : Term) :=
    match T1, T2 with
      | cfg KS1 S1, cfg KS2 S2 => andb (KSequence_beq KS1 KS2) (State_beq S1 S2)    end.   









  

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


Inductive Rule : Type := rule : Formula -> Formula -> Rule .
Notation "L => R" := (rule L R) (at level 100) .


Fixpoint Formula_beq (F1 : Formula) (F2 : Formula) : bool :=
  match F1, F2 with
    | bp pi, bp pi' => (Term_beq pi pi')
    | T, T => true
    | notF F11, notF F22 => Formula_beq F11 F22
    | andF F11 F12, andF F21 F22
      => andb (Formula_beq F11 F21) (Formula_beq F12 F22)
    | orF F11 F12, orF F21 F22
      => orb (Formula_beq F11 F21) (Formula_beq F12 F22)
    | impliesF F11 F12, impliesF F21 F22
      => andb (Formula_beq F11 F21) (Formula_beq F12 F22)
    | symF F1, symF F2 => SymBool_beq F1 F2
    | _, _ => false 
  end.

Fixpoint Rule_beq (R1 : Rule) (R2 : Rule) : bool :=
  match R1, R2 with
    | (phi1 => phi1'), (phi2 => phi2') =>
      andb (Formula_beq phi1 phi2) (Formula_beq phi1' phi2')
  end.

Fixpoint beqListRule (L1 : list Rule) (L2 : list Rule) : bool :=
  match L1, L2 with
    | nil, nil => true
    | r1 :: tl1, r2 :: tl2 => andb (Rule_beq r1 r2) (beqListRule tl1 tl2)
    | _, _ => false
  end.



















(* Semantics *)

  Fixpoint evalAexp (s : State) (e : AExp) :=
    match e with
      | aExpSymInt x => Some x
      | aExpId x => lookup x s
      | aExpDiv e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symDiv v1 v2) 
                           | _, _ => None                           
                         end
      | aExpMult e1 e2 => match evalAexp s e1, evalAexp s e2 with
                            | Some v1, Some v2 => Some (symMult v1 v2)
                            | _, _ => None                           
                          end
      | aExpPlus e1 e2 => match evalAexp s e1, evalAexp s e2 with
                            | Some v1, Some v2 => Some (symPlus v1 v2)
                            | _, _ => None                           
                          end
      | aExp e => evalAexp s e
    end.

  Fixpoint evalBexp (s : State) (be : BExp) :=
    match be with
      | bExpBool b => Some b
      | bExpNeg b => match evalBexp s b with
                       | Some v => Some (symNeg v)
                       | _ => None
                     end
      | bExpLeq e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symLeqInt v1 v2)
                           | _, _ => None
                         end
      | bExpLe e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symLeInt v1 v2)
                           | _, _ => None
                         end
      | bExpEq e1 e2 => match evalAexp s e1, evalAexp s e2 with
                           | Some v1, Some v2 => Some (symEqInt v1 v2)
                           | _, _ => None
                         end
      | bExpAnd b1 b2 => match evalBexp s b1, evalBexp s b2 with
                           | Some v1, Some v2 => Some (symAnd v1 v2)
                           | _, _ => None
                         end
      | bExp b => evalBexp s b
    end.

  
Inductive Sem : Rule -> Prop :=
  | stepAssign : forall Env Env' X E V P K,
                   evalAexp Env E = Some V -> update X V Env = Some Env' ->
                   Sem (rule
                        (andF (bp (cfg (kra (stmtAssign X E) K) Env)) P)
                        (andF (bp (cfg (kra stmtSkip K) Env')) P))
  | stepIfThen : forall St1 St2 Env B K P C,
                   evalBexp Env B = Some C ->
                   Sem (rule
                        (andF (bp (cfg (kra (stmtIfElse B St1 St2) K) Env)) (symF P))
                           (andF (bp (cfg (kra St1 K) Env))
                                 (symF (symAnd C P)))
                       )
  | stepIfElse : forall St1 St2 Env B K P C,
                   evalBexp Env B = Some C ->
                   Sem (rule
                        (andF (bp (cfg (kra (stmtIfElse B St1 St2) K) Env)) (symF P))
                           (andF (bp (cfg (kra St2 K) Env))
                                 (symF (symAnd (symNeg C) P)))
                       )
  | stepWhile : forall St Env B K P,
                  Sem (rule
                       (andF (bp (cfg (kra (stmtWhile B St) K) Env)) P)
                       (andF (bp (cfg (kra (stmtIfElse B (stmtList St (stmtWhile B St)) stmtSkip) K) Env)) P))
  | stepList : forall St1 St2 Env K P,
                 Sem (rule
                      (andF (bp (cfg (kra (stmtList St1 St2) K) Env)) P)
                      (andF (bp (cfg (kra St1 (kra St2 K)) Env)) P))
  | stepSkip : forall Env K P,
                 Sem (rule
                      (andF (bp (cfg (kra stmtSkip K) Env)) P)
                      (andF (bp (cfg K Env)) P)) .
















Fixpoint bGetFromMap (M : Map Formula bool) (phi : Formula) : bool :=
  match (Map.get Formula bool M phi Formula_beq) with
    | None => false
    | Some v => v
  end.


Fixpoint get_two (r : Rule) (R : list Rule)
         (M : Map Rule (Map (list Rule) (list Rule))) :=
  match Map.get Rule (Map (list Rule) (list Rule)) M r Rule_beq with
    | Some v => match Map.get (list Rule) (list Rule) v R beqListRule with
                  | Some l => l
                  | None => nil
                end
    | None => nil
  end.
                                                                
                                                   
Fixpoint prove (n : nat) (G0 G S : list Rule)
               (Valid : Map Formula bool) 
               (Derivable : Map Formula bool) (* TODO : S parameter *)
               (Delta : Map Rule (Map (list Rule) (list Rule)))
               (ChooseCirc : Map Formula Rule) (* consistency? *) :=
  match n with
    | 0 => false
    | S m => match G with
               | nil => true
               | (phi => phi') :: Rest =>
                 if (bGetFromMap Valid (impliesF phi phi'))
                 then prove m G0 Rest S Valid Derivable Delta ChooseCirc
                 else
                   match Map.get Formula Rule ChooseCirc phi Formula_beq  with
                     | Some circ => prove m G0
                                          ((get_two (phi => phi') (circ :: nil)
                                                  Delta) ++ Rest)  (* rule, Sem -> Derivatives *)
                                          S Valid Derivable Delta ChooseCirc
                                            
                     | None => if (bGetFromMap Derivable phi)
                               then prove m G0
                                          ((get_two (phi => phi') S Delta) ++ Rest)
                                          S Valid Derivable Delta ChooseCirc
                               else false
                   end
             end
  end.

Extraction prove .


(* Testing *)
Open Scope string_scope.
Definition phi :=
  (andF
     (bp 
        (cfg (kra (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1)))) kdot)
             (("i", symInt "I")::("n", symInt "N")::nil)))
     (symF (symLeqInt (symInt "I") (symInt "N")))).

Definition phi' :=
  (andF
     (bp (cfg kdot
             (("i", (symPlus (symInt "I") (symZ 1)))::("n", symInt "N")::nil)))
     (symF (symLeqInt (symInt "N") (symInt "I")))).


Definition phi1 :=
  (andF
     (bp 
        (cfg (kra
                (stmtIfElse (bExpLe (aExpId "i") (aExpId "n"))
                            (stmtList
                               (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1)))
                               (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1))))
                            )
                            stmtSkip
                )
                                 kdot)
             (("i", symInt "I")::("n", symInt "N")::nil)))
     (symF (symLeqInt (symInt "I") (symInt "N")))).


Check stepIfElse.

Definition phi21 :=
     (andF
        (bp 
           (cfg (kra
                   (stmtList
                      (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1)))
                      (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1))))
                   )
                   kdot)
                (("i", symInt "I")::("n", symInt "N")::nil)))
        (symF (symAnd
                 (symLeInt (symInt "I") (symInt "N"))
                 (symLeqInt (symInt "I") (symInt "N")))
        ))
.

Definition phi22 :=
     (andF
        (bp 
           (cfg (kra stmtSkip kdot)
                (("i", symInt "I")::("n", symInt "N")::nil)))
        (symF (symAnd
                 (symNeg (symLeInt (symInt "I") (symInt "N")))
                 (symLeqInt (symInt "I") (symInt "N")))
        ))
   .

Check stepList.
   
Definition phi3 := 
     (andF
        (bp 
           (cfg (kra
                   
                   (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1)))
                   (kra
                      (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1))))
                      kdot)
                   )
                (("i", symInt "I")::("n", symInt "N")::nil)))
        (symF (symAnd
                 (symLeInt (symInt "I") (symInt "N"))
                 (symLeqInt (symInt "I") (symInt "N")))
        ))
.


Check stepAssign.

Definition phi4 :=
     (andF
        (bp 
           (cfg (kra
                   stmtSkip
                   (kra
                      (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1))))
                      kdot)
                )
                (("i", (symPlus (symInt "I") (symZ 1)))::("n", symInt "N")::nil)))
        (symF (symAnd
                 (symLeInt (symInt "I") (symInt "N"))
                 (symLeqInt (symInt "I") (symInt "N")))
        )).


Definition phi5 := 
     (andF
        (bp 
           (cfg
              (kra
                 (stmtWhile (bExpLe (aExpId "i") (aExpId "n")) (stmtAssign "i" ($ "i" + aExpSymInt (symZ 1))))
                 kdot)
                
              (("i", (symPlus (symInt "I") (symZ 1)))::("n", symInt "N")::nil)))
        (symF (symAnd
                 (symLeInt (symInt "I") (symInt "N"))
                 (symLeqInt (symInt "I") (symInt "N")))
        )).


Lemma tr1 : exists phi', Sem (phi => phi') .
  exists phi1.
  apply stepWhile.
Qed.


Lemma tr21 : exists phi', Sem (phi1 => phi').
  exists phi21.
  apply stepIfThen.
  simpl. trivial.
Qed.

Lemma tr22 : exists phi', Sem (phi1 => phi').
  exists phi22.
  apply stepIfElse.
  simpl. trivial.
Qed.

Lemma tr3 : exists phi', Sem (phi21 => phi') .
  exists phi3.
  apply stepList.
Qed.

Lemma tr4 : exists phi', Sem (phi3 => phi') .
  exists phi4.
  eapply stepAssign; simpl; trivial.
Qed.

Lemma tr5 : exists phi', Sem (phi4 => phi') .
  exists phi5.
  eapply stepSkip.
Qed.


(*
               (Valid : Map Formula bool)
               (Derivable : Map Formula bool)
               (Delta : Map Rule (Map (list Rule) (list Rule)))
               (ChooseCirc : Map Formula Rule) :=

 *)
Definition Derivable1 : Map Formula bool := (phi, true)
                       :: (phi1, true)
                       :: (phi21, true)
                       :: (phi3, true)
                       :: (phi4, true)
                       :: nil.

Check (nil, (phi1 => phi') :: nil) :: nil .

Definition Delta1 : Map Rule (Map (list Rule) (list Rule)) :=
        (phi => phi', (nil, (phi1 => phi') :: nil) :: nil)
     :: (phi1 => phi', (nil, (phi21 => phi') :: (phi22 => phi') :: nil) :: nil)
     :: (phi21 => phi', (nil, (phi3 => phi') :: nil) :: nil)
     :: (phi3 => phi', (nil, (phi4 => phi') :: nil) :: nil)
     :: (phi4 => phi', (nil, (phi5 => phi') :: nil) :: nil)
     :: (phi5 => phi', ((phi => phi') :: nil, (phi' => phi') :: nil) :: nil)
     :: nil.


Definition Valid1 : Map Formula bool :=
  (impliesF phi1 phi', true) :: nil .
Definition Valid2 : Map Formula bool :=
  (impliesF phi5 phi', true) :: nil .



Definition ChooseCirc1 : Map Formula Rule :=
  (phi5, phi => phi') :: nil.
Definition ChooseCirc2 : Map Formula Rule :=
  (phi1, phi => phi') :: nil.



Print prove.


Eval compute in (prove 10
                       ((phi => phi') :: nil)
                       ((phi1 => phi') :: nil)
                       nil Valid1 Derivable1 Delta1 ChooseCirc1) .

(*
Eval compute in bGetFromMap Valid2 (impliesF phi1 phi') .
Eval compute in Map.get Formula Rule ChooseCirc2 phi1 Formula_beq.
Eval compute in (delta (phi => phi') ((phi => phi') :: nil) Delta1).
*)

Eval compute in (prove 10
                       ((phi => phi') :: nil)
                       ((phi1 => phi') :: nil)
                       nil Valid2 Derivable1 Delta1 ChooseCirc1) .
