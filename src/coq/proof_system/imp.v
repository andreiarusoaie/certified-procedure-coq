(* Imports *)
Require Import ZArith String Bool .
Require Import List.
Require Import Model .

Open Scope Z_scope.
Import ImpModel.

(* Instantiate Terms with IMP syntax *)
Module ImpSyntax (* <: TERM *) .
  
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
  (*
  Notation "K ~> K'" := (kra K K') (at level 99).
   *)

  (* Configuration *)
  Inductive Cfg : Type := cfg : KSequence -> State -> Cfg .

  (* Finally, the terms *)
  Definition Term : Type := Cfg .

End ImpSyntax.


(* Module Import F := MLFormula (ImpSyntax) . *)
Import ImpSyntax .
  (* Variables - ??? *)
  Inductive Var : Set := varF : Z -> Var .
  (* Matching logic formulas *)
  Inductive Formula : Type :=
    | bp : Term -> Formula
    | T : Formula 
    | andF : Formula -> Formula -> Formula
    | orF : Formula -> Formula -> Formula
    | notF : Formula -> Formula
    | impliesF : Formula -> Formula -> Formula 
    | existsF : Var -> Formula -> Formula
    | symF : SymBool -> Formula 
  .
   
  (* Rules = Reachability Logic formulas *)
  Inductive Rule : Type := rule : Formula -> Formula -> Rule .
  Notation "L => R" := (rule L R) (at level 100).
  
  (* Reachability rules system *)
  Definition System := Rule -> Prop .

  (* TODO: move this in its own file ? *)
  Definition Valid (phi : Formula) := True.
  


(* Semantics *)
Inductive S : System :=
  | stepAssign : forall Env Env' X E V P K,
                   evalAexp Env E = Some V -> update X V Env = Some Env' ->
                   S (rule
                        (andF (bp (cfg (kra (stmtAssign X E) K) Env)) P)
                        (andF (bp (cfg (kra stmtSkip K) Env')) P))
  (* trick -> get rid of delta *)
  | stepIfElse : forall St1 St2 Env B K P C,
                   evalBexp Env B = Some C ->
                   S (rule
                        (andF (bp (cfg (kra (stmtIfElse B St1 St2) K) Env)) (symF P))
                        (orF
                           (andF (bp (cfg (kra St1 K) Env))
                                 (symF (symAnd C P)))
                           (andF (bp (cfg (kra St2 K) Env))
                                 (symF (symAnd (symNeg C) P)))))
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






(* Module Import PS := ProofSystem.ProofSystem (ImpSyntax) . *)

  (* TODO: implement the functions below *)
  Fixpoint delta_S (phi : Formula) (S : System) : Formula := phi .
  Fixpoint delta_G (phi : Formula) (C : Rule) : Formula := phi .
  Fixpoint covers (r : Rule) (phi : Formula) := True .
  Fixpoint derivable (phi : Formula) (S : System) := True .

  Inductive PS : System -> System -> Rule -> Prop :=
    | ps_ss : forall (S : System) (G : System)
                     (phi : Formula) (phi' : Formula),
                derivable phi S -> PS S G (phi => (delta_S phi S))
    | ps_circ : forall (S : System) (G : System)
                       (phi : Formula) (phi' : Formula) (phi'' : Formula),
                  G (phi' => phi'') -> covers (phi' => phi'') phi ->
                  PS S G (phi => (delta_G phi (phi' => phi'')))
    | ps_impl : forall (S : System) (G : System)
                       (phi : Formula) (phi' : Formula),
            Valid (impliesF phi phi') -> PS S G (phi => phi')
    | ps_ca : forall (S : System) (G : System)
                     (phi : Formula) (phi' : Formula) (phi'' : Formula),
                PS S G (phi' => phi) -> PS S G (phi'' => phi)
                -> PS S G ((orF phi' phi'') => phi)
    | ps_trans : forall (S : System) (G : System)
                        (phi : Formula) (phi' : Formula) (phi'' : Formula),
                   PS S G (phi => phi'') -> PS S G (phi'' => phi') -> PS S G (phi => phi') .







Open Scope string_scope .

Inductive G : System :=
  | circularity : forall N Sum I, 
                    G ((andF
               (bp
                  (cfg
                     (kra (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                     (stmtList (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                               (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)) ))))
                          kdot)
                     (("n", N)::("i", I)::("s", Sum)::nil) ))
               (symF (symAnd
                        (symLeInt (symZ 0) N)
                        (symEqInt Sum (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))
                     ))
            )
            =>
            (andF (bp (cfg (kra stmtSkip kdot)
                           (("n", N)::("i", (symPlus I (symZ 1)))::("s", (symDiv (symMult (symPlus I (symZ 1)) (symPlus I (symZ 2))) (symZ 2)))::nil))) T)) .



Axiom reduceToSem : forall (S : System) (G : System)
                           (phi : Formula) (phi' : Formula),
                      S (phi => phi') -> PS S G (phi => phi') .

(* Take care with this! :-) *)
Axiom reduceToCirc : forall (S : System) (G : System)
                           (phi : Formula) (phi' : Formula),
                      G (phi => phi') -> PS S G (phi => phi') .


  


Lemma sum :
  forall N I Sum,
    PS S G ((andF
               (bp
                  (cfg
                     (kra (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                     (stmtList (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                               (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)) ))))
                          kdot)
                     (("n", N)::("i", I)::("s", Sum)::nil) ))
               (symF (symAnd
                        (symLeInt (symZ 0) N)
                        (symEqInt Sum (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))
                     ))
            )
            =>
            (andF (bp (cfg (kra stmtSkip kdot)
                           (("n", N)::("i", (symPlus I (symZ 1)))::("s", (symDiv (symMult (symPlus I (symZ 1)) (symPlus I (symZ 2))) (symZ 2)))::nil))) T)) .
Proof.
  intros.

  apply ps_trans with
  (phi'' :=
    (andF
        (bp
           (cfg
              (kra (stmtIfElse (bexpLeq (aexpId "i") (aexpId "n"))
                          (stmtList
                          (stmtList
                             (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                             (stmtAssign "i"
                                         (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)))))
                          (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                     (stmtList
                                        (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                        (stmtAssign "i"
                                                    (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))))) stmtSkip)
                   kdot) (("n", N) :: ("i", I) :: ("s", Sum) :: nil)))
      (symF
         (symAnd (symLeInt (symZ 0) N)
                 (symEqInt Sum
                           (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2))))))
  ).


  - apply reduceToSem.
    apply stepWhile.
  - apply ps_trans with
    (phi'' :=
       (orF
          (andF
             (bp
                (cfg
                   (kra 
                      (stmtList
                         (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                         (stmtList
                            (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                            (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                       (stmtList
                                          (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                          (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))))))
                   kdot)
                   (("n", N) :: ("i", I) :: ("s", Sum) :: nil)))
             (symF
                (symAnd (symLeInt I N)
                        (symAnd (symLeInt (symZ 0) N)
                                (symEqInt Sum (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))))))
          (andF
             (bp
                (cfg
                   (kra stmtSkip kdot)
                   (("n", N) :: ("i", I) :: ("s", Sum) :: nil)))
             (symF
                (symAnd (symNeg (symLeInt I N))
                        (symAnd (symLeInt (symZ 0) N)
                                (symEqInt Sum (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))))))
          
       )).
    +
      apply ps_trans with
      (phi'' := andF
        (bp
           (cfg
              (kra
                 (stmtIfElse (bexpLeq (aexpId "i") (aexpId "n"))
                             (stmtList
                                (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                (stmtList
                                   (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                                   (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                              (stmtList
                                                 (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                                 (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)))))))
                                )
                    stmtSkip) kdot)
              (("n", N) :: ("i", I) :: ("s", Sum) :: nil)))
        (symF
           (symAnd (symLeInt (symZ 0) N)
              (symEqInt Sum
                        (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))))
        ).

      apply ps_impl.
      unfold Valid. trivial.

      apply reduceToSem.
      apply stepIfElse.
      simpl. auto. 

    + apply ps_ca.
      * apply ps_trans with
        (phi'' := (
                   andF
                     (bp
                        (cfg
                           (kra
                              (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                              (kra
                                 (stmtList
                                    (stmtAssign "i"
                                                (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                                    (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                               (stmtList
                                                  (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                                  (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)))))))
                                 kdot))
                           (("n", N) :: ("i", I) :: ("s", Sum) :: nil)))
                     (symF
                        (symAnd (symLeInt I N)
                                (symAnd (symLeInt (symZ 0) N)
                                        (symEqInt Sum
                                                  (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2))))))
                 )).
        
        apply reduceToSem.
        apply stepList.

        apply ps_trans with
        (phi'' :=
           (andF
              (bp
                 (cfg
                    (kra stmtSkip
                         (kra
                            (stmtList
                               (stmtAssign "i"
                                           (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                               (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                          (stmtList
                                             (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                             (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)))))))
                            kdot)) (("n", N) :: ("i", I) :: ("s", (symPlus Sum I)) :: nil)))
              (symF
                 (symAnd (symLeInt I N)
                         (symAnd (symLeInt (symZ 0) N)
                                 (symEqInt Sum
                                           (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2))))))
           )).

        apply reduceToSem.

        (*  evalAexp Env E = Some V -> update X V Env = Some Env'  *)
(*        Eval compute in  evalAexp (("n", N) :: ("i", I) :: ("s", Sum) :: nil)
                                   (aexpPlus (aexpId "s") (aexpId "i")).
*)        
        apply stepAssign with (V := (symPlus Sum I)) .
        simpl. trivial.
        simpl. trivial.
        

        apply ps_trans with
        (phi'' :=
           (andF
              (bp
                 (cfg
                         (kra
                            (stmtList
                               (stmtAssign "i"
                                           (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                               (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                          (stmtList
                                             (stmtAssign "s"
                                (aexpPlus (aexpId "s") (aexpId "i")))
                                             (stmtAssign "i"
                                                         (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)))))))
                            kdot)
                    (("n", N) :: ("i", I) :: ("s", symPlus Sum I) :: nil)))
              (symF
                 (symAnd (symLeInt I N)
                         (symAnd (symLeInt (symZ 0) N)
                                 (symEqInt Sum
                                           (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2))))))
           )
        ).

        apply reduceToSem.
        apply stepSkip.



        apply ps_trans with
        (phi'' :=
           (andF
        (bp
           (cfg
              (kra
                 (stmtAssign "i"
                       (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))
                 (kra
                    
                    (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                       (stmtList
                          (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                          (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))))
                 kdot)) (("n", N) :: ("i", I) :: ("s", symPlus Sum I) :: nil)))
        (symF
           (symAnd (symLeInt I N)
              (symAnd (symLeInt (symZ 0) N)
                 (symEqInt Sum
                    (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2))))))
        )).


        apply reduceToSem.
        apply stepList.


        apply ps_trans with
        (phi'' :=
           (andF
              (bp
                 (cfg
                    (kra
                       stmtSkip
                       (kra
                          (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                     (stmtList
                                        (stmtAssign "s"
                                                    (aexpPlus (aexpId "s") (aexpId "i")))
                                        (stmtAssign "i"
                                                    (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))))
                          kdot))
                    (("n", N) :: ("i", symPlus I (symZ 1)) :: ("s", symPlus Sum I) :: nil)))
              (symF
                 (symAnd (symLeInt I N)
                         (symAnd (symLeInt (symZ 0) N)
                                 (symEqInt Sum
                                           (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))))))
        ).

        apply reduceToSem.
        apply stepAssign with (V := symPlus I (symZ 1)).
        simpl. trivial.
        simpl. trivial.

        apply ps_trans with
        (phi'' :=
           (andF
              (bp
                 (cfg
                         (kra
                            (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                       (stmtList
                                          (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                          (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1))))))
                            kdot)
                    (("n", N)
                       :: ("i", symPlus I (symZ 1)) :: ("s", symPlus Sum I) :: nil)))
              (symF
                 (symAnd (symLeInt I N)
                         (symAnd (symLeInt (symZ 0) N)
                                 (symEqInt Sum
                                           (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))))))
        ).

        apply reduceToSem.
        apply stepSkip.


        (* prepare for circularity *)
        apply ps_trans with
        (phi'' :=
           (andF
               (bp
                  (cfg
                     (kra (stmtWhile (bexpLeq (aexpId "i") (aexpId "n"))
                                     (stmtList (stmtAssign "s" (aexpPlus (aexpId "s") (aexpId "i")))
                                               (stmtAssign "i" (aexpPlus (aexpId "i") (aexpSymInt (symZ 1)) ))))
                          kdot)
                     (("n", N)::("i", I)::("s", Sum)::nil) ))
               (symF (symAnd
                        (symLeInt (symZ 0) N)
                        (symEqInt Sum (symDiv (symMult I (symPlus I (symZ 1))) (symZ 2)))
                     ))
           )
        ).

        apply ps_impl.
        unfold Valid. trivial.


        (* circularity -> apply ps_circ. *)
        apply reduceToCirc.
        apply circularity.

      * apply ps_impl.
        unfold Valid. trivial.
Qed.

