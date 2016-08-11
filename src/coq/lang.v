Require Import ml.
Require Import String.
Require Import List.
Require Import Classical.
Require Import ZArith.

Module Lang <: Formulas.

  Open Scope string_scope.

  (* syntax *)
  (*
     Exp ::= Id | Int
           | Exp + Exp

     BExp ::= Bool 
            | Exp <= Exp
            | ! Exp

     Stmt ::= 
            Id = Exp;
            if BExp then Stmt else Stmt
            while BExp do Stmt
            Stmt Stmt
   *)

  Inductive ID : Type :=
  | a : ID
  | b : ID
  | c : ID
  | n : ID
  | i : ID
  | x : ID
  | y : ID
  | s : ID.

  Inductive Var : Type :=
  | A : Var
  | B : Var
  | C : Var
  | N : Var
  | I : Var
  | X : Var
  | Y : Var
  | S : Var.
          
  
  Inductive Exp : Type := 
  | id : ID -> Exp
  | val : Z -> Exp
  | var_exp : Var -> Exp
  | plus : Exp -> Exp -> Exp.
  

  Notation "$ A" := (id A) (at level 100).
  Notation "! A" := (var_exp A) (at level 100).
  Eval compute in ($ a).
  Eval compute in (val 2).
  Eval compute in (! A).
  Eval compute in (plus (! A) ($ a)).  


  Inductive BExp : Type :=
  | TT : BExp
  | FF : BExp
  | var_bexp : Var -> BExp
  | leq : Exp -> Exp -> BExp .

  Eval compute in TT.
  Eval compute in (val 4).
  Eval compute in (leq (! A) (val 3)).
  

  Inductive Stmt : Type :=
  | assign : ID -> Exp -> Stmt
  | var_stmt : Var -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | skip : Stmt
  | seq : Stmt -> Stmt -> Stmt .


  Notation "A <- B " := (assign A B) (at level 100).
  Notation "A ; B" := (seq A B) (at level 100).
  
  Eval compute in  (i <- (val 0)).
  Eval compute in (var_stmt S).
  Eval compute in (ifelse (leq ($ i) ($ n))  (assign s (plus ($ s) ($ i))) skip) .
  Eval compute in (i <- (val 0) ; (s <- (val 0))).
  Eval compute in (i <- (val 0) ; (s <- (val 0)) ;
                   (while (leq ($ i) ($ n))
                          ((s <- (plus ($ s) ($ i))) ;
                           (i <- (plus ($ i) (val 1))))
                   )).
  

  (* configuration *)
  Inductive MapItem := 
  | var_mi : Var -> MapItem
  | item : ID -> Exp -> MapItem.

  Inductive Cfg := 
  | var_cfg : Var -> Cfg
  | cfg : Stmt -> list MapItem -> Cfg .

(*  Notation "A |-> B" := (item_z A B) (at level 100). *)
  Notation "A |-> B" := (item A B) (at level 100).
  Eval compute in (cfg 

                     (i <- (val 0) ; (s <- (val 0)) ;
                   (while (leq ($ i) ($ n))
                          ((s <- (plus ($ s) ($ i))) ;
                           (i <- (plus ($ i) (val 1))))
                   ))
                     
                   ((n |-> (! N)) :: nil)).

  
  (* model and state: equiv classes? *)
  Inductive _exp : Type :=
    | _int : Z -> _exp
    | _plus : _exp -> _exp -> _exp
    | _id : ID -> _exp. 

  Inductive _bexp : Type :=
  | _bool : bool -> _bexp
  | _leq : _exp -> _exp -> _bexp.
                             
  
  Inductive _stmt : Type :=
  | _skip : _stmt
  | _assign : ID -> _exp -> _stmt
  | _ifelse : _bexp -> _stmt -> _stmt -> _stmt 
  | _while : _bexp -> _stmt -> _stmt 
  | _seq : _stmt -> _stmt -> _stmt.
   
  Definition _map_item := (ID * _exp)%type.
  Definition State : Type := (_stmt * list _map_item)%type.
  Inductive Model : Type := 
    | to_m_exp : _exp -> Model
    | to_m_bexp : _bexp -> Model
    | to_m_stmt : _stmt -> Model
    | to_m_map_item : _map_item -> Model
    | to_m_state : State -> Model.



  (* var equality *)
  Definition var_eq (X Y : Var) : bool := 
    match X, Y with
      | A, A => true
      | B, B => true
      | C, C => true
      | N, N => true
      | I, I => true
      | X, X => true
      | Y, Y => true
      | S, S => true
      | _, _ => false
    end.

  Lemma var_eq_true : 
    forall a b, var_eq a b = true <-> a = b.
  Proof.
    intros a b.
    split; intros H.
    - case_eq a; intros Ha; case_eq b; intros Hb; rewrite Ha, Hb in H; simpl in H;
      try inversion H; trivial.
    - rewrite H; case_eq b; intros Hb; simpl; trivial.
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
    - case_eq a; intros Ha; case_eq b; intros Hb; simpl; trivial;
      rewrite Ha, Hb in *; try contradict H; trivial.
 Qed.

  Lemma var_eq_refl : 
    forall x, var_eq x x = true.
  Proof.
    intros x; rewrite var_eq_true; trivial.
  Qed.




  (* MLFormula *)
  Inductive MLFormula : Type :=
    | T : MLFormula
    | pattern: Cfg -> MLFormula 
    | NotML : MLFormula -> MLFormula
    | AndML : MLFormula -> MLFormula -> MLFormula
    | ExistsML : list Var -> MLFormula -> MLFormula

    (* custom: add these by need; 
       TODO: create separate type decls for basic ops and preds.
    *)                                            
    | gteML : Var -> Z -> MLFormula.

  Notation "A >>= B" := (gteML A B) (at level 100).
  
  Eval compute in pattern
                    (cfg 

                     (i <- (val 0) ; (s <- (val 0)) ;
                   (while (leq ($ i) ($ n))
                          ((s <- (plus ($ s) ($ i))) ;
                           (i <- (plus ($ i) (val 1))))
                   ))
                     
                   ((n |-> (! N)) :: nil)).

  Eval compute in AndML T
                     (pattern (cfg 

                     (i <- (val 0) ; (s <- (val 0)) ;
                   (while (leq ($ i) ($ n))
                          ((s <- (plus ($ s) ($ i))) ;
                           (i <- (plus ($ i) (val 1))))
                   ))
                     
                   ((n |-> (! N)) :: nil))).

  Eval compute in AndML
                    (N >>= 0)
                    (pattern (cfg 
                        (i <- (val 0) ; (s <- (val 0)) ;
                        (while (leq ($ i) ($ n))
                           ((s <- (plus ($ s) ($ i))) ;
                            (i <- (plus ($ i) (val 1))))
                        ))
                     ((n |-> (! N)) :: nil))).

  
  (* Valuation *)
  Definition Valuation : Type := Var -> Model .


  (* apply valuations *)
  Fixpoint applyValExp (rho : Valuation) (e : Exp) : option _exp :=
    match e with
      | id j => Some (_id j)
      | val v => Some (_int v)
      | var_exp v => match (rho v) with
                       | to_m_exp e => Some e
                       | _ => None
                     end
      | plus v v' => match (applyValExp rho v), (applyValExp rho v') with
                       | Some e', Some e'' => Some (_plus e' e'')
                       | _, _ => None
                     end
    end.


  Fixpoint applyValBExp (rho : Valuation) (b : BExp) : option _bexp :=
    match b with
      | TT => Some (_bool true)
      | FF => Some (_bool false)
      | var_bexp v => match (rho v) with
                        | to_m_bexp b' => Some b'
                        | _ => None
                      end
      | leq v v' => match (applyValExp rho v), (applyValExp rho v') with
                       | Some e', Some e'' => Some (_leq e' e'')
                       | _, _ => None
                     end
    end.


  Fixpoint applyValStmt (rho: Valuation)(st : Stmt) : option _stmt :=
    match st with
      | assign x' e' => match (applyValExp rho e') with
                          | Some e'' => Some (_assign x' e'')
                          | _ => None
                        end
      | ifelse b' s1 s2 => match (applyValBExp rho b'), (applyValStmt rho s1), (applyValStmt rho s2) with
                             | Some b'', Some s1', Some s2' => Some (_ifelse b'' s1' s2')
                             | _, _, _ => None
                           end
      | while b' s' => match (applyValBExp rho b'), (applyValStmt rho s') with
                         | Some b'', Some s'' => Some (_while b'' s'')
                         | _, _ => None
                       end
      | seq s1 s2 => match (applyValStmt rho s1), (applyValStmt rho s2) with
                       | Some s1', Some s2' => Some (_seq s1' s2')
                       | _, _ => None
                     end
      | skip => Some _skip
      | var_stmt s' => match (rho s') with
                         | to_m_stmt s' => Some s'
                         | _ => None
                       end
    end.
  

  Fixpoint applyValMapItem (rho : Valuation) (mi : MapItem) : option _map_item :=
    match mi with
      | var_mi v => match (rho v) with
                      | to_m_map_item m => Some m
                      | _ => None
                    end
      | item i' v => match (applyValExp rho v) with
                       | Some e' => Some  (i, e')
                       | _ => None
                     end
    end.


  Print Model.
  Print Cfg .
  Print MapItem.

  Fixpoint applyValList (rho: Valuation) (l : list MapItem) : option (list _map_item) :=
    match l with
      | nil => None
      | e :: l' => match (applyValMapItem rho e), (applyValList rho l') with
                     | Some v', Some l'' =>  Some (v' :: l'')
                     | _, _ => None
                   end
    end.
      
  
  Fixpoint applyVal (rho : Valuation) (c : Cfg) : option State := 
    match c with
      | var_cfg v => match (rho v) with
                       | to_m_state s' => Some s'
                       | _ => None
                     end
      | cfg st l => match (applyValStmt rho st), (applyValList rho l) with
                     | Some s',  Some l' => Some (s', l')
                     | _, _ => None
                   end
    end.


  
  

End Lang.
