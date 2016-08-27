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

  Inductive VarExp : Type :=
  | N : VarExp
  | I : VarExp
  | X : VarExp
  | Y : VarExp
  | S : VarExp.
  Inductive VarBExp : Type :=
  | B : VarBExp.
  Inductive VarStmt : Type :=
  | St : VarStmt
  | S1 : VarStmt
  | S2 : VarStmt.
  Inductive VarMI : Type :=
  | M : VarMI .
  Inductive VarMList : Type :=
  | Rest : VarMList .
  Inductive VarCfg : Type :=
  | C : VarCfg.
  Inductive SpecialVar : Type :=
  | ZZ : SpecialVar.
  
  
  Inductive Exp : Type := 
  | id : ID -> Exp
  | val : Z -> Exp
  | var_exp : VarExp -> Exp
  | plus : Exp -> Exp -> Exp.
  

  Notation "$ A" := (id A) (at level 100).
  Notation "! A" := (var_exp A) (at level 100).
  Eval compute in ($ a).
  Eval compute in (val 2).
  Eval compute in (! N).
  Eval compute in (plus (! N) ($ a)).  


  Inductive BExp : Type :=
  | TT : BExp
  | FF : BExp
  | var_bexp : VarBExp -> BExp
  | leq : Exp -> Exp -> BExp .

  Eval compute in TT.
  Eval compute in (val 4).
  Eval compute in (leq (! N) (val 3)).
  

  Inductive Stmt : Type :=
  | assign : ID -> Exp -> Stmt
  | var_stmt : VarStmt -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | skip : Stmt
  | seq : Stmt -> Stmt -> Stmt .


  Notation "A <- B " := (assign A B) (at level 100).
  Notation "A ; B" := (seq A B) (at level 100).
  
  Eval compute in  (i <- (val 0)).
  Eval compute in (var_stmt St).
  Eval compute in (ifelse (leq ($ i) ($ n))  (assign s (plus ($ s) ($ i))) skip) .
  Eval compute in (i <- (val 0) ; (s <- (val 0))).
  Eval compute in (i <- (val 0) ; (s <- (val 0)) ;
                   (while (leq ($ i) ($ n))
                          ((s <- (plus ($ s) ($ i))) ;
                           (i <- (plus ($ i) (val 1))))
                   )).
  

  (* configuration *)
  Inductive MapItem := 
  | var_mi : VarMI -> MapItem
  | item : ID -> Exp -> MapItem.

  Inductive Cfg := 
  | var_cfg : VarCfg -> Cfg
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
  Inductive Model' : Type := 
    | to_m_exp : _exp -> Model'
    | to_m_bexp : _bexp -> Model'
    | to_m_stmt : _stmt -> Model'
    | to_m_map_item : _map_item -> Model'
    | to_m_state : State -> Model'.
  Definition Model := Model'.
  

  Inductive Var' : Type :=
  | evar : VarExp -> Var'
  | bvar : VarBExp -> Var'
  | svar : VarStmt -> Var'
  | mivar : VarMI -> Var'
  | lvar : VarMList -> Var'
  | cvar : VarCfg -> Var'
  | spvar : SpecialVar -> Var'.
  Definition Var := Var'.

  (* Valuation *)
  Definition Valuation := Var -> Model .
  
  (* var equality *)
  Definition var_eq (X Y : Var) : bool := 
    match X, Y with
      | evar e1, evar e2 => match e1, e2 with
                              | N, N => true
                              | I, I => true
                              | X, X => true
                              | Y, Y => true
                              | S, S => true
                              | _, _ => false
                            end
      | bvar b1, bvar b2 => match b1, b2 with
                              | B, B => true
                            end
      | svar s1, svar s2 => match s1, s2 with
                              | St, St => true
                              | S1, S1 => true
                              | S2, S2 => true
                              | _, _ => false
                            end
      | mivar m1, mivar m2 => match m1, m2 with
                              | M, M => true
                            end
      | lvar l1, lvar l2 => match l1, l2 with
                              | Rest, Rest => true
                            end
      | cvar c1, cvar c2 => match c1, c2 with
                              | C, C => true
                            end
      | spvar c1, spvar c2 => match c1, c2 with
                                | ZZ, ZZ => true
                              end
      | _, _ => false
    end.

  
  Lemma var_eq_true : 
    forall a b, var_eq a b = true <-> a = b.
  Proof.
    intros a b.
    split; intros H.
    - case_eq a; intros va Ha; case_eq b; intros vb Hb; rewrite Ha, Hb in H;
      case_eq va; intros Hva; case_eq vb; intros Hvb; rewrite Hva, Hvb in H;
      simpl in H; try inversion H; trivial.
    - rewrite H. case_eq b; intros v Hv; case_eq v; intros Hv'; trivial.
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
    - case_eq a; intros a' Ha; case_eq b; intros b' Hb; simpl;
      case_eq a'; intros Ha'; case_eq b'; intros Hb'; subst; trivial;
      try contradict H; trivial.
 Qed.

  Lemma var_eq_refl : 
    forall x, var_eq x x = true.
  Proof.
    intros x; rewrite var_eq_true; trivial.
  Qed.

  Inductive MLFormula' : Type :=
  | T : MLFormula'
  | pattern: Cfg -> MLFormula'
  | AndML' : MLFormula' -> MLFormula' -> MLFormula'
  | ImpliesML' : MLFormula' -> MLFormula' -> MLFormula'
  | ExistsML' : list Var -> MLFormula' -> MLFormula'
                                           
  (* custom: add these by need; 
       TODO: create separate type decls for basic ops and preds.
   *)
  | encoding' : MLFormula' -> MLFormula'
  | gteML : Exp -> Exp -> MLFormula'.

  Definition AndML := AndML'.
  Definition ImpliesML := ImpliesML'.
  Definition ExistsML := ExistsML'.
  Definition MLFormula := MLFormula'.
  Definition encoding := encoding'.
  
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
                    (! N >>= (val 0))
                    (pattern (cfg 
                        (i <- (val 0) ; (s <- (val 0)) ;
                        (while (leq ($ i) ($ n))
                           ((s <- (plus ($ s) ($ i))) ;
                            (i <- (plus ($ i) (val 1))))
                        ))
                     ((n |-> (! N)) :: nil))).


  (* apply valuations *)
  Fixpoint applyValExp (rho : Valuation) (e : Exp) : option _exp :=
    match e with
      | id j => Some (_id j)
      | val v => Some (_int v)
      | var_exp v => match (rho (evar v)) with
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
      | var_bexp v => match (rho (bvar v)) with
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
      | var_stmt s' => match (rho (svar s')) with
                         | to_m_stmt s' => Some s'
                         | _ => None
                       end
    end.
  

  Fixpoint applyValMapItem (rho : Valuation) (mi : MapItem) : option _map_item :=
    match mi with
      | var_mi v => match (rho (mivar v)) with
                      | to_m_map_item m => Some m
                      | _ => None
                    end
      | item i' v => match (applyValExp rho v) with
                       | Some e' => Some  (i, e')
                       | _ => None
                     end
    end.



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
      | var_cfg v => match (rho (cvar v)) with
                       | to_m_state s' => Some s'
                       | _ => None
                     end
      | cfg st l => match (applyValStmt rho st), (applyValList rho l) with
                     | Some s',  Some l' => Some (s', l')
                     | _, _ => None
                   end
    end.

  
  Fixpoint red_exp (e : _exp) : option Z :=
    match e with
      | _int z' => Some z'
      | _plus e1 e2 => match (red_exp e1), (red_exp e2) with
                         | Some z1, Some z2 => Some (Z.add z1 z2)
                         | _, _ => None
                       end
      | _ => None
    end.

   Fixpoint SatML (gamma : State) (rho : Valuation) (phi : MLFormula) : Prop :=
    match phi with
      | T => True
      | pattern pi => (applyVal rho pi) = Some gamma (* rho(pi) = gamma *) 
      | AndML phi1 phi2 => SatML gamma rho phi1 /\ SatML gamma rho phi2
      | ImpliesML phi1 phi2 => SatML gamma rho phi1 -> SatML gamma rho phi2
      | ExistsML xs phi' => exists rho',
                            (forall x, ~ In x xs -> rho' x = rho x) /\
                            SatML gamma rho' phi'

      (* custom? *)
      | encoding phi' => exists gamma', SatML gamma' rho phi'
      | gteML e1 e2 => match (applyValExp rho e1), (applyValExp rho e2) with
                         | Some v1, Some v2 => match (red_exp v1), (red_exp v2) with
                                                 | Some z1, Some z2 => (Z.ge z1 z2)
                                                 | _, _ => False
                                               end
                                                   
                         | _, _ => False
                       end
    end.

  

    Lemma SatML_Exists :
      forall phi gamma rho V,
        SatML gamma rho (ExistsML V phi) <->
        exists rho',
          (forall v, ~In v V -> rho v = rho' v) /\
          SatML gamma rho' phi.
    Proof.
      intros phi gamma rho V.
      split; intros H.
      - simpl in H.
        destruct H as (rho' & H1 & H2).
        exists rho'.
        split; trivial.
        intros.
        apply H1 in H.
        rewrite H; trivial.
      - simpl.
        destruct H as (rho' & H1 & H2).
        exists rho'.
        split; trivial.
        intros x0 Hxo.
        apply H1 in Hxo.
        rewrite Hxo; trivial.
    Qed.


    Lemma SatML_And :
      forall gamma rho phi phi',
        SatML gamma rho (AndML phi phi') <->
        SatML gamma rho phi /\ SatML gamma rho phi'.
    Proof.
      intros gamma rho phi phi'; split; intros H.
      - simpl in H; trivial.
      - simpl; trivial.
    Qed.

    Lemma SatML_Implies :
      forall gamma rho phi phi',
        SatML gamma rho (ImpliesML phi phi') <->
        SatML gamma rho phi -> SatML gamma rho phi'.
    Proof.
      intros gamma rho phi phi'; split; intros H.
      - simpl in H; trivial.
      - simpl; trivial.
    Qed.
      

  (* Validity in ML *)
  Definition ValidML (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.


  (* Free variables *)
  Fixpoint in_list (v : Var) (l : list Var) : bool :=
    match l with
      | nil => false
      | v' :: ls => if (var_eq v v') then true else (in_list v ls)
    end.

  Eval compute in (in_list (evar N) (nil)).
  Eval compute in (in_list (evar N) ((evar N) :: nil)).
  Eval compute in (in_list (evar N) ((evar N) :: nil)).
  Eval compute in (in_list (evar N) ((evar S) :: (evar N) :: nil)).

  
  
  Fixpoint append_set (l1 : list Var) (l2 : list Var) : list Var :=
    match l2 with
      | nil => l1
      | j :: ls => if (in_list j l1) then (append_set l1 ls) else (append_set (j :: l1) ls)
    end.

  Eval compute in (append_set (nil) (nil) ).
  Eval compute in (append_set ((evar N) :: nil) (nil) ).
  Eval compute in (append_set (nil) ((evar N) :: nil) ).
  Eval compute in (append_set ((evar N) :: nil) ((evar N) :: nil) ).
  Eval compute in (append_set ((evar N) :: (evar S) :: nil) ((evar N) :: nil) ).
  Eval compute in (append_set ((evar N) :: nil) ((evar S) :: (evar N) :: nil) ).

  Fixpoint minus_elem (l1 : list Var) (v : Var) : list Var :=
    match l1 with
      | nil => nil
      | (v' :: l) => if (var_eq v' v) then minus_elem l v else (v' :: (minus_elem l v))
    end.
  
  Fixpoint minus_set (l1 : list Var) (l2 : list Var) : list Var :=
    match l2 with
      | nil => l1
      | v :: l => minus_set (minus_elem l1 v) l
    end.
  
  Eval compute in (minus_set (nil) (nil) ).
  Eval compute in (minus_set ((evar N) :: nil) (nil) ).
  Eval compute in (minus_set (nil) ((evar N) :: nil) ).
  Eval compute in (minus_set ((evar N) :: nil) ((evar N) :: nil) ).
  Eval compute in (minus_set ((evar N) :: (evar S) :: nil) ((evar N) :: nil) ).
  Eval compute in (minus_set ((evar I) :: (evar N) :: nil) ((evar S) :: (evar N) :: nil) ).

  Fixpoint getFreeVarsExp (e : Exp) : list Var :=
    match e with
      | var_exp v => ((evar v) :: nil)
      | plus e1 e2 => append_set (getFreeVarsExp e1) (getFreeVarsExp e2)
      | _ => nil
    end.

  Eval compute in (getFreeVarsExp ($ a)).
  Eval compute in (getFreeVarsExp (val 2)).
  Eval compute in (getFreeVarsExp (!  N)).
  Eval compute in (getFreeVarsExp (plus (! N) (! N))).  

  Fixpoint getFreeVarsMapItem (mi : MapItem) : list Var :=
    match mi with
      | var_mi v => ((mivar v) :: nil)
      | item h e => (getFreeVarsExp e)
    end.

  Eval compute in (getFreeVarsMapItem ((n |-> (! N)))).
  
  Fixpoint getFreeVarsItems (it : list MapItem) : list Var :=
    match it with
      | nil => nil
      | v :: its => append_set (getFreeVarsMapItem v) (getFreeVarsItems its)
    end.

  Eval compute in (getFreeVarsItems ((n |-> (! N)) :: nil)).


  Fixpoint getFreeVarsBExp (be : BExp) : list Var :=
    match be with
      | var_bexp vb => ((bvar vb) :: nil)
      | leq e1 e2 => append_set (getFreeVarsExp e1) (getFreeVarsExp e2)
      | _ => nil
    end.


  Fixpoint getFreeVarsStmt (st : Stmt) : list Var :=
    match st with
      | assign i' e => getFreeVarsExp e
      | var_stmt st => ((svar st) :: nil)
      | ifelse be s1 s2 => append_set (append_set (getFreeVarsBExp be) (getFreeVarsStmt s1)) (getFreeVarsStmt s2)
      | while be st => append_set (getFreeVarsBExp be) (getFreeVarsStmt st)
      | seq s1 s2 => append_set (getFreeVarsStmt s1) (getFreeVarsStmt s2)
      | _ => nil
    end.
  
  Fixpoint getFreeVarsCfg (c : Cfg) : list Var :=
    match c with
      | var_cfg v => ((cvar v) :: nil)
      | cfg st mi => append_set (getFreeVarsStmt st) (getFreeVarsItems mi)
    end.
  
  Fixpoint getFreeVars (phi : MLFormula) : list Var :=
    match phi with
      | T => nil
      | pattern pi => (getFreeVarsCfg pi)
      | AndML phi1 phi2 => append_set (getFreeVars phi1) (getFreeVars phi2)
      | ImpliesML phi1 phi2 => append_set (getFreeVars phi1) (getFreeVars phi2)
      | ExistsML Vs phi' => minus_set (getFreeVars phi') Vs
      | gteML e1 e2 => append_set (getFreeVarsExp e1) (getFreeVarsExp e2)
      | encoding phi' => (getFreeVars phi') (* the encoding doesn't affect the free variable set *)
    end.

  Eval compute in 
      getFreeVars (AndML
                     (! N >>= (val 0))
                     (pattern (cfg 
                                 (i <- (val 0) ; (s <- (val 0)) ;
                                  (while (leq ($ i) (! N))
                                         ((s <- (plus (! S) ($ i))) ;
                                          (i <- (plus ($ i) (val 1))))
                                  ))
                                 ((n |-> (! I)) :: nil))))  .
                   
  (* existential closure *)
  Definition EClos (phi : MLFormula) := (ExistsML (getFreeVars phi) phi).


  (* Modify valuation on set *)
  Definition modify_val_on_var(rho rho' : Valuation) (x : Var) : Valuation :=
    fun z => if (var_eq x z) then rho' x else rho z .
  Fixpoint modify_val_on_set(rho rho' : Valuation) (X : list Var) : Valuation :=
    match X with
      | nil => rho
      | cons x' Xs => modify_val_on_var (modify_val_on_set rho rho' Xs) rho' x'
    end.


  
  (* helper *)
  Lemma modify_in :
    forall V x rho rho',
      In x V -> (modify_val_on_set rho rho' V) x = rho' x.
  Proof.
    induction V; intros.
    - contradiction.
    - simpl in *.
      destruct H as [H | H].
      + subst.
        unfold modify_val_on_var.
        rewrite var_eq_refl.
        reflexivity.
      + unfold modify_val_on_var.
        case_eq (var_eq a0 x0); intros H'.
        * apply var_eq_true in H'.
          subst.
          reflexivity.
        * apply IHV; trivial.
  Qed.
    

  (* helper *)
  Lemma modify_not_in :
    forall V x rho rho',
      ~ In x V -> (modify_val_on_set rho rho' V) x = rho x.
  Proof.
    induction V; intros.
    - simpl.
      reflexivity.
    - simpl in *.
      apply not_or_and in H.
      destruct H as (H & H').
      unfold modify_val_on_var.
      case_eq (var_eq a0 x0); intros H''.
      + apply var_eq_true in H''.
        subst.
        contradict H.
        reflexivity.
      + apply IHV; trivial.
  Qed.

  
  Definition modify_val_on_ZZ(rho : Valuation) (m : State) : Valuation :=
    fun z => if (var_eq z (spvar ZZ)) then to_m_state m else rho z .


  Lemma Proposition1 :
    forall phi gamma' rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
  Proof.
    intros.
    split; intros.
    - simpl in H.
      destruct H as (gamma & H).
      exists gamma; trivial.
    - simpl; trivial.
  Qed.

  Lemma incl_nil :
    forall (X: list Var), incl X nil -> X = nil.
  Proof.
    intros X H.
    induction X; trivial.
    unfold incl in H.
    unfold incl in IHX.
    assert (H' : In a0 (a0 :: X0)).
    - simpl.
      left; trivial.
    - apply H in H'.
      contradiction.
  Qed.
  
  Lemma append_left :
    forall B A a,
      In a A -> In a (append_set A B).
  Proof.
    intros B.
    induction B; intros A a H.
    - simpl.
      trivial.
    - simpl.
      case_eq (in_list a0 A); intros H'.
      + apply IHB; trivial.
      + apply IHB.
        simpl. right. trivial.
  Qed.

  Lemma append_right :
    forall B A a,
      In a B -> In a (append_set A B).
  Proof.
    intros B.
    induction B; intros A a Ha.
    - contradiction.
    - simpl in Ha.
      destruct Ha as [Ha | Ha].
      + subst.
        simpl.
        case_eq (in_list a A); intros H.
        * apply append_left.
          induction A.
          simpl in H.
          inversion H.
          simpl.
          simpl in H.
          case_eq (var_eq a a0); intros H'.
          left.
          apply var_eq_true in H'.
          subst; trivial.
          rewrite H' in H.
          right.
          apply IHA; trivial.
        * apply append_left.
          simpl. left. trivial.
      + simpl.
        case_eq (in_list a0 A); intros H; apply IHB; trivial.
  Qed.
        
  
  Lemma append_set_nil :
    forall B A,
      append_set A B = nil -> A = nil /\ B = nil .
  Proof.
    intros B.
    induction B.
    - intros A H.
      split; trivial.
    - intros A H.
      simpl in H.
      case_eq (in_list a0 A); intros H'.
      + rewrite H' in H.
        apply IHB in H.
        destruct H as (H & H'').
        subst.
        simpl in H'.
        inversion H'.
      + rewrite H' in H.
        apply IHB in H.
        destruct H as (H & H'').
        inversion H.
  Qed.  

  
  Lemma incl_append_left :
    forall V A B,
      incl (append_set A B) V -> incl A V.
  Proof.
    induction V; intros.
    - apply incl_nil in H.
      apply append_set_nil in H.
      destruct H as (H & H').
      subst.
      unfold incl.
      intros a H.
      trivial.
    - unfold incl in H.
      unfold incl.
      intros a Ha.
      apply append_left with (B := B0) in Ha.
      apply H in Ha.
      trivial.
  Qed.

  Lemma incl_append_right :
    forall V A B,
      incl (append_set A B) V -> incl B V.
  Proof.
    induction V; intros.
    - apply incl_nil in H.
      apply append_set_nil in H.
      destruct H as (H & H').
      subst.
      unfold incl.
      intros a H.
      trivial.
    - unfold incl in H.
      unfold incl.
      intros a Ha.
      apply append_right with (A := A) (B := B0) in Ha.
      apply H in Ha.
      trivial.
  Qed.

  Lemma in_append_iff :
    forall B A x,
      In x (append_set A B) <-> In x A \/ In x B.
  Proof.
    split.
    - revert  B0 A x0.
      induction B0.
      + intros.
        simpl in *.
        left. trivial.
      + intros A x H.
        simpl in H.
        case_eq (in_list a0 A); intro H'.
        * rewrite H' in H.
          apply IHB0 in H.
          destruct H as [H | H].
          left. trivial.
          right.
          simpl.
          right. trivial.
        * rewrite H' in H.
          apply IHB0 in H.
          destruct H as [H | H].
          simpl in H.
          destruct H as [H | H].
          subst.
          right.
          simpl.
          left.
          reflexivity.
          left.
          assumption.
          right.
          simpl.
          right.
          assumption.
    - intros.
      destruct H as [H | H].
      apply append_left; trivial.
      apply append_right; trivial.
  Qed.
      
  
  Lemma minus_elem_helper :
    forall A x y, In x A -> x <> y -> In x (minus_elem A y).
  Proof.
    induction A.
    - simpl. trivial.
    - intros x y H H'.
      simpl.
      destruct H as [H | H].
      case_eq (var_eq a0 y); intros K.
      + apply IHA; trivial.
        simpl in H.
        subst.
        apply var_eq_true in K.
        subst.
        contradict H'.
        reflexivity.
      + subst.
        simpl.
        left. reflexivity.
      + case_eq (var_eq a0 y); intros K.
        * apply IHA; trivial.
        * simpl.
          right.
          apply IHA; trivial.
  Qed.

  Lemma minus_elem_helper' :
    forall A x y,
      In x (minus_elem A y) -> In x A /\ x <> y.
  Proof.
    intros A.
    induction A; intros.
    - simpl in H.
      contradiction.
    - simpl in *.
      case_eq (var_eq a0 y0); intros H0; rewrite H0 in *.
      apply IHA in H.
      destruct H as (H & H').
      split.
      + right. trivial.
      + trivial.
      + simpl in H.
        destruct H as [H | H].
        * split.
          left. trivial.
          subst.
          apply var_eq_false.
          trivial.
        * apply IHA in H.
          destruct H as (H & H').
          split; trivial.
          right. trivial.
  Qed.
  
  
  
  Lemma minus_set_helper:
    forall B A x,
      In x A -> ~ In x B -> In x (minus_set A B).
  Proof.
    induction B0.
    - intros.
      simpl.
      assumption.
    - induction A.
      + intros.
        contradiction.
      + intros x H H'.
        destruct H as [H | H].
        subst.
        case_eq (var_eq x a0); intros Ha.
        * contradict H'.
          simpl.
          left.
          apply var_eq_true in Ha.
          subst.
          reflexivity.
        * simpl.
          rewrite Ha.
          apply IHB0.
          simpl. left. reflexivity.
          unfold not.
          intros.
          apply H'.
          simpl.
          right. assumption.
        * simpl.
          case_eq (var_eq a1 a0); intros Ha.
          simpl in H'.
          apply not_or_and in H'.
          destruct H' as (H' & H'').
          apply IHB0; trivial.
          apply var_eq_true in Ha.
          subst.
          apply minus_elem_helper; trivial.
          unfold not in H'.
          unfold not.
          intros.
          apply H'.
          subst.
          reflexivity.
          simpl in H'.
          apply not_or_and in H'.
          destruct H' as (H' & H'').
          apply IHB0; trivial.
          simpl.
          right.
          apply minus_elem_helper; trivial.
          unfold not in *.
          intros.
          apply H'.
          subst.
          trivial.
  Qed.


  Lemma minus_nil :
    forall SET,
      minus_set nil SET = nil.
  Proof.
    induction SET; simpl in *; trivial.
  Qed.            
  
  Lemma minus_set_helper':
    forall B A x,
      In x (minus_set A B) -> In x A /\ ~ In x B.
  Proof.
    intros B.
    induction B; intros A x Hx.
    - simpl in *.
      split; trivial.
      unfold not.
      intros; trivial.
    - simpl in *.
      induction A.
      + simpl in *.
        rewrite minus_nil in Hx.
        contradiction.
      + simpl in *.
        split; case_eq (var_eq a1 a0); intros Ha; rewrite Ha in *.
        * apply IHA in Hx.
          destruct Hx as (Hx & Hx').
          right. trivial.
        * apply IHB in Hx.
          destruct Hx as (Hx & Hx').
          simpl in Hx.
          destruct Hx as [Hx | Hx].
          left. trivial.
          apply minus_elem_helper' in Hx.
          destruct Hx as (Hx & Hx'').
          right. trivial.
        * apply IHB in Hx.
          destruct Hx as (Hx & Hx').
          simpl in Hx.
          apply minus_elem_helper' in Hx.
          destruct Hx as (Hx & Hx'').
          apply and_not_or.
          split; trivial.
          apply var_eq_true in Ha.
          unfold not in *.
          intros.
          apply Hx''.
          subst. trivial.
        * apply IHB in Hx.
          destruct Hx as (Hx & Hx').
          apply and_not_or.
          split; trivial.
          simpl in Hx.
          destruct Hx as [Hx | Hx].
          subst.
          unfold not.
          intros.
          subst.
          apply var_eq_false in Ha.
          apply Ha. trivial.
          apply minus_elem_helper' in Hx.
          destruct Hx as (Hx & Hx'').
          unfold not in *.
          intros.
          apply Hx''.
          subst.
          reflexivity.
  Qed.
        

  Lemma incl_exp :
    forall e rho rho' V,
      incl (getFreeVarsExp e) V ->
      applyValExp rho' e = applyValExp (modify_val_on_set rho rho' V) e.
  Proof.
    induction e; intros.
    - simpl in *. trivial.
    - simpl in *. trivial.
    - simpl in *.
      unfold incl in H.
      assert (H' : In (evar v) (evar v :: nil)).
      simpl. left. trivial.
      apply H in H'.
      apply modify_in with (rho := rho) (rho' := rho') in H'.
      rewrite H'.
      trivial.
    - simpl in *.
      rewrite IHe1 with (rho := rho) (V := V).
      rewrite IHe2 with (rho := rho) (V := V).
      + trivial.
      + unfold incl in *.
        intros a Ha.
        apply H.
        apply append_right.
        trivial.
      + unfold incl in *.
        intros a Ha.
        apply H.
        apply append_left.
        trivial.
  Qed.

  Lemma incl_bexp :
    forall b rho rho' V,
      incl (getFreeVarsBExp b) V ->
      applyValBExp rho' b = applyValBExp (modify_val_on_set rho rho' V) b.
  Proof.
    intros b.
    induction b; intros.
    - simpl. trivial.
    - simpl. trivial.
    - simpl in *.
      assert (H' : In (bvar v) (bvar v :: nil)).
      simpl. left. trivial.
      apply H in H'.
      apply modify_in with (rho := rho) (rho' := rho') in H'.
      rewrite H'.
      trivial.
    - simpl in *.
      rewrite incl_exp with (rho := rho) (V := V).
      rewrite incl_exp with (rho := rho) (V := V) (e := e0).
      trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
  Qed.

  Lemma incl_stmt :
    forall s rho rho' V,
      incl (getFreeVarsStmt s) V ->
      applyValStmt rho' s = applyValStmt (modify_val_on_set rho rho' V) s.
  Proof.
    intros s.
    induction s; intros.
    - simpl in *.
      rewrite incl_exp with (rho := rho) (V := V); trivial.
    - simpl in *.
      assert (H' : In (svar v) (svar v :: nil)).
      simpl. left. trivial.
      apply H in H'.
      apply modify_in with (rho := rho) (rho' := rho') in H'.
      rewrite H'.
      trivial.
    - simpl in *.
      rewrite <- incl_bexp.
      rewrite <- IHs1.
      rewrite <- IHs2.
      trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H.
      apply incl_append_left in H; trivial.
    - simpl in *.
      rewrite <- incl_bexp.
      rewrite <- IHs.
      trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
    - simpl in *.
      trivial.
    - simpl in *.
      rewrite <- IHs1.
      rewrite <- IHs2.
      reflexivity.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
  Qed.

  Lemma incl_mapitem :
    forall mi rho rho' V,
      incl (getFreeVarsMapItem mi) V ->
      applyValMapItem rho' mi = applyValMapItem (modify_val_on_set rho rho' V) mi.
  Proof.
    induction mi; intros.
    - simpl in *.
      assert (H' : In (mivar v) (mivar v :: nil)).
      simpl. left. trivial.
      apply H in H'.
      apply modify_in with (rho := rho) (rho' := rho') in H'.
      rewrite H'.
      trivial.
    - simpl in *.
      rewrite <- incl_exp; trivial.
  Qed.

  Lemma incl_list :
    forall l rho rho' V,
      incl (getFreeVarsItems l) V ->
      applyValList rho' l = applyValList (modify_val_on_set rho rho' V) l.
  Proof.
    induction l; intros.
    - simpl in *. trivial.
    - simpl in *.
      rewrite <- incl_mapitem.
      rewrite <- IHl.
      trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
  Qed.


  Lemma incl_cfg :
    forall c rho rho' V,
      incl (getFreeVars (pattern c)) V ->
      applyVal rho' c = applyVal (modify_val_on_set rho rho' V) c.
  Proof.
    intros c. induction c; intros.
    - simpl in *.
      assert (H' : In (cvar v) (cvar v :: nil)).
      simpl. left. trivial.
      apply H in H'.
      apply modify_in with (rho := rho) (rho' := rho') in H'.
      rewrite H'.
      trivial.
    - simpl in *.
      rewrite <- incl_stmt.
      rewrite <- incl_list.
      trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
  Qed.      



  Lemma not_incl_exp:
    forall e rho rho' V,
      (forall x, In x (getFreeVarsExp e) -> ~ In x V) ->
      applyValExp rho e = applyValExp (modify_val_on_set rho rho' V) e.
  Proof.
    intros e. induction e; intros; simpl in *; trivial.
    - rewrite modify_not_in; trivial.
      apply H. left. trivial.
    - rewrite <- IHe1, <- IHe2; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
  Qed.

  Lemma not_incl_bexp:
    forall b rho rho' V,
      (forall x, In x (getFreeVarsBExp b) -> ~ In x V) ->
      applyValBExp rho b = applyValBExp (modify_val_on_set rho rho' V) b.
  Proof.
    intros b. induction b; intros; simpl in *; trivial.
    - rewrite modify_not_in; trivial.
      apply H. left. trivial.
    - rewrite <- not_incl_exp, <- not_incl_exp; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
  Qed.

  Lemma not_incl_stmt:
    forall s rho rho' V,
      (forall x, In x (getFreeVarsStmt s) -> ~ In x V) ->
      applyValStmt rho s = applyValStmt (modify_val_on_set rho rho' V) s.
  Proof.
    intros s. induction s; intros; simpl in *; trivial.
    - rewrite <- not_incl_exp; trivial.
    - rewrite modify_not_in; trivial.
      apply H. left. trivial.
    - rewrite <- not_incl_bexp.
      rewrite <- IHs1, <- IHs2; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left. apply append_right. trivial.
      intros x Hx. apply H. apply append_left. apply append_left. trivial.
    - rewrite <- not_incl_bexp.
      rewrite <- IHs; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
    - rewrite <- IHs1, <- IHs2; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
  Qed.

  
  Lemma not_incl_mapitem:
    forall mi rho rho' V,
      (forall x, In x (getFreeVarsMapItem mi) -> ~ In x V) ->
      applyValMapItem rho mi = applyValMapItem (modify_val_on_set rho rho' V) mi.
  Proof.
    induction mi; intros; simpl in *; trivial.
    - rewrite modify_not_in; trivial.
      apply H. left. trivial.
    - rewrite <- not_incl_exp. trivial.
      intros x Hx. apply H. trivial.
  Qed.

  Lemma not_incl_list:
    forall l rho rho' V,
      (forall x, In x (getFreeVarsItems l) -> ~ In x V) ->
      applyValList rho l = applyValList (modify_val_on_set rho rho' V) l.
  Proof.
    intros l. induction l; intros; simpl in *; trivial.
    - rewrite <- not_incl_mapitem.
      rewrite <- IHl; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
  Qed.


  Lemma not_incl_cfg:
    forall c rho rho' V,
      (forall x, In x (getFreeVarsCfg c) -> ~ In x V) ->
      applyVal rho c = applyVal (modify_val_on_set rho rho' V) c.
  Proof.
    intros c. induction c; intros; simpl in *; trivial.
    - rewrite modify_not_in; trivial.
      apply H. left. trivial.
    - rewrite <- not_incl_stmt; trivial.
      rewrite <- not_incl_list; trivial.
      intros x Hx. apply H. apply append_right; trivial.
      intros x Hx. apply H. apply append_left; trivial.
  Qed.

  
      
          
  Lemma modify_Sat_right :
    forall phi V gamma rho rho',
      incl (getFreeVars phi) V ->
      (SatML gamma rho' phi <->
      SatML gamma (modify_val_on_set rho rho' V) phi).
  Proof.
    induction phi; intros.
    - simpl. split; intros; trivial.
    - simpl in *.
      split.
      intros H';
      rewrite <- incl_cfg with (rho := rho) (V := V); trivial.
      rewrite <- incl_cfg with (rho := rho) (V := V); trivial.
    - split.
      + intros H1.
        simpl in *.
        destruct H1 as (H1 & H2).
        split.
        apply IHphi1; trivial.
        apply incl_append_left in H; trivial.
        apply IHphi2; trivial.
        apply incl_append_right in H; trivial.
      + intros H1.
        simpl in *.
        destruct H1 as (H1 & H2).
        split.
        rewrite IHphi1 with (rho := rho) (V := V); trivial.
        apply incl_append_left in H; trivial.
        apply IHphi2 with (rho := rho) (V := V); trivial.
        apply incl_append_right in H; trivial.
    - split.
      + intros H1.
        simpl in *.
        intros H2.
        rewrite <- IHphi1 in H2.
        apply IHphi2.
        apply incl_append_right in H; trivial.
        apply H1; trivial.
        apply incl_append_left in H; trivial.
      + simpl in *. intros.
        rewrite IHphi2 with (V := V).
        rewrite IHphi1 with (rho := rho) (V := V) in H1 .
        apply H0; trivial.
        apply incl_append_left in H; trivial.
        apply incl_append_right in H; trivial.
    - simpl in *.
      split; intros.
      + destruct H0 as (mu & H0 & H1).
        exists (modify_val_on_set (modify_val_on_set rho rho' V) mu (append_set V l)).
        split.
        * intros x H2.
          assert (H3 : In x V \/ ~ In x V).
          apply classic.
          destruct H3 as [H3 | H3].
          assert (H4: In x (append_set V l)).
          apply append_left; trivial.
          apply modify_in with (rho := (modify_val_on_set rho rho' V)) (rho' := mu) in H4.
          rewrite H4.
          rewrite modify_in; trivial.
          apply H0; trivial.
          assert (H4: ~ In x (append_set V l)).
          unfold not.
          intros H5.
          apply in_append_iff in H5.
          destruct H5 as [H5 | H5]; contradiction.
          rewrite modify_not_in; trivial.
        * apply IHphi; trivial.
          unfold incl in *.
          intros a Ha.
          assert (H2: In a l \/ ~ In a l).
          apply classic.
          destruct H2 as [H2 | H2].
          rewrite in_append_iff.
          right. trivial.
          assert (H3: In a (minus_set (getFreeVars phi) l)).
          apply minus_set_helper; trivial.
          apply H in H3.
          rewrite in_append_iff.
          left. trivial.
      + destruct H0 as (mu & H0 & H1).
        exists (modify_val_on_set rho' mu (append_set V l)).
        {
          split.
          - intros x Hx.
            assert (H2 : In x V \/ ~ In x V).
            apply classic.
            destruct H2 as [H2 | H2].
            assert (H3: In x (append_set V l)).
            apply append_left; trivial.
            apply modify_in with (rho := rho') (rho' := mu) in H3.
            rewrite H3.
            apply H0 in Hx.
            rewrite Hx.
            apply modify_in; trivial.
            assert (H4: ~ In x (append_set V l)).
            unfold not.
            intros H5.
            apply in_append_iff in H5.
            destruct H5 as [H5 | H5]; contradiction.
            rewrite modify_not_in; trivial.
          - apply IHphi; trivial.
            unfold incl in *.
            intros y Hy.
            assert (H2: In y (minus_set (getFreeVars phi) l) \/
                        ~ In y (minus_set (getFreeVars phi) l)).
            apply classic.
            destruct H2 as [H2 | H2]; trivial.
            + apply H in H2.
              apply append_left; trivial.
            + assert (H3 : In y l \/ ~ In y l).
              apply classic.
              destruct H3 as [H3 | H3].
              * apply append_right. trivial.
              * contradict H2.
                apply minus_set_helper; trivial.
        }
    - simpl in *.
      split; intros H'; destruct H' as (gamma' & H'); exists gamma'.
      + rewrite <- IHphi with (V := V); trivial.
      + rewrite IHphi with (V := V) (rho := rho); trivial.
    - simpl in *.
      rewrite incl_exp with (rho := rho) (V := V).
      rewrite incl_exp with (rho := rho) (V := V) (e := e0).
      split; intros H'; trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.
  Qed.


  
  Lemma modify_Sat1 :
    forall phi V gamma rho rho',
      SatML gamma rho' phi ->
      incl (getFreeVars phi) V ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Proof.
    intros.
    apply modify_Sat_right; trivial.
  Qed.
  

 
  Lemma modify_Sat_left :
    forall phi gamma rho rho' V,
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      (SatML gamma rho phi <->
       SatML gamma (modify_val_on_set rho rho' V) phi).
  Proof.
    induction phi.
    - intros. simpl.
      split; trivial.
    - split; intros.
      + simpl in *.
        rewrite <- H0.
        rewrite <- not_incl_cfg; trivial.
      + simpl in *.
        rewrite <- H0.
        rewrite <- not_incl_cfg; trivial.
    - split; intros; simpl in *; destruct H0 as (H0 & H1); split.
      + rewrite <- IHphi1; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_left; trivial.
        apply H; trivial.
      + rewrite <- IHphi2; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_right; trivial.
        apply H; trivial.
      + rewrite IHphi1 with (rho' := rho') (V := V); trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_left; trivial.
        apply H; trivial.
      + rewrite IHphi2 with (rho' := rho') (V := V); trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_right; trivial.
        apply H; trivial.
    - split; intros; simpl in *; intros.
      + rewrite <- IHphi2.
        apply H0.
        rewrite <- IHphi1 in H1; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_left; trivial.
        apply H; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_right; trivial.
        apply H; trivial.
      + rewrite IHphi2 with (rho' := rho') (V := V).
        apply H0.
        rewrite <- IHphi1; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_left; trivial.
        apply H; trivial.
        intros x Hx.
        assert (H2 : In x (append_set (getFreeVars phi1) (getFreeVars phi2))).
        apply append_right; trivial.
        apply H; trivial.
    - split; simpl in *; intros H0; destruct H0 as (mu & H0 & H1).
      + exists (modify_val_on_set mu (modify_val_on_set rho rho' V) (minus_set V l)).
        split.
        * intros x Hx.
          assert (H2: In x V \/ ~ In x V).
          apply classic.
          destruct H2 as [H2 | H2].
          assert (H': In x (minus_set V l)).
          apply minus_set_helper; trivial.
          rewrite modify_in; trivial.
          assert (H': ~ In x (minus_set V l)).
          unfold not.
          intros HH.
          apply H2.
          apply minus_set_helper' in HH.
          destruct HH as (HH & HH').
          contradiction.
          rewrite modify_not_in; trivial.
          rewrite modify_not_in; trivial.
          apply H0; trivial.          
        * rewrite <- IHphi; trivial.
          intros x Hx.
          unfold not.
          intros HH.
          assert (H2: In x V /\ ~ In x l).
          apply minus_set_helper' in HH.
          destruct HH as (HH & HH').
          split; trivial.
          destruct H2 as (H2 & H3).
          assert (~ In x V).
          apply H.
          apply minus_set_helper; trivial.
          contradiction.
      + exists (modify_val_on_set mu rho (minus_set V l)).
        split.
        * intros x Hx.
          assert (H2: In x V \/ ~ In x V).
          apply classic.
          destruct H2 as [H2 | H2].
          assert (H': In x (minus_set V l)).
          apply minus_set_helper; trivial.
          rewrite modify_in; trivial.
          assert (H': ~ In x (minus_set V l)).
          unfold not.
          intros HH.
          apply H2.
          apply minus_set_helper' in HH.
          destruct HH as (HH & HH').
          contradiction.
          rewrite modify_not_in; trivial.
          apply H0 in Hx.
          rewrite Hx.
          apply modify_not_in; trivial.
        * rewrite <- IHphi; trivial.
          intros x Hx.
          unfold not.
          intros KH.
          apply minus_set_helper' in KH.
          destruct KH.
          assert (KK : In x (minus_set (getFreeVars phi) l)).
          apply minus_set_helper; trivial.
          apply H in KK.
          contradiction.
    - split; intros; simpl in *;
        destruct H0 as (gamma' & H0);
        exists gamma'.
      rewrite <- IHphi; trivial.
      rewrite IHphi with (rho' := rho') (V := V); trivial.
    - split; intros.
      + simpl in *.
        rewrite <- not_incl_exp.
        rewrite <- not_incl_exp; trivial.
        intros x Hx.
        apply H.
        apply append_right. trivial.
        intros x Hx.
        apply H.
        apply append_left. trivial.
      + simpl in *.
        rewrite not_incl_exp with (rho' := rho') (V := V).
        rewrite not_incl_exp with (rho' := rho') (V := V) (e := e0); trivial.
        intros x Hx.
        apply H.
        apply append_right. trivial.
        intros x Hx.
        apply H.
        apply append_left. trivial.
  Qed.


  Lemma modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Proof.
    intros.
    apply modify_Sat_left; trivial.
  Qed.
         
End Lang.
