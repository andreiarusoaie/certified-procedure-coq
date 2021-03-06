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

  Inductive Id : Type :=
  | a : Id
  | b : Id
  | c : Id
  | n : Id
  | i : Id
  | x : Id
  | y : Id
  | s : Id.


  Inductive VarID : Type :=
  | X : VarID
  | Y : VarID
  | XFRESH : VarID
  | YFRESH : VarID.
  Inductive VarExp : Type :=
  | N : VarExp
  | I : VarExp
  | S : VarExp
  | S' : VarExp
  | NFRESH : VarExp
  | IFRESH : VarExp
  | SFRESH : VarExp
  | S'FRESH : VarExp.
  Inductive VarBExp : Type :=
  | B : VarBExp
  | BFRESH : VarBExp.
  Inductive VarStmt : Type :=
  | St : VarStmt
  | S1 : VarStmt
  | S2 : VarStmt
  | StFRESH : VarStmt
  | S1FRESH : VarStmt
  | S2FRESH : VarStmt.
  Inductive VarMI : Type :=
  | M : VarMI
  | MFRESH : VarMI.
  Inductive VarMIList : Type :=
  | Rest : VarMIList
  | RestFRESH : VarMIList.
  Inductive VarCfg : Type :=
  | C : VarCfg
  | CFRESH : VarCfg.
  
  
  Inductive ID : Type :=
  | idc : Id -> ID
  | ivar : VarID -> ID .

  Inductive Exp : Type := 
  | id : ID -> Exp
  | val : Z -> Exp
  | var_exp : VarExp -> Exp
  | plus : Exp -> Exp -> Exp.
  

  Notation "$ A" := (id A) (at level 100).
  Notation "! A" := (var_exp A) (at level 100).
  Eval compute in ($ (idc a)).
  Eval compute in (val 2).
  Eval compute in (! N).
  Eval compute in (plus (! N) ($ (idc a))).  


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
  
  Eval compute in  ((idc i) <- (val 0)).
  Eval compute in (var_stmt St).
  Eval compute in (ifelse (leq ($ (idc i)) ($ (idc n)))  (assign (idc s) (plus ($ (idc s)) ($ (idc i)))) skip) .
  Eval compute in ((idc i) <- (val 0) ; ((idc s) <- (val 0))).
  Eval compute in ((idc i) <- (val 0) ; ((idc s) <- (val 0)) ;
                   (while (leq ($ (idc i)) ($ (idc n)))
                          (((idc s) <- (plus ($ (idc s)) ($ (idc i)))) ;
                           ((idc i) <- (plus ($ (idc i)) (val 1))))
                   )).
  

  (* configuration *)
  Inductive MapItem := 
  | var_mi : VarMI -> MapItem
  | item : ID -> Exp -> MapItem.

  Inductive MIList :=
  | Nil : MIList
  | Cons : MapItem -> MIList -> MIList
  | list_var : VarMIList -> MIList.

  Notation "A ;; B" := (Cons A B) (at level 100).
  
  Inductive Cfg := 
  | var_cfg : VarCfg -> Cfg
  | cfg : Stmt -> MIList -> Cfg .

(*  Notation "A |-> B" := (item_z A B) (at level 100). *)
  Notation "A |-> B" := (item A B) (at level 100).
  Eval compute in (cfg 

                     ((idc i) <- (val 0) ; ((idc s) <- (val 0)) ;
                   (while (leq ($ (idc i)) ($ (idc n)))
                          (((idc s) <- (plus ($ (idc s)) ($ (idc i)))) ;
                           ((idc i) <- (plus ($ (idc i)) (val 1))))
                   ))
                     
                   (((idc n) |-> (! N)) ;; Nil)).

  
  (* model and state: equiv classes? *)
  Inductive _exp : Type :=
    | _int : Z -> _exp
    | _plus : _exp -> _exp -> _exp
    | _id : Id -> _exp. 

  Inductive _bexp : Type :=
  | _bool : bool -> _bexp
  | _leq : _exp -> _exp -> _bexp.
                             
  
  Inductive _stmt : Type :=
  | _skip : _stmt
  | _assign : Id -> _exp -> _stmt
  | _ifelse : _bexp -> _stmt -> _stmt -> _stmt 
  | _while : _bexp -> _stmt -> _stmt 
  | _seq : _stmt -> _stmt -> _stmt.
   
  Definition _map_item := (Id * _exp)%type.
  Definition State : Type := (_stmt * list _map_item)%type.
  Inductive Model' : Type := 
    | to_m_id : Id -> Model'
    | to_m_exp : _exp -> Model'
    | to_m_bexp : _bexp -> Model'
    | to_m_stmt : _stmt -> Model'
    | to_m_map_item : _map_item -> Model'
    | to_m_list : list _map_item -> Model'
    | to_m_state : State -> Model'.
  Definition Model := Model'.
  

  Inductive Var' : Type :=
  | idvar : VarID -> Var'
  | evar : VarExp -> Var'
  | bvar : VarBExp -> Var'
  | svar : VarStmt -> Var'
  | mivar : VarMI -> Var'
  | lvar : VarMIList -> Var'
  | cvar : VarCfg -> Var'.
  Definition Var := Var'.

  (* Valuation *)
  Definition Valuation := Var -> Model .

  (* var equality *)
  Definition var_eq (X Y : Var) : bool := 
    match X, Y with
      | idvar v1, idvar v2 => match v1, v2 with
                              | X, X => true
                              | Y, Y => true
                              | XFRESH, XFRESH => true
                              | YFRESH, YFRESH => true
                              | _, _ => false
                              end
      | evar e1, evar e2 => match e1, e2 with
                              | N, N => true
                              | I, I => true
                              | S, S => true
                              | S', S' => true
                              | NFRESH, NFRESH => true
                              | IFRESH, IFRESH => true
                              | SFRESH, SFRESH => true
                              | S'FRESH, S'FRESH => true
                              | _, _ => false
                            end
      | bvar b1, bvar b2 => match b1, b2 with
                              | B, B => true
                              | BFRESH, BFRESH => true
                              | _, _ => false
                            end
      | svar s1, svar s2 => match s1, s2 with
                              | St, St => true
                              | S1, S1 => true
                              | S2, S2 => true
                              | StFRESH, StFRESH => true
                              | S1FRESH, S1FRESH => true
                              | S2FRESH, S2FRESH => true
                              | _, _ => false
                            end
      | mivar m1, mivar m2 => match m1, m2 with
                              | M, M => true
                              | MFRESH, MFRESH => true
                              | _, _ => false
                            end
      | lvar l1, lvar l2 => match l1, l2 with
                              | Rest, Rest => true
                              | RestFRESH, RestFRESH => true
                              | _, _ => false
                            end
      | cvar c1, cvar c2 => match c1, c2 with
                              | C, C => true
                              | CFRESH, CFRESH => true
                              | _, _ => false
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

  Definition SUM := pattern
                    (cfg 

                     ((idc i) <- (val 0) ; ((idc s) <- (val 0)) ;
                   (while (leq ($ (idc i)) ($ (idc n)))
                          (((idc s) <- (plus ($ (idc s)) ($ (idc i)))) ;
                           ((idc i) <- (plus ($ (idc i)) (val 1))))
                   ))
                     
                   (((idc n) |-> (! N)) ;; Nil)).
  Eval compute in SUM.

  Eval compute in AndML T SUM.

  Eval compute in AndML SUM (! N >>= (val 0)).




  
  (* eq_dec needed to deal (remove, search) with goals in G *)
  Fixpoint Id_eq_dec (id id' : Id) : bool :=
    match id, id' with
      | a, a => true
      | b, b => true
      | c, c => true
      | n, n => true
      | i, i => true
      | x, x => true
      | y, y => true
      | s, s => true
      | _, _ => false
    end.

  Lemma Id_eq_dec_true :
    forall id id', Id_eq_dec id id' = true -> id = id'.
  Proof.
    intros i i' H.
    case_eq i; case_eq i'; intros; subst; trivial; simpl in H; try inversion H.
  Qed.
  
  Lemma Id_eq_dec_false :
    forall id id', Id_eq_dec id id' = false -> id <> id'.
  Proof.
    intros i0 i' H.
    unfold not. intros H'. subst.
    case_eq i'; intros; subst; trivial; simpl in H; try inversion H.
  Qed.

  Lemma Id_eq_dec_refl :
    forall id, Id_eq_dec id id = true.
  Proof.
    intros id.
    induction id; intros; simpl; trivial.
  Qed.



  
  Fixpoint ID_eq_dec (id id' : ID) : bool :=
    match id, id' with
      | idc i0, idc i' => Id_eq_dec i0 i'
      | ivar v, ivar v' => var_eq (idvar v) (idvar v')
      | _, _ => false
    end.
  
  Lemma ID_eq_dec_refl :
    forall id, ID_eq_dec id id = true.
  Proof.
    intros id.
    induction id; intros; simpl.
    - apply Id_eq_dec_refl.
    - case_eq v; intros; reflexivity.
  Qed.

  Lemma ID_eq_dec_true :
    forall id id', ID_eq_dec id id' = true -> id = id'.
  Proof.
    induction id0, id'; intros H; simpl in H; try inversion H.
    - apply Id_eq_dec_true in H. subst. reflexivity.
    - case_eq v; case_eq v0; intros H0 H2; subst; trivial; try inversion H.
  Qed.
  
  Lemma ID_eq_dec_false :
    forall id id', ID_eq_dec id id' = false -> id <> id'.
  Proof.
    intros id0 id' H. unfold not. intros H'. subst.
    rewrite ID_eq_dec_refl in H. inversion H.
  Qed.




    
  Fixpoint Exp_eq_dec (e e' : Exp) : bool :=
    match e, e' with
      | id i0, id i' => ID_eq_dec i0 i'
      | val z1, val z2 => if Z.eq_dec z1 z2 then true else false
      | var_exp v, var_exp v' => var_eq (evar v) (evar v')
      | plus e1 e2, plus e1' e2' => andb (Exp_eq_dec e1 e1') (Exp_eq_dec e2 e2')
      | _, _ => false
    end.

  Lemma Exp_eq_dec_refl :
    forall e, Exp_eq_dec e e = true.
  Proof.
    intros e; induction e; simpl in *.
    - apply ID_eq_dec_refl.
    - case_eq (Z.eq_dec z z); intros H' H; try contradiction H'; reflexivity.
    - case_eq v; intros; reflexivity.
    - rewrite IHe1, IHe2. simpl. reflexivity.
  Qed.
  
  Lemma Exp_eq_dec_true :
    forall e1 e2, Exp_eq_dec e1 e2 = true -> e1 = e2.
  Proof.
    induction e1, e2; intros; subst; simpl in H; try inversion H.
    - apply ID_eq_dec_true in H. subst. reflexivity.
    - case_eq (Z.eq_dec z z0); intros H0 H2; subst; try reflexivity.
      rewrite H2 in H. inversion H.
    - case_eq v; case_eq v0; intros H' H''; subst; try reflexivity; try inversion H.
    - case_eq (Exp_eq_dec e1_1 e2_1); intros H0.
      apply IHe1_1 in H0. subst.
      case_eq (Exp_eq_dec e1_2 e2_2). intros H2.
      apply IHe1_2 in H2. subst. reflexivity.
      intros H2. rewrite H2 in *. simpl in H.
      case_eq (Exp_eq_dec e2_1 e2_1). intros H3.
      rewrite H3 in *. simpl in H. inversion H.
      intros H3. rewrite H3 in *. simpl in H. inversion H.
      rewrite H0 in H. simpl in H. inversion H.
  Qed.
  
  Lemma Exp_eq_dec_false :
    forall e1 e2, Exp_eq_dec e1 e2 = false -> e1 <> e2.
  Proof.
    intros e1 e2 H. unfold not. intros H'. subst.
    rewrite Exp_eq_dec_refl in H. inversion H.
  Qed.




  
  
  Fixpoint BExp_eq_dec (b b' : BExp) : bool :=
    match b, b' with
      | TT, TT => true
      | FF, FF => true
      | var_bexp v, var_bexp v' => var_eq (bvar v) (bvar v')
      | leq e1 e2, leq e1' e2' => andb (Exp_eq_dec e1 e1') (Exp_eq_dec e2 e2')
      | _, _ => false
    end.

  Lemma BExp_eq_dec_refl :
    forall b, BExp_eq_dec b b = true.
  Proof.
    intros b. induction b; simpl; trivial.
    - case_eq v; intros; reflexivity.
    - rewrite 2 Exp_eq_dec_refl.
      simpl. reflexivity.
  Qed.

  Lemma BExp_eq_dec_true :
    forall b b',
      BExp_eq_dec b b' = true -> b = b'.
  Proof.
    intros b b' H.
    induction b, b'; simpl in H; try inversion H; trivial.
    - case_eq v; case_eq v0; intros H2 H3;
      subst; try reflexivity; try inversion H.
    - clear H1.
      case_eq (Exp_eq_dec e e1); intros H1.
      case_eq (Exp_eq_dec e0 e2); intros H2.
      apply Exp_eq_dec_true in H1.
      apply Exp_eq_dec_true in H2.
      subst. reflexivity.
      rewrite H1, H2 in H. simpl in H. inversion H.
      rewrite H1 in H. simpl in H. inversion H.
  Qed.

  Lemma BExp_eq_dec_false :
    forall b b',
      BExp_eq_dec b b' = false -> b <> b'.
  Proof.
    intros b b' H. unfold not. intros H'. subst.
    rewrite BExp_eq_dec_refl in H. inversion H.
  Qed.


  
  Fixpoint Stmt_eq_dec (st st' : Stmt) : bool :=
    match st, st' with
      | assign i0 e, assign i' e' => andb (ID_eq_dec i0 i') (Exp_eq_dec e e')
      | var_stmt v, var_stmt v' => var_eq (svar v) (svar v')
      | ifelse b0 s1 s2, ifelse b' s1' s2' => andb (BExp_eq_dec b0 b') (andb (Stmt_eq_dec s1 s1') (Stmt_eq_dec s2 s2'))
      | while b0 s0, while b' s' => andb (BExp_eq_dec b0 b') (Stmt_eq_dec s0 s')
      | skip, skip => true
      | seq s1 s2, seq s1' s2' => andb (Stmt_eq_dec s1 s1') (Stmt_eq_dec s2 s2')
      | _, _ => false
    end.

  Lemma Stmt_eq_dec_refl :
    forall s, Stmt_eq_dec s s = true.
  Proof.
    intros s. induction s; intros; simpl.
    - rewrite ID_eq_dec_refl. rewrite Exp_eq_dec_refl. simpl. reflexivity.
    - case_eq v; intros v'; subst; reflexivity.
    - rewrite BExp_eq_dec_refl.
      rewrite IHs1, IHs2.
      simpl. reflexivity.
    - rewrite BExp_eq_dec_refl.
      rewrite IHs.
      simpl. reflexivity.
    - reflexivity.
    - rewrite IHs1, IHs2. simpl. reflexivity.
  Qed.
  
  Lemma Stmt_eq_dec_true :
    forall s1 s2, Stmt_eq_dec s1 s2 = true -> s1 = s2.
  Proof.
    intros ss.
    induction ss; intros ss'; induction ss';
    simpl in *; intros; try inversion H.
    - case_eq (ID_eq_dec i0 i1); case_eq (Exp_eq_dec e e0); intros.
      clear H1.
      apply Exp_eq_dec_true in H0.
      apply ID_eq_dec_true in H2.
      subst. reflexivity.
      rewrite H0 in *. rewrite H2 in *.
      simpl in H1. inversion H1.
      rewrite H0 in *. rewrite H2 in *.
      simpl in H1. inversion H1.
      rewrite H0 in *. rewrite H2 in *.
      simpl in H1. inversion H1.
    - case_eq v; intros Hv;
      case_eq v0; intros Hv0;
      subst; try reflexivity; try inversion H.
    - clear H1.
      case_eq (BExp_eq_dec b0 b1); intros Hb.
      case_eq (Stmt_eq_dec ss1 ss'1); intros Hs1.
      case_eq (Stmt_eq_dec ss2 ss'2); intros Hs2.
      + apply BExp_eq_dec_true in Hb.
        apply IHss1 in Hs1.
        apply IHss2 in Hs2.
        subst. reflexivity.
      + rewrite Hb, Hs1, Hs2 in H. simpl in H. inversion H.
      + rewrite Hb, Hs1 in H. simpl in H. inversion H.
      + rewrite Hb in H. simpl in H. inversion H.
    - case_eq (BExp_eq_dec b0 b1); intros Hb.
      case_eq (Stmt_eq_dec ss ss'); intros Hs.
      apply BExp_eq_dec_true in Hb.
      apply IHss in Hs.
      subst. reflexivity.
      rewrite Hb, Hs in H. simpl in H. inversion H.
      rewrite Hb in H. simpl in H. inversion H.
    - reflexivity.
    - case_eq (Stmt_eq_dec ss1 ss'1); intros Hs1.
      case_eq (Stmt_eq_dec ss2 ss'2); intros Hs2.
      apply IHss1 in Hs1.
      apply IHss2 in Hs2.
      subst. reflexivity.
      rewrite Hs1, Hs2 in H.
      simpl in H. inversion H.
      rewrite Hs1 in H.
      simpl in H. inversion H.
  Qed.

  Lemma Stmt_eq_dec_false :
    forall s1 s2, Stmt_eq_dec s1 s2 = false -> s1 <> s2.
  Proof.
    intros s1 s2 H. unfold not. intros H'. subst.
    rewrite Stmt_eq_dec_refl in H. inversion H.
  Qed.
      
      
  

  
  Fixpoint MapItem_eq_dec (mi mi' : MapItem) : bool :=
    match mi, mi' with
      | var_mi v, var_mi v' => var_eq (mivar v) (mivar v')
      | item i0 e0, item i' e' => andb (ID_eq_dec i0 i') (Exp_eq_dec e0 e')
      | _, _ => false
    end.

  Lemma MapItem_eq_dec_refl :
    forall mi, MapItem_eq_dec mi mi = true.
  Proof.
    induction mi; simpl.
    - case_eq v; intros; subst; try reflexivity; try inversion H.
    - rewrite ID_eq_dec_refl, Exp_eq_dec_refl.
      simpl. reflexivity.
  Qed.

  Lemma MapItem_eq_dec_true:
    forall mi mi',
      MapItem_eq_dec mi mi' = true -> mi = mi'.
  Proof.
    intros mi. induction mi; induction mi'; intros; simpl in *; try inversion H.
    - case_eq v; intros; case_eq v0; intros; subst; try reflexivity; try inversion H.
    - clear H1.
      case_eq (ID_eq_dec i0 i1); intros H1.
      case_eq (Exp_eq_dec e e0); intros H2.
      + apply ID_eq_dec_true in H1.
        apply Exp_eq_dec_true in H2.
        subst. reflexivity.
      + rewrite H1, H2 in H. simpl in H. inversion H.
      + rewrite H1 in H. simpl in H. inversion H.
  Qed.

  Lemma MapItem_eq_dec_false:
    forall mi mi',
      MapItem_eq_dec mi mi' = false -> mi <> mi'.
  Proof.
    intros mi mi' H.
    unfold not. intros H'. subst.
    rewrite MapItem_eq_dec_refl in H. inversion H.
  Qed.
  
      
  
  
  Fixpoint MIList_eq_dec (mil mil' : MIList) : bool :=
    match mil, mil' with
      | Nil, Nil => true
      | Cons mi ml, Cons mi' ml' => andb (MapItem_eq_dec mi mi') (MIList_eq_dec ml ml')
      | list_var v, list_var v' => var_eq (lvar v) (lvar v')
      | _, _ => false
    end.

  Lemma MIList_eq_dec_refl :
    forall ml, MIList_eq_dec ml ml = true.
  Proof.
    induction ml; simpl.
    - reflexivity.
    - rewrite MapItem_eq_dec_refl, IHml.
      simpl. reflexivity.
    - case_eq v; intros; reflexivity.
  Qed.


  Lemma MIList_eq_dec_true:
    forall ml ml', MIList_eq_dec ml ml' = true -> ml = ml'.
  Proof.
    induction ml, ml'; intros; trivial; simpl in H; try inversion H.
    - clear H1.
      case_eq (MapItem_eq_dec m m0); intros H1.
      case_eq (MIList_eq_dec ml ml'); intros H2.
      + apply MapItem_eq_dec_true in H1.
        apply IHml in H2.
        subst. reflexivity.
      + rewrite H1, H2 in H. simpl in H. inversion H.
      + rewrite H1 in H. simpl in H. inversion H.
    - clear H1.
      case_eq v; case_eq v0; intros Hv Hv0; subst; try reflexivity; try inversion H.
  Qed.

  Lemma MIList_eq_dec_false:
    forall ml ml', MIList_eq_dec ml ml' = false -> ml <> ml'.
  Proof.
    intros ml ml' H. unfold not. intros. subst.
    rewrite MIList_eq_dec_refl in H. inversion H.
  Qed.
    



  
  Fixpoint Cfg_eq_dec (cfg cfg' : Cfg) : bool :=
    match cfg, cfg' with
      | var_cfg v, var_cfg v' => var_eq (cvar v) (cvar v')
      | cfg S0 MI, cfg S0' MI' => andb (Stmt_eq_dec S0 S0') (MIList_eq_dec MI MI')
      | _, _ => false
    end.

  Lemma Cfg_eq_dec_refl :
    forall cfg, Cfg_eq_dec cfg cfg = true.
  Proof.
    intros cf. induction cf; simpl.
    - case_eq v; intros; subst; trivial; try inversion H.
    - rewrite Stmt_eq_dec_refl, MIList_eq_dec_refl.
      simpl. reflexivity.
  Qed.

  Lemma Cfg_eq_dec_true :
    forall c c', Cfg_eq_dec c c' = true -> c = c'.
  Proof.
    intros c. induction c; induction c'; intros; simpl; try inversion H.
    - case_eq v; case_eq v0; intros; subst; try reflexivity; try inversion H.
    - case_eq (Stmt_eq_dec s0 s1); intros H2.
      case_eq (MIList_eq_dec m m0); intros H3.
      apply Stmt_eq_dec_true in H2.
      apply MIList_eq_dec_true in H3.
      subst. reflexivity.
      rewrite H2, H3 in H1. simpl in H1. inversion H1.
      rewrite H2 in H1. simpl in H1. inversion H1.
  Qed.

  Lemma Cfg_eq_dec_false :
    forall c c', Cfg_eq_dec c c' = false -> c <> c'.
  Proof.
    intros c c' H. unfold not. intros H'. subst.
    rewrite Cfg_eq_dec_refl in H. inversion H.
  Qed.
  

  
  Fixpoint var_list_eq_dec (l1 l2 : list Var) : bool :=
    match l1, l2 with
      | nil, nil => true
      | cons v vs, cons v' vs' => andb (var_eq v v') (var_list_eq_dec vs vs')
      | _, _ => false
    end.

  Lemma var_list_eq_dec_refl :
    forall x, var_list_eq_dec x x = true.
  Proof.
    intros x. induction x; simpl; trivial.
    rewrite var_eq_refl, IHx.
    simpl. reflexivity.
  Qed.

  Lemma var_list_eq_dec_true:
    forall x y, var_list_eq_dec x y = true -> x = y.
  Proof.
    intros x.
    induction x; intros y; induction y; simpl; intros H; try inversion H; trivial.
    clear H1.
    case_eq (var_eq a0 a1); intros Hx.
    case_eq (var_list_eq_dec x0 y0); intros Hy.
    - apply var_eq_true in Hx.
      apply IHx in Hy. subst.
      reflexivity.
    - rewrite Hx, Hy in H. simpl in H. inversion H.
    - rewrite Hx in H. simpl in H. inversion H.
  Qed.

  Lemma var_list_eq_dec_false:
    forall x y, var_list_eq_dec x y = false -> x <> y.
  Proof.
    intros x y H. unfold not. intros H'. subst.
    rewrite var_list_eq_dec_refl in H. inversion H.
  Qed.
  
  
  
  Fixpoint MLFormula_eq_dec (phi phi' : MLFormula) : bool :=
    match phi, phi' with
      | T, T => true
      | pattern pi, pattern pi' => Cfg_eq_dec pi pi'
      | AndML p0 p0', AndML p1 p1' => andb (MLFormula_eq_dec p0 p1) (MLFormula_eq_dec p0' p1')
      | ImpliesML p0 p0', ImpliesML p1 p1' => andb (MLFormula_eq_dec p0 p1) (MLFormula_eq_dec p0' p1')
      | ExistsML l p, ExistsML l' p' => andb (var_list_eq_dec l l') (MLFormula_eq_dec p p')
      | encoding p, encoding p' => MLFormula_eq_dec p p'
      | gteML e1 e2, gteML e3 e4 => andb (Exp_eq_dec e1 e3) (Exp_eq_dec e2 e4)
      | _, _ => false
    end.

  Lemma MLFormula_eq_dec_refl :
    forall phi, MLFormula_eq_dec phi phi = true.
  Proof.
    induction phi; simpl; trivial.
    - apply Cfg_eq_dec_refl; trivial.
    - rewrite IHphi1, IHphi2. simpl. reflexivity.
    - rewrite IHphi1, IHphi2. simpl. reflexivity.
    - rewrite var_list_eq_dec_refl, IHphi. simpl. reflexivity.
    - rewrite 2 Exp_eq_dec_refl. simpl. reflexivity.
  Qed.

  Lemma MLFormula_eq_dec_true:
    forall phi phi', MLFormula_eq_dec phi phi' = true -> phi = phi'.
  Proof.
    induction phi; induction phi'; intros; simpl in *; try inversion H; try reflexivity.
    - apply Cfg_eq_dec_true in H. subst. reflexivity.
    - case_eq (MLFormula_eq_dec phi1 phi'1); intros H2.
      case_eq (MLFormula_eq_dec phi2 phi'2); intros H3.
      apply IHphi1 in H2.
      apply IHphi2 in H3.
      subst. reflexivity.
      rewrite H2, H3 in H. simpl in H. inversion H.
      rewrite H2 in H. simpl in H. inversion H.
    - case_eq (MLFormula_eq_dec phi1 phi'1); intros H2.
      case_eq (MLFormula_eq_dec phi2 phi'2); intros H3.
      apply IHphi1 in H2.
      apply IHphi2 in H3.
      subst. reflexivity.
      rewrite H2, H3 in H. simpl in H. inversion H.
      rewrite H2 in H. simpl in H. inversion H.
    - case_eq (var_list_eq_dec l l0); intros H2.
      case_eq (MLFormula_eq_dec phi phi'); intros H3.
      apply var_list_eq_dec_true in H2.
      apply IHphi in H3. subst. reflexivity.
      rewrite H2, H3 in H. simpl in H. inversion H.
      rewrite H2 in H. simpl in H. inversion H.
    - apply IHphi in H. subst. reflexivity.
    - case_eq (Exp_eq_dec e e1); intros H2.
      case_eq (Exp_eq_dec e0 e2); intros H3.
      apply Exp_eq_dec_true in H2.
      apply Exp_eq_dec_true in H3.
      subst. reflexivity.
      rewrite H2, H3 in H. simpl in H. inversion H.
      rewrite H2 in H. simpl in H. inversion H.
  Qed.

  Lemma MLFormula_eq_dec_false :
    forall phi phi', MLFormula_eq_dec phi phi' = false -> phi <> phi'.
  Proof.
    intros phi phi' H. unfold not. intros H'. subst.
    rewrite MLFormula_eq_dec_refl in H. inversion H.
  Qed.
    
                                                              
  (* End eq_dec *)

  
  
  (* apply valuations *)
  Fixpoint applyValID (rho : Valuation) (i : ID) : option Id :=
    match i with
      | idc j => Some j
      | ivar v => match (rho (idvar v)) with
                       | to_m_id e => Some e
                       | _ => None
                     end
    end.

  
  Fixpoint applyValExp (rho : Valuation) (e : Exp) : option _exp :=
    match e with
      | id j => match (applyValID rho j) with
                  | Some id' => Some (_id id')
                  | _ => None
                end
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
      | assign x' e' => match (applyValID rho x'), (applyValExp rho e') with
                          | Some x'', Some e'' => Some (_assign x'' e'')
                          | _, _ => None
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
  
Check item.
  Fixpoint applyValMapItem (rho : Valuation) (mi : MapItem) : option _map_item :=
    match mi with
      | var_mi v => match (rho (mivar v)) with
                      | to_m_map_item m => Some m
                      | _ => None
                    end
      | item i' v => match (applyValID rho i'), (applyValExp rho v) with
                       | Some i'', Some e' => Some  (i'', e')
                       | _, _ => None
                     end
    end.


  Fixpoint applyValList (rho: Valuation) (l : MIList) : option (list _map_item) :=
    match l with
      | Nil => None
      | Cons e l' => match (applyValMapItem rho e), (applyValList rho l') with
                     | Some v', Some l'' =>  Some (v' :: l'')
                     | _, _ => None
                     end
      | list_var lv => match (rho (lvar lv)) with
                         | to_m_list xv => Some xv
                         | _ => None
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


  
  (* helpers to get free variables *)
  Fixpoint getFreeVarsID (x : ID) : list Var :=
    match x with
      | ivar v => ((idvar v) :: nil)
      | _ => nil
    end.
  Eval compute in (getFreeVarsID (idc a)).
  Eval compute in (getFreeVarsID (ivar X)).

  Fixpoint getFreeVarsExp (e : Exp) : list Var :=
    match e with
      | var_exp v => ((evar v) :: nil)
      | id i' => getFreeVarsID i'
      | plus e1 e2 => append_set (getFreeVarsExp e1) (getFreeVarsExp e2)
      | _ => nil
    end.

  Eval compute in (getFreeVarsExp ($ (idc a))).
  Eval compute in (getFreeVarsExp (val 2)).
  Eval compute in (getFreeVarsExp (!  N)).
  Eval compute in (getFreeVarsExp (plus (! N) (! N))).  

  Fixpoint getFreeVarsMapItem (mi : MapItem) : list Var :=
    match mi with
      | var_mi v => ((mivar v) :: nil)
      | item h e => append_set (getFreeVarsID h) (getFreeVarsExp e)
    end.

  Eval compute in (getFreeVarsMapItem (((idc n) |-> (! N)))).

  Fixpoint getFreeVarsItems (it : MIList) : list Var :=
    match it with
      | Nil => nil
      | Cons v its => append_set (getFreeVarsMapItem v) (getFreeVarsItems its)
      | list_var lv => ((lvar lv) :: nil)
    end.

  Eval compute in (getFreeVarsItems (((idc n) |-> (! N)) ;; Nil)).


  Fixpoint getFreeVarsBExp (be : BExp) : list Var :=
    match be with
      | var_bexp vb => ((bvar vb) :: nil)
      | leq e1 e2 => append_set (getFreeVarsExp e1) (getFreeVarsExp e2)
      | _ => nil
    end.


  Fixpoint getFreeVarsStmt (st : Stmt) : list Var :=
    match st with
      | assign i' e => append_set (getFreeVarsID i') (getFreeVarsExp e)
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

  Print SUM.
  Eval compute in (getFreeVars SUM).
  Eval compute in getFreeVars (AndML (! S >>= (val 0)) SUM).

  
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
        

  Lemma incl_id :
    forall e rho rho' V,
      incl (getFreeVarsID e) V ->
      applyValID rho' e = applyValID (modify_val_on_set rho rho' V) e.
  Proof.
    intros e.
    induction e; intros.
    - simpl in *. trivial.
    - simpl in *.
      rewrite modify_in; trivial.
      unfold incl in H. apply H. simpl. left. reflexivity.
  Qed.

  
  Lemma incl_exp :
    forall e rho rho' V,
      incl (getFreeVarsExp e) V ->
      applyValExp rho' e = applyValExp (modify_val_on_set rho rho' V) e.
  Proof.
    induction e; intros.
    - simpl in *. rewrite <- incl_id; trivial.
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
      rewrite <- incl_id.
      rewrite <- incl_exp.
      trivial.
      apply incl_append_right in H. trivial.
      apply incl_append_left in H. trivial.
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
      rewrite <- incl_id.
      rewrite <- incl_exp; trivial.
      apply incl_append_right in H; trivial.
      apply incl_append_left in H; trivial.      
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
    - simpl in *.
      rewrite modify_in; trivial.
      unfold incl in H.
      apply H.
      simpl.
      left.
      reflexivity.
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


  Lemma not_incl_id:
    forall e rho rho' V,
      (forall x, In x (getFreeVarsID e) -> ~ In x V) ->
      applyValID rho e = applyValID (modify_val_on_set rho rho' V) e.
  Proof.
    induction e; intros.
    - simpl in *. reflexivity.
    - simpl in *.
      rewrite modify_not_in; trivial.
      apply H. left. reflexivity.
  Qed.

    
  Lemma not_incl_exp:
    forall e rho rho' V,
      (forall x, In x (getFreeVarsExp e) -> ~ In x V) ->
      applyValExp rho e = applyValExp (modify_val_on_set rho rho' V) e.
  Proof.
    intros e. induction e; intros; simpl in *; trivial.
    - rewrite <- not_incl_id; trivial.
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
    - rewrite <- not_incl_exp.
      rewrite <- not_incl_id; trivial.
      intros x Hx. apply H. rewrite in_append_iff. left. assumption.
      intros x Hx. apply H. rewrite in_append_iff. right. assumption.
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
    - rewrite <- not_incl_id. rewrite <- not_incl_exp. trivial.
      intros x Hx. apply H. rewrite in_append_iff. right. assumption.
      intros x Hx. apply H. rewrite in_append_iff. left. assumption.
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
    - rewrite modify_not_in; trivial.
      apply H. left. reflexivity.
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
    intros. apply modify_Sat_right; trivial.
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
    intros. apply modify_Sat_left; trivial.
  Qed.
         
End Lang.
