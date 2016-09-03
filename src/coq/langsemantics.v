Require Import util.
Require Import ml.
Require Import List.
Require Import lang.
Require Import rl.
Require Import Classical.

Module Semantics : RL Lang.
  Import Lang.
  Import Utils.
  Import ListNotations.
  
  (* get free variables for a list of ML formulas *)
  Fixpoint FreeVars (l : list MLFormula) : list Var :=
    match l with
      | nil => nil
      | a' :: l' => getFreeVars a' ++ (FreeVars l')
    end.

    (* RL *)
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).
  Notation lhs := fst .
  Notation rhs := snd .


    (* well Formed *)
  Definition wfFormula (F : RLFormula) : Prop :=
    incl (getFreeVars (rhs F)) (getFreeVars (lhs F)).  

  (* helper *)
  Lemma wf_free :
    forall phi phi' x,
      wfFormula (phi => phi') ->
      (In x (getFreeVars phi ++ getFreeVars phi') <-> In x (getFreeVars phi)).
  Proof.
    intros phi phi' x H.
    split; intros H'.
    - unfold wfFormula, incl in H.
      rewrite in_app_iff in H'.
      destruct H' as [H' | H']; trivial.
      apply H in H'; trivial.
    - rewrite in_app_iff.
      left.
      trivial.
  Qed.


  (* helper *)
  Lemma RL_decompose :
    forall F : RLFormula, F = ((lhs F) => (rhs F)).
  Proof.
    intros F.
    destruct F.
    simpl.
    reflexivity.
  Qed.


(*
  (* RL formulas *)
  Definition skip_rule :=
    (pattern (cfg (seq skip (var_stmt St)) (list_var Rest)) ,
     pattern (cfg (var_stmt St) (list_var Rest))).



  
  (* TODO: add other rules *)
  Definition S := (skip_rule :: nil).
 *)
  Parameter S : list RLFormula.


  
  (* transition given by a single rule *)
  Definition TS_rule (gamma gamma' : State)
             (alpha : RLFormula) : Prop :=
    exists rho,
      SatML gamma rho (lhs alpha) /\ SatML gamma' rho (rhs alpha) .
  
  (* transition system given by a set of rules *)
  Definition TS (S' : list RLFormula) (gamma gamma' : State) : Prop :=
    exists phi phi' rho,
      In (phi => phi') S' /\
      (SatML gamma rho phi) /\ (SatML gamma' rho phi').
  Notation "f =>S f'" := (TS S f f') (at level 100).

  
  (* concrete paths *)
  Definition Path := GPath State.
  Definition wfPath := wfGPath State (TS S).
  Definition Path_i (tau : Path) := GPath_i State tau.
  Definition isInfinite (tau : Path) := isInfiniteGPath State tau. 
  
  (* starts from *)
  Definition startsFrom (tau : Path) (rho : Valuation) 
             (phi : MLFormula) : Prop :=
    exists gamma, tau 0 = Some gamma /\ SatML gamma rho phi .

  (* terminating state *)
  Definition terminating (gamma : State) :=
    forall gamma', not (gamma =>S gamma') .

  (* complete path with n transitions *)
  Definition completeN (tau : Path) (n : nat) :=
    exists gamma, tau n = Some gamma /\ terminating gamma.

  Definition complete (tau : Path) :=
    isInfinite tau \/ (~ isInfinite tau /\ exists n, completeN tau n) .

  (* path satisfaction *)
  (* Note: the path should be well-formed *)
  Definition SatRL (tau : Path) (rho : Valuation) 
             (F : RLFormula) : Prop :=
    startsFrom tau rho (lhs F) /\
    ((exists n i gamma,
       i <= n /\
       completeN tau n /\
       tau i = Some gamma /\
       SatML gamma rho (rhs F))
    \/
    isInfinite tau).
                   
  (* RL satisfaction *)
  Definition SatTS (F : RLFormula) : Prop :=
    forall tau rho,
      wfPath tau ->
      startsFrom tau rho (lhs F) ->
      complete tau ->
      SatRL tau rho F.

  (* RL satisfaction for a set of formulas *)
  Definition SatTS_G (G : list RLFormula) : Prop :=
    forall F, In F G -> SatTS F.



  (* ML helper relation *)
  Definition ML_val_relation (phi : MLFormula) (rho : Valuation)
             (phi' : MLFormula) (rho' : Valuation) : Prop :=
    forall gamma, SatML gamma rho phi <-> SatML gamma rho' phi'.
        

  (* RL_alpha_equiv *)
  Definition RL_alpha_equiv (F1 F2 : RLFormula) : Prop :=
    (forall rho, exists rho',
      (ML_val_relation (lhs F1) rho (lhs F2) rho') /\ (ML_val_relation (rhs F1) rho (rhs F2) rho')) /\
    (forall rho, exists rho',
       (ML_val_relation (lhs F2) rho (lhs F1) rho') /\ (ML_val_relation (rhs F2) rho (rhs F1) rho')) /\
    wfFormula F1 /\ wfFormula F2.
  
  Lemma RL_alpha_equiv_ML :
    forall f f' g g',
      RL_alpha_equiv (f => f') (g => g') ->
      forall rho, exists rho',
        (ML_val_relation f rho g rho') /\ (ML_val_relation f' rho g' rho') .
  Proof.
    intros.
    unfold RL_alpha_equiv in *.
    simpl in *.
    assert (H':  exists rho' : Valuation,
        ML_val_relation (lhs (f => f')) rho (lhs (g => g')) rho' /\
        ML_val_relation (rhs (f => f')) rho (rhs (g => g')) rho').
    apply H.
    destruct H' as (rho' & H' & H'').
    simpl in *. exists rho'. split; trivial.
  Qed.

  
  Lemma RL_alpha_equiv_sym :
    forall F F',
      RL_alpha_equiv F F' -> RL_alpha_equiv F' F.
  Proof.
    intros F F' H.
    unfold RL_alpha_equiv in *.
    destruct H as (H1 & H2 & H7 & H8).
    split. intros rho.
    - assert (H: exists rho' : Valuation,
         ML_val_relation (lhs F') rho (lhs F) rho' /\
         ML_val_relation (rhs F') rho (rhs F) rho'); trivial.
    - split. intros rho.
      assert (H: exists rho' : Valuation,
         ML_val_relation (lhs F) rho (lhs F') rho' /\
         ML_val_relation (rhs F) rho (rhs F') rho'); trivial.
      split; trivial.
  Qed.
    
  Lemma RL_alpha_equiv_wf :
    forall F F',
      wfFormula F -> RL_alpha_equiv F F' -> wfFormula F'.
  Proof.
    intros F F' H H'.
    unfold RL_alpha_equiv in H'.
    destruct H' as (_ & _ & _ & H'); trivial.
  Qed.

  (* Extension to sets *)
  Definition RL_alpha_equiv_S (S S' : list RLFormula) : Prop :=
    (forall F, In F S -> exists F_eqv, In F_eqv S' /\ RL_alpha_equiv F F_eqv) /\
    (forall F_eqv, In F_eqv S' -> exists F, In F S /\ RL_alpha_equiv F_eqv F).

  (* Disjoint variables section *)
  Definition disjoint_vars (phi phi' : MLFormula) : Prop :=
    (forall x, In x (getFreeVars phi) -> ~ In x (getFreeVars phi')) .

  Definition disjoint_set_RL (F' : RLFormula) (V : list Var) : Prop :=
    (forall x, In x V -> ~ In x (FreeVars (lhs F' :: (rhs F' :: nil)))) .

  Definition disjoint_vars_RL (F F' : RLFormula) : Prop :=
    disjoint_vars (lhs F) (lhs F').
  
  Definition disjoint_vars_rules (S' : list RLFormula) (F : RLFormula) :=
    forall alpha, In alpha S' -> disjoint_vars_RL alpha F .

  (* helper *)
  Lemma disjoint_vars_RL_sym :
    forall F F',
      disjoint_vars_RL F F' <-> disjoint_vars_RL F' F.
  Proof.
    intros F F'. split; intros H;
    unfold disjoint_vars_RL, disjoint_vars in *;
    intros x Hx; unfold not; intros C; apply H in C;
    contradiction.
  Qed.


  Definition RLFormula_eq_dec (F F' : RLFormula) : bool :=
    andb (MLFormula_eq_dec (lhs F) (lhs F')) (MLFormula_eq_dec (rhs F) (rhs F')).

  Lemma RLFormula_eq_dec_refl :
    forall F, RLFormula_eq_dec F F = true.
  Proof.
    intros F. destruct F.
    unfold RLFormula_eq_dec. simpl.
    rewrite 2 MLFormula_eq_dec_refl.
    simpl. reflexivity.
  Qed.

  Lemma RLFormula_eq_dec_true :
    forall F F',
      RLFormula_eq_dec F F' = true -> F = F'.
  Proof.
    intros F F' H.
    destruct F, F'.
    unfold RLFormula_eq_dec in H.
    simpl in *.
    case_eq (MLFormula_eq_dec m m1). intros H1.
    case_eq (MLFormula_eq_dec m0 m2). intros H2.
    - apply MLFormula_eq_dec_true in H1.
      apply MLFormula_eq_dec_true in H2.
      subst. reflexivity.
    - intros H2.
      rewrite H1, H2 in H. simpl in H. inversion H.
    - intros H1.
      rewrite H1 in H. simpl in H. inversion H.
  Qed.

  Lemma RLFormula_eq_dec_false :
    forall F1 F2, RLFormula_eq_dec F1 F2 = false -> F1 <> F2.
  Proof.
    intros F1 F2 H. unfold not. intros H'. subst.
    rewrite RLFormula_eq_dec_refl in H. inversion H.
  Qed.

End Semantics.