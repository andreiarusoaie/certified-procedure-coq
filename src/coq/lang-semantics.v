Require Import util.
Require Import ml.
Require Import List.
Require Import lang.
Require Import rl.
Require Import Classical.

Module Semantics <: RL.
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

  Definition RLFormula_eq_dec :=
    forall x y : RLFormula, {x = y} + {x <> y}.

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



  (* RL formulas *)
  Definition skip_rule :=
    (pattern (cfg (seq skip (var_stmt St)) (list_var Rest)) ,
     pattern (cfg (var_stmt St) (list_var Rest))).

  (* TODO: add other rules *)
  Definition S := (skip_rule :: nil).

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
    forall gamma, SatML gamma rho phi -> SatML gamma rho' phi' .
  

  Print TS_rule.
  (* RL_alpha_equiv *)
  Definition RL_alpha_equiv (F1 F2 : RLFormula) : Prop :=
    forall rho, exists rho',
      (ML_val_relation (lhs F1) rho (lhs F2) rho') /\ (ML_val_relation (rhs F1) rho (rhs F2) rho') .
  
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
    destruct H' as (rho' & H').
    exists rho'; trivial.
  Qed.

  
  Lemma RL_alpha_equiv_sym :
    forall F F',
      RL_alpha_equiv F F' -> RL_alpha_equiv F' F.
  Proof.
  Admitted.
  
    
  Axiom RL_alpha_equiv_wf :
    forall F F',
      wfFormula F -> RL_alpha_equiv F F' -> wfFormula F'.

  (* Extension to sets *)
  Definition RL_alpha_equiv_S (S S' : list RLFormula) : Prop :=
    (forall F, In F S -> exists F_eqv, In F_eqv S' /\ RL_alpha_equiv F F_eqv) /\
    (forall F_eqv, In F_eqv S' -> exists F, In F S /\ RL_alpha_equiv F_eqv F).


  
End Semantics.