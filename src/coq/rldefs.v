Require Import formula.
Require Import util.
Require Import List.

Module Type RL (F : Formulas) (U : Utils).
  Import F.
  Import U.
  Import ListNotations.

  Fixpoint FreeVars (l : list MLFormula) : list Var :=
    match l with
      | nil => nil
      | a :: l' => getFreeVars a ++ (FreeVars l')
    end.
  
  (* RL *)
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).
  Notation lhs := fst .
  Notation rhs := snd .

  Parameter RLFormula_eq_dec :
    forall x y : RLFormula, {x = y} + {x <> y}.

  (* well Formed *)
  Definition wfFormula (F : RLFormula) : Prop :=
    incl (FreeVars [(rhs F)]) (FreeVars [(lhs F)]).  

  Lemma wf_free :
    forall F x,
      wfFormula F ->
      (In x (FreeVars [lhs F; rhs F]) <-> In x (FreeVars [lhs F])).
  Proof.
    intros F x H.
    split; intros H'.
    - unfold wfFormula, incl in H.
      unfold FreeVars in *.
      rewrite app_nil_r in *.
      rewrite in_app_iff in H'.
      destruct H' as [H' | H']; trivial.
      apply H in H'.
      rewrite app_nil_r in H'.
      trivial.
    - unfold FreeVars in *.
      rewrite app_nil_r in *.
      rewrite in_app_iff.
      left.
      trivial.
  Qed.

  
  Lemma RL_decompose :
    forall F : RLFormula, F = ((lhs F) => (rhs F)).
  Proof.
    intros F.
    destruct F.
    simpl.
    reflexivity.
  Qed.
  
  (* Hereafter S is a set of RLFormula *)
  Variable S : list RLFormula .

  (* rule transition *)
  Definition TS_rule (gamma gamma' : State)
             (alpha : RLFormula) : Prop :=
    exists rho,
      SatML gamma rho (lhs alpha) /\ SatML gamma' rho (rhs alpha) .
  
  (* transition system *)
  Definition TS (gamma gamma' : State) : Prop :=
    exists phi phi' rho,
      In (phi => phi') S /\
      (SatML gamma rho phi) /\ (SatML gamma' rho phi').
  Notation "f =>S f'" := (TS f f') (at level 100).
  
  (* concrete paths *)
  Definition Path := GPath State.
  Definition wfPath := wfGPath State TS.
  Definition Path_i (tau : Path) := GPath_i State tau.
  
  (* starts from *)
  Definition startsFrom (tau : Path) (rho : Valuation) 
             (phi : MLFormula) : Prop :=
    exists gamma, tau 0 = Some gamma /\ SatML gamma rho phi .

  (* terminating state *)
  Definition terminating (gamma : State) :=
    forall gamma', not (gamma =>S gamma') .

  (* complete path *)
  Definition complete (tau : Path) (n : nat) :=
    exists gamma, tau n = Some gamma /\ terminating gamma.

  (* path satisfaction *)
  (* Note: the path should be well-formed *)
  Definition SatRL (tau : Path) (rho : Valuation) 
             (F : RLFormula) : Prop :=
    startsFrom tau rho (lhs F) /\
    (exists n i gamma,
       i <= n /\
       complete tau n /\
       tau i = Some gamma /\
       SatML gamma rho (rhs F)).
                                
  (* RL satisfaction *)
  Definition SatTS (F : RLFormula) : Prop :=
    forall tau rho n,
      wfPath tau ->
      startsFrom tau rho (lhs F) ->
      complete tau n ->
      SatRL tau rho F.

  (* RL satisfaction for a set of formulas *)
  Definition SatTS_G (G : list RLFormula) : Prop :=
    forall F, In F G -> SatTS F.


  Definition rename_vars_RL (X Y : list Var) (F : RLFormula) : RLFormula :=
    (rename_var_set X Y (lhs F)) => (rename_var_set X Y (rhs F)) .
  
End RL.