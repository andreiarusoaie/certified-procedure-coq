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
    incl (getFreeVars (rhs F)) (getFreeVars (lhs F)).  

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


  Definition disjoint_vars (phi phi' : MLFormula) : Prop :=
    (forall x, In x (getFreeVars phi) -> ~ In x (getFreeVars phi')) /\
    (forall x, In x (getFreeVars phi') -> ~ In x (getFreeVars phi)).
  

  Definition disjoint_vars_rules (S' : list RLFormula) (phi : MLFormula) :=
    forall alpha, In alpha S' -> disjoint_vars (lhs alpha) phi .
  
End RL.