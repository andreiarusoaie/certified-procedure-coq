Require Import formula.
Require Import util.
Require Import List.

Module Type RL (F : Formulas) (U : Utils).
  Import F.
  Import U.
  Import ListNotations.

  (* get free variables for a list of ML formulas *)
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


  
  (* Hereafter S is a set of RLFormula *)
  Variable S : list RLFormula .

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
  

  (* RL_alpha_equiv *)
  Parameter RL_alpha_equiv : RLFormula -> RLFormula -> Prop.

  Axiom RL_alpha_equiv_ML :
    forall f f' g g',
      RL_alpha_equiv (f => f') (g => g') ->
      forall rho, exists rho',
        (ML_val_relation f rho g rho') /\ (ML_val_relation f' rho g' rho') .

  Axiom RL_alpha_equiv_sym :
    forall F F',
      RL_alpha_equiv F F' -> RL_alpha_equiv F' F.
  
    
  Axiom RL_alpha_equiv_wf :
    forall F F',
      wfFormula F -> RL_alpha_equiv F F' -> wfFormula F'.

  (* Extension to sets *)
  Definition RL_alpha_equiv_S (S S' : list RLFormula) : Prop :=
    (forall F, In F S -> exists F_eqv, In F_eqv S' /\ RL_alpha_equiv F F_eqv) /\
    (forall F_eqv, In F_eqv S' -> exists F, In F S /\ RL_alpha_equiv F_eqv F).

  

  (* Disjoint variables section *)
  Definition disjoint_vars (phi phi' : MLFormula) : Prop :=
    (forall x, In x (getFreeVars phi) -> ~ In x (getFreeVars phi')) .

  Definition disjoint_set_RL (F : RLFormula) (V : list Var) : Prop :=
    (forall x, In x V -> ~ In x (FreeVars [lhs F; rhs F])) .

  Definition disjoint_vars_RL (F F' : RLFormula) : Prop :=
    disjoint_vars (lhs F) (lhs F').
  
  Definition disjoint_vars_rules (S' : list RLFormula) (F : RLFormula) :=
    forall alpha, In alpha S' -> disjoint_vars_RL alpha F .

  (* helper *)
  Lemma disjoint_vars_RL_sym :
    forall F F',
      disjoint_vars_RL F F' <-> disjoint_vars_RL F' F.
  Proof.
    intros F F'.
    split; intros H;
    unfold disjoint_vars_RL, disjoint_vars in *;
    intros x Hx;
    unfold not;
    intros C;
    apply H in C;
    contradiction.
  Qed.
  
End RL.