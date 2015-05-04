Require Import formula.
Require Import util.
Require Import List.

Module Type RL (F : Formulas) (U : Utils).
  Import F.
  Import U.
  
  (* RL *)
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).
  Notation lhs := fst .
  Notation rhs := snd .

  Parameter RLFormula_eq_dec :
    forall x y : RLFormula, {x = y} + {x <> y}.

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
      
  (* transition system *)
  Definition TS (gamma gamma' : State) : Prop :=
    exists phi phi' rho,
      In (phi => phi') S /\
      (SatML gamma rho phi) /\ (SatML gamma' rho phi').
  Notation "f =>S f'" := (TS f f') (at level 100).

  (* concrete paths *)
  Definition Path := GPath State.
  Definition wfPath := wfGPath State TS.
  Definition isInfinite (tau : Path) := isInfiniteGPath State tau.
  Definition Path_i (tau : Path) := GPath_i State tau.
  
  (* starts from *)
  Definition startsFrom (tau : Path) (rho : Valuation) 
             (phi : MLFormula) : Prop :=
    exists gamma, tau 0 = Some gamma /\ SatML gamma rho phi .

  (* terminating state *)
  Definition terminating (gamma : State) :=
    forall gamma', not (gamma =>S gamma') .

  (* complete path *)
  Definition complete (tau : Path) :=
    exists i gamma, tau i = Some gamma /\ terminating gamma.

  (* path satisfaction *)
  (* Note: the path should be well-formed *)
  Definition SatRL (tau : Path) (rho : Valuation) 
             (F : RLFormula) : Prop :=
    startsFrom tau rho (lhs F) /\
    (isInfinite tau
      \/
      (complete tau /\
       exists i gamma, tau i = Some gamma
                       /\ SatML gamma rho (rhs F))).

  (* RL satisfaction *)
  Definition SatTS (F : RLFormula) : Prop :=
    forall tau rho, wfPath tau -> 
                    startsFrom tau rho (lhs F) ->
                    (complete tau \/ isInfinite tau) ->
                    SatRL tau rho F .

  (* RL satisfaction for a set of formulas *)
  Definition SatTS_G (G : list RLFormula) : Prop :=
    forall F, In F G -> SatTS F.

  
End RL.