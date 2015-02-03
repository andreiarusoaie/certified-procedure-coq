Module Type Formulas.

  Parameter Model : Type .
  Parameter Term : Type .
  Parameter FOLFormula : Type .
  Parameter MLFormula : Type .
  Definition Valuation : Type := Term -> Model .
  Parameter folenc : MLFormula -> FOLFormula .
  Parameter SatFOL : forall (rho : Valuation)
                            (phi : FOLFormula) ,Prop .
  Parameter SatML : forall (rho : Valuation) (gamma : Model)
                           (phi : MLFormula) , Prop .

  Axiom Prop1 : forall varphi rho,
                  SatFOL rho (folenc varphi) <->
                  exists gamma, SatML rho gamma varphi .
End Formulas.

Module Soundness (F : Formulas).
  Require Import List .
  Import F.
  
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).

  Section RLSemantics.
    Definition TS_Spec := list RLFormula.
    Variable S : TS_Spec .

    Definition TS_S (gamma gamma' : Model) : Prop :=
    exists phi phi' rho,
    In (phi => phi') S ->
    (SatML rho gamma phi) /\ (SatML rho gamma' phi').

    Notation "g =>S g'" := (TS_S g g') (at level 100).

    Definition Path := nat -> option Model.
    
    Definition wfPath (p : Path) : Prop :=
      (forall i j, i < j -> p i = None -> p j = None)
      /\
      (forall i, exists gamma gamma', p i = Some gamma /\ p (i+1) = Some gamma' /\ (gamma =>S gamma'))
    .  
     
    
    Definition isInfinite (p : Path) : Prop :=
      forall i, p i <> None.

    Definition Path_i (p : Path) (i : nat) : Path :=
      fun j => p (i+j).

    Definition startsFrom (p : Path) (phi : MLFormula) (rho : Valuation): Prop :=
      exists gamma, p 0 = Some gamma -> SatML rho gamma phi .


    Notation lhs := fst .
    Notation rhs := snd .

    Definition SatRL (tau : Path) (rho : Valuation) (r : RLFormula) : Prop :=
      (startsFrom tau (lhs r) rho /\ exists i gamma, tau i = Some gamma -> SatML rho gamma (rhs r)) \/ isInfinite tau .

    Definition SatTS_S (r : RLFormula) : Prop :=
      forall tau rho, startsFrom tau (lhs r) rho -> SatRL tau rho r .

    Definition semRL (r : RLFormula) : Path -> Prop :=
      fun p => exists rho, SatRL p rho r .
    
  End RLSemantics.

  
    
End Soundness.
