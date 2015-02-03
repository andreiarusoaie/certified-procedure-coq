Module Type Formulas.

  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Parameter FOLFormula : Type .

  Parameter MLFormula : Type .
  Parameter MLFormula_eq_dec : MLFormula -> MLFormula -> Prop .
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .

  Definition Valuation : Type := Term -> Model .
  Parameter folenc : MLFormula -> FOLFormula .
  Parameter FolToML : FOLFormula -> MLFormula .
  Parameter SatFOL : forall (rho : Valuation)
                            (phi : FOLFormula) ,Prop .
  Parameter SatML : forall (rho : Valuation) (gamma : Model)
                           (phi : MLFormula) , Prop .

  Parameter FreeVars : list MLFormula -> list Var .

  Axiom Prop1 : forall varphi rho,
                  SatFOL rho (folenc varphi) <->
                  exists gamma, SatML rho gamma varphi .
End Formulas.


Module Soundness (F : Formulas).
  Require Import List .
  Import F.

  Import ListNotations.
  
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).

  Section RLSemantics.
    Definition TS_Spec := list RLFormula.
    Variable S : TS_Spec .

    Definition TS_S (gamma gamma' : Model) : Prop :=
    exists phi phi' rho,
    In (phi => phi') S ->
    (SatML rho gamma phi) /\ (SatML rho gamma' phi').

    Notation "f =>S f'" := (TS_S f f') (at level 100).

    Definition Path := nat -> option Model.
    
    Definition wfPath (tau : Path) : Prop :=
      (forall i j, i < j -> tau i = None -> tau j = None)
      /\
      (forall i, exists gamma gamma', 
         tau i = Some gamma 
         /\ 
         tau (i+1) = Some gamma' /\ (gamma =>S gamma'))
    .
         
    Definition isInfinite (tau : Path) : Prop :=
      forall i, tau i <> None.

    Definition Path_i (tau : Path) (i : nat) : Path :=
      fun j => tau (i+j).

    Definition startsFrom (p : Path) (rho : Valuation) 
               (phi : MLFormula) : Prop :=
      exists gamma, p 0 = Some gamma -> SatML rho gamma phi .


    Notation lhs := fst .
    Notation rhs := snd .

    Definition SatRL (tau : Path) (rho : Valuation) 
               (F : RLFormula) : Prop :=
      (startsFrom tau rho (lhs F) 
       /\ 
       exists i gamma, tau i = Some gamma -> SatML rho gamma (rhs F)) 
      \/ isInfinite tau .

    Definition SatTS_S (F : RLFormula) : Prop :=
      forall tau rho, startsFrom tau rho (lhs F) -> SatRL tau rho F .

    Definition sem_RL (F : RLFormula) : Path -> Prop :=
      fun tau => exists rho, SatRL tau rho F .
    
    Definition SDer (f : RLFormula) (F : RLFormula) : Prop :=
      MLFormula_eq_dec (rhs f) (rhs F) ->
      forall tau1 rho, SatRL tau1 rho (lhs f => rhs f) -> 
                       (exists tau, SatRL tau rho (lhs F => rhs F) 
                                    /\ 
                                    Path_i tau 1 = tau1).
(*
    Definition SDer (phi : MLFormula) (phi' : MLFormula)
               (phi1 : MLFormula) : Prop :=
      forall tau1 rho, SatRL tau1 rho (phi1 => phi') -> 
                       (exists tau, SatRL tau rho (phi => phi') 
                                    /\ 
                                    Path_i tau 1 = tau1).
*)
    Definition SDerSet (Delta : list RLFormula) 
               (F : RLFormula) : RLFormula -> Prop :=
      fun f => In f Delta -> SDer f F.
      

    Definition sem_SDerSet (Delta : list RLFormula) 
               (F : RLFormula) : Path -> Prop :=
      fun tau => exists f, SDerSet Delta F f /\ sem_RL f tau .

    Definition completeSDerSet (Delta : list RLFormula) 
               (F : RLFormula) : Prop :=
      forall f, 
        SDer f F -> forall tau, sem_RL f tau -> sem_SDerSet Delta F tau .
      
    Definition SDerivable (phi : MLFormula) : Prop :=
      exists gamma rho, SatML rho gamma phi /\ 
                        exists gamma', TS_S gamma gamma' .

    Definition SynSDerML (phi : MLFormula) : MLFormula -> Prop :=
      fun f =>  exists F, In F S ->
                          f = (AndML 
                                 (ExistsML (FreeVars [lhs F; rhs F]) 
                                           (FolToML (folenc (AndML (lhs F) phi))))
                                 (rhs F)). 
    
    Definition SynSDerRL (F : RLFormula) : RLFormula -> Prop :=
      fun f => (rhs F) = (rhs f) /\ SynSDerML (lhs F) (lhs f) .

  End RLSemantics.
    
End Soundness.
