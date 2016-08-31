Require Import util.
Require Import ml.
Require Import rl.
Require Import List.
Require Import lang.
Require Import langsemantics.
Require Import derivatives.

Module Derivatives : Definitions Lang Semantics.
  Import Utils.
  Import Lang.
  Import Semantics.
  Import ListNotations.

  
  (* S - derivable *)
  Definition SDerivable (phi : MLFormula) : Prop :=
    exists gamma rho gamma', SatML gamma rho phi /\ (gamma =>S gamma') .

  (* Total S *)
  Definition total :=
    forall phi gamma rho,
      SDerivable phi -> SatML gamma rho phi ->
      exists gamma', gamma =>S gamma'.
  
  (* Syntactic Derivatives *)
  Definition SynDerML' (phi : MLFormula)
             (F : RLFormula)  : MLFormula :=
    (ExistsML (FreeVars (lhs F :: (rhs F :: nil)))
              (AndML
                 (encoding (AndML (lhs F) phi))
                 (rhs F))) .
  Definition SynDerRL' (F : RLFormula)
             (phi1 : MLFormula) : RLFormula :=
      phi1 => rhs F .

    
  Definition SynDerML (phi : MLFormula)
             (S' : list RLFormula) : list MLFormula :=
    map (SynDerML' phi) S'.
  
  Definition SynDerRL (S' : list RLFormula)
             (F : RLFormula) : list RLFormula :=
    map (SynDerRL' F) (SynDerML (lhs F) S').
  
  (* Delta_S(G) *)
  Fixpoint Delta (S' G' : list RLFormula)
    : list RLFormula :=
      match G' with
        | nil => nil
        | alpha :: G'' =>
          (SynDerRL S' alpha) ++ (Delta S' G'')
      end.
    
End Derivatives.