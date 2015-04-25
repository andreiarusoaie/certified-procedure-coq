Require Import formula.
Require Import util.
Require Import rldefs.
Require Import List.

Module Type Definitions (U : Utils)
       (F : Formulas) (R : RL F U) .
  Import U.
  Import F.
  Import R.
  Import ListNotations.

  (* S - derivable *)
  Definition SDerivable (phi : MLFormula) : Prop :=
    exists gamma rho gamma', SatML gamma rho phi /\ (gamma =>S gamma') .
  
  (* Syntactic Derivatives *)
  Definition SynDerML' (phi : MLFormula)
             (F : RLFormula)  : MLFormula :=
    (ExistsML (FreeVars [lhs F; rhs F])
              (AndML
                 (injectFOL (encoding (AndML (lhs F) phi)))
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
  
  Definition SynSDerML (phi : MLFormula) : list MLFormula :=
    map (SynDerML' phi) S .
  
  Definition SynSDerRL (F : RLFormula) : list RLFormula :=
    map (SynDerRL' F) (SynDerML (lhs F) S) .

  (* Delta_S(G) *)
  Fixpoint Delta (S' G' : list RLFormula)
    : list RLFormula :=
      match G' with
        | nil => nil
        | alpha :: G'' =>
          (SynDerRL S' alpha) ++ (Delta S' G'')
      end.
  
  
  (* Symbolic transition relation *)
  Definition TS_Symb (phi phi' : MLFormula) : Prop :=
    In phi' (SynSDerML phi).
  
  (* Symbolic paths *)
  Definition SymPath := GPath MLFormula .
  Definition wfSymPath := wfGPath MLFormula TS_Symb.
  Definition isInfiniteSym (mu : SymPath) :=
    isInfiniteGPath MLFormula mu.
  Definition SymPath_i (mu : SymPath) := GPath_i MLFormula mu.

  (* complete SPath *)
  Definition completeSymPath (mu : SymPath) : Prop :=
    (isInfiniteSym mu -> forall i,
                         exists phi,
                           mu i = Some phi-> SDerivable phi)
    \/
    (exists n phi, mu n = Some phi ->
                   (~ SDerivable phi)
                   /\
                   forall i, exists phi',
                     i < n -> mu i = Some phi'
                     -> SDerivable phi').

  (* startsFromSymPath *)
  Definition startsFromSymPath (mu : SymPath)
             (phi : MLFormula) : Prop :=
    exists phi0,
      mu 0 = Some phi0 /\ ValidML (ImpliesML phi0 phi).
  
  (* Symbolic paths satisfaction *)
  Definition SatSymb (mu : SymPath)
             (F : RLFormula) : Prop :=
    startsFromSymPath mu (lhs F) /\
    (isInfiniteSym mu
     \/
     (completeSymPath mu /\
      exists i phi_i,
        mu i = Some phi_i /\
        ValidML (ImpliesML phi_i (rhs F)))).

  (* Cover 1 : symb covers concrete *)
  Definition cover (mu : SymPath) (tau : Path) : Prop :=
    forall i, exists rho phi gamma,
      mu i = Some phi /\ tau i = Some gamma ->
      SatML gamma rho phi .

  (* Cover 2 : symb covers symb *)
  Definition scover (mu mu' : SymPath) : Prop :=
    forall i, exists phi phi',
      mu i = Some phi /\ mu' i = Some phi' ->
      ValidML (ImpliesML phi' phi).
  
End Definitions.