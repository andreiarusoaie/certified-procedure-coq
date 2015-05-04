Require Import formula.
Require Import util.
Require Import rldefs.
Require Import definition.
Require Import List.
Require Import Classical.

Module Type External (F : Formulas) (U : Utils)
       (R : RL F U) (Def : Definitions U F R).
  Import F U R Def.
  Import ListNotations.
  
  (* we assume the existence of an ML prover 
     with this interfaces *)
  Parameter check_Valid : MLFormula -> bool .
  Parameter check_Derivable : MLFormula -> list RLFormula -> bool .

  Parameter Valid : RLFormula -> Prop .
  Parameter DerivableS : MLFormula -> Prop .


  (* axioms over Valid and DerivableS *)
  Axiom axiom_Valid :
    forall F,
      check_Valid (ImpliesML (lhs F) (rhs F)) = true -> Valid F.

  Axiom axiom_DerivableS :
    forall phi, 
      check_Derivable phi S = true -> DerivableS phi.

  Axiom impl_V : forall phi phi',
                   Valid (phi => phi') ->
                   ValidML (ImpliesML phi phi') .
  
  Axiom der_D : forall phi,
                  DerivableS phi -> SDerivable phi.

  Axiom prop1 : forall phi phi',
                  DerivableS phi' -> Valid (phi => phi')
                  -> DerivableS phi.
  
  Axiom prop2 : forall phi,
                  DerivableS phi ->
                  DerivableS (EClos phi).

  Axiom prop3 : forall phi phi' phi'',
                  Valid (phi => phi') ->
                  Valid (phi' => phi'') ->
                  Valid (phi => phi'').

  (* this should be a lemma *)
  Axiom prop4 : forall phi, Valid (phi => phi).
  
End External.