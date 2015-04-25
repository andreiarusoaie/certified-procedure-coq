Require Import term.
Require Import List.
Require Import String.

Record Predicate :=
  pred {
      pname : string;
      pargs : list string
    }.

Inductive FOLFormula :=
| t : FOLFormula
| pFOL : Predicate -> list Term -> FOLFormula
| notFOL : FOLFormula -> FOLFormula
| andFOL : FOLFormula -> FOLFormula -> FOLFormula
| existsFOL : list Var -> FOLFormula -> FOLFormula .


Definition Predicates := list Predicate .

(* Well formed formulas *)
Fixpoint wff (Σ : Signature) (Π : Predicates)
         (f : FOLFormula) :=
  match f with
    | t => true
    | pFOL p terms => list_string_eq (pargs p)
                                     (getListOfTermsSorts terms)
    | notFOL f' => wff Σ Π f'
    | andFOL f1 f2 => andb (wff Σ Π f1) (wff Σ Π f2)
    | existsFOL vars f' => wff Σ Π f'
  end.



(* TODO: FOL Model *)
Record FOLModel :=
  folm {
      alg : Type; (* Algebra ?*)
      psets : list Type
    }. 


Fixpoint applyValuationToTerm (rho: Var -> Term)
         (t : Term) :=
  match t with
    | tvar x => rho x
    | term o args => term o (applyValuationToListOfTerms rho args)
  end.

Fixpoint applyValuationToListOfTerms (rho : Var -> Term)
         (l : list Term) :=
  match l with
    | nil => nil
    | t' :: ts => (applyValuationToTerm rho t') ::
                                              (applyValuationToListOfTerms rho ts)
  end.


(* Sat relation *)
Fixpoint FOLSat (F : FOLFormula) (M : FOLModel)
         (rho: Var -> Fun) : Prop :=
  match F with
    | t => True
    | pFOL p args => In (applyValuationToListOfTerms rho args) (psets M)
    | notFOL f => ~ (FOLSat f M rho)
    | andFOL f f' => (FOLSat f M rho) /\ (FOLSat f M rho)
    | existsFOL X f => (exists rho', (forall x,
                                        ~ (In x X) -> (FOLModel_eq_dec (rho' x) (rho x))) /\ (FOLSat F M rho'))
  end.
