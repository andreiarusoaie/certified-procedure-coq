Require Import term.
Require Import List.

Parameter PSymbol : Set .
Definition Predicates := list (PSymbol * list Sort)%type .

Parameter Σ : Signature .
Parameter Π : Predicates .

Definition FOLSignature := (Σ, Π).


Inductive FOLFormula :=
| t : FOLFormula
| pred : PSymbol -> list Term -> FOLFormula
| notFOL : FOLFormula -> FOLFormula
| andFOL : FOLFormula -> FOLFormula -> FOLFormula
| existsFOL : list Var -> FOLFormula -> FOLFormula .

(* TODO 
Fixpoint wff (Φ : FOLSignature) (f : FOLFormula) :=
*)







Variables p1 p2 : PSymbol.
Variables f1 f2 : OpSymbol .
Variables s1 s2 : Sort.
Variables v1 v2 : Var .

Definition Sigma := sig (s1 :: s2 :: nil)
                        ((f1, ((s1 :: s1 :: nil), s2)) ::
                        (f2, ((s1 :: nil), s1)) :: nil) .

Definition Pi := (p1, (s1 :: s2 ::nil)) :: nil .

Definition S := (Sigma, Pi) .

Eval compute in tcst f1 .
Eval compute in tvar v1.
Eval compute in (p1, s1 :: s1 :: nil) :: nil .
Eval compute in pred p1 ((tcst f1) :: (tvar v1) :: nil) . 