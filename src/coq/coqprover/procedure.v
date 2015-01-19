Require Import logic .
Require Import List .
Require Import Arith .

Definition Path := nat -> option Model.

Definition PathTo (tau : Path) (n : nat) : Path :=
  fun (i : nat) => if (leb n i)
                   then None
                   else tau i . 


Definition PathFrom (tau : Path) (n : nat) : Path :=
  fun (i : nat) => if (leb i n)
                   then tau i
                   else None .

Definition nth (tau : Path) (n : nat) : option Model := tau n.


Parameter Path_eq_dec : Path -> Path -> Prop .
Definition isPrefix (p : Path) (P : Path) := exists i, Path_eq_dec (PathTo P i) p .

Definition isProperPrefix (p : Path) (P : Path) := exists i, (Path_eq_dec (PathTo P i) p /\ not (nth P (i + 1) = None)) .

Lemma prefix: forall p, forall P, isProperPrefix p P -> isPrefix p P .
Proof.
  intros.
  destruct H.
  destruct H.
  unfold isPrefix.
  exists x.
  assumption.
Qed.  

Definition completePath (P : Path) := forall p : Path, not (isProperPrefix P p) .

Definition StartsFrom (tau : Path) (rho : Valuation) (phi : MLFormula) :=
  exists gamma, nth tau 0 = Some gamma /\ Satisfies gamma rho phi .


(* All Paths Reachability Satisfaction *)

Definition APRLFormula := (MLFormula*MLFormula)%type .
Notation "L ==> R" := (L, R) (at level 100).
Notation Lhs := fst.
Notation Rhs := snd. 

Parameter isInfinite : Path -> Prop .
Parameter infiniteIsComplete : forall p : Path, isInfinite p -> completePath p .


(* (tau, rho) |= phi ==> phi' *)
Definition entails (tau : Path) (rho : Valuation) (F : APRLFormula) :=
  (StartsFrom tau rho (Lhs F)) ->
  (or (exists i, exists gamma,
                   (nth tau i = Some gamma) /\ Satisfies gamma rho (Rhs F))
      (isInfinite tau)).

(* =>S |= phi ==> phi' *)
Definition entailsTS (TS : RLSystem -> Model -> Model -> Prop) (F : APRLFormula)
  := forall (tau : Path), forall (rho : Valuation),
       (StartsFrom tau rho (Lhs F)) -> (entails tau rho F) .

(*
Definition f : { x : nat | x > 5 } -> nat := fun n => n-1.
Lemma f_prop : forall n, f n > 4

Definition f' : nat -> nat := x-1.
Lemma f'_prop : forall n, n > 5 -> f n > 4
                                 
Definition pos := nat.

(* Semantics for phi ==> phi' *)
Definition sem (F: APRLFormula) :=
  { tau : Path & (exists (rho : Valuation), entails tau rho F) } .
*)



(* S-Derivative *)
Definition SDerivative (phi phi' phi1 : MLFormula) :=
  forall (tau1 : Path), forall (rho : Valuation),
    (entails tau1 rho (phi1 ==> phi')) ->
    (exists (tau : Path),
       entails tau rho (phi ==> phi') /\ (Path_eq_dec tau1 (PathFrom tau 1))).

(* Proper S-Derivative  phi1 => phi'  phi => phi' *)
Definition ProperSDerivative (phi phi' phi1 : MLFormula) :=
  SDerivative phi phi' phi1 /\
  (exists tau, exists rho, entails tau rho (phi ==> phi')) .

(* S-Derivable *)
Definition SDerivable (F : APRLFormula) :=
  exists (phi1 : MLFormula), ProperSDerivative (Lhs F) (Rhs F) phi1 .

(* Complete *)
Definition completeSetsOfDer (Δ : list APRLFormula) (phi phi' : MLFormula):=
  forall (phi1 : MLFormula),
    SDerivative phi phi' phi1 -> In (phi1 ==> phi') Δ.
                             
      

(* FOL encoding *)
Fixpoint bp (phi : MLFormula) : list MLFormula :=
  match phi with
    | T => nil
    | Bp C => (Bp C) :: nil
    | Fol F => nil
    | Not phi' => bp phi'
    | And phi' phi'' => (bp phi') ++ (bp phi'') 
    | Or phi' phi'' => (bp phi') ++ (bp phi'') 
    | Implies phi' phi'' => (bp phi') ++ (bp phi'') 
    | logic.Exists v phi' => (bp phi')
  end.

Fixpoint conjGen (L : list MLFormula) : MLFormula :=
  match L with
    | t :: nil => ??
    | C :: Rest => Equals C (conjGen Rest)
  end.

Fixpoint phiEQ (phi : MLFormula) (conj : MLFormula) : MLFormula :=
  match phi with
    | T => T
    | Bp C => conj
    | Not phi' => phiEQ phi' conj
    | And phi' phi'' => And (phiEQ phi' conj) (phiEQ phi'' conj) 
    | Or phi' phi'' => Or (phiEQ phi' conj) (phiEQ phi'' conj) 
    | Implies phi' phi'' => Implies (phiEQ phi' conj) (phiEQ phi'' conj) 
    | logic.Exists v phi' => logic.Exists v (phiEQ phi' conj)
    | Equals phi' phi'' => Equals (phiEQ phi' conj) (phiEQ phi'' conj)
  end.



Parameter pi1 : logic.Cfg.
Parameter pi2 : logic.Cfg.
Parameter pi3 : logic.Cfg.
Parameter pi4 : logic.Cfg.

(* (pi1 /\ T) /\ ( pi2 -> not pi3  \/ pi4 ) *)
Eval compute in
    And
      (And (Bp pi1) T)
      (Or
         (Implies (Bp pi2) (Not (Bp pi3)))
         (Bp pi4)
      ).

Eval compute in bp (And
      (And (Bp pi1) T)
      (Or
         (Implies (Bp pi2) (Not (Bp pi3)))
         (Bp pi4)
      ))
.

Eval compute in conjGen (bp (And
      (And (Bp pi1) T)
      (Or
         (Implies (Bp pi2) (Not (Bp pi3)))
         (Bp pi4)
      ))).

Eval compute in phiEQ
                  (And
                     (And (Bp pi1) T)
                     (Or
                        (Implies (Bp pi2) (Not (Bp pi3)))
                        (Bp pi4)
                     ))
                  (conjGen (bp (And
      (And (Bp pi1) T)
      (Or
         (Implies (Bp pi2) (Not (Bp pi3)))
         (Bp pi4)
      )))).


Definition phi := Or (And (Bp pi1) T) (And (Bp pi2) T).
Eval compute in phi .
Eval compute in bp phi.
Eval compute in conjGen (bp phi) .
