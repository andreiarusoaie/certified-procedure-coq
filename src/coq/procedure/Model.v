Require Import ZArith .
Require Import String .
Require Import List .


Module ImpModel .
  (* Symbolic values *)
  Inductive SymInt := symZ : Z -> SymInt
                    | symInt: string -> SymInt
                    | symPlus : SymInt -> SymInt -> SymInt
                    | symDiv : SymInt -> SymInt -> SymInt
                    | symMult : SymInt -> SymInt -> SymInt .
  Inductive SymBool := symB : bool -> SymBool
                     | symBool : string -> SymBool
                     | symLeqInt : SymInt -> SymInt -> SymBool 
                     | symLeInt : SymInt -> SymInt -> SymBool 
                     | symEqInt : SymInt -> SymInt -> SymBool 
                     | symNeg : SymBool -> SymBool 
                     | symAnd : SymBool -> SymBool -> SymBool .
  
  Scheme Equality for SymInt.
  Scheme Equality for SymBool.
  
    (* State *)
  Definition State := list (string * SymInt) .

  (* Lookup and update state - functions *)
  Fixpoint lookup (x : string) (s : State) :=
    match s with
      | (a, v) :: tl => if (string_dec a x) then Some v else lookup x tl
      | nil => None
    end
  .

  Fixpoint update (x : string) (e : SymInt) (s : State) :=
    match s with
      | (a, v) :: tl => if (string_dec a x)
                        then Some ((a, e) :: tl)
                        else match update x e tl with
                               | Some tl' => Some ((a, v) :: tl')
                               | _ => None
                             end
      | nil => None
    end.

  (*
Open Scope string_scope.
Eval compute in (update "c" 3 (("c", 10)::("b", 5)::nil)).
Eval compute in (update "a" 3 (("c", 10)::("b", 5)::nil)).
Eval compute in (update "b" 3 nil).
   *)

  (* S1 in S2 *)
  Fixpoint stateIncl (S1 S2 : State) :=
    match S1 with
      | (k, v) :: tl => match lookup k S2 with
                          | Some v' => if (SymInt_beq v v')
                                       then stateIncl tl S2
                                       else false
                          | None => false
                        end
      | nil => true
    end.

  (*
  Open Scope string_scope.
  Eval compute in SymInt_beq (symZ 10) (symZ 10) .
  Eval compute in stateIncl
                    (("c", (symZ 10))::("b", (symZ 5))::nil)
                    (("c", (symZ 10))::("b", (symZ 5))::nil) .
  Eval compute in stateIncl
                    (("c", (symZ 10))::("b", (symZ 5))::nil)
                    (("c", (symZ 10))::nil) .
  Eval compute in stateIncl
                    (("c", (symZ 10))::nil)
                    (("c", (symZ 10))::("b", (symZ 5))::nil) .
   *)
  
  Definition State_beq (S1 S2 : State) := andb (stateIncl S1 S2) (stateIncl S2 S1) .

  (*
  Open Scope string_scope.
  Eval compute in State_beq
                    (("c", (symZ 10))::("b", (symZ 5))::nil)
                    (("c", (symZ 10))::("b", (symZ 5))::nil) .
  Eval compute in State_beq
                    (("c", (symZ 10))::("b", (symZ 5))::nil)
                    (("c", (symZ 10))::nil) .
  Eval compute in State_beq
                    (("c", (symZ 10))::nil)
                    (("c", (symZ 10))::("b", (symZ 5))::nil) .
  Eval compute in State_beq nil nil .
  *)
End ImpModel .