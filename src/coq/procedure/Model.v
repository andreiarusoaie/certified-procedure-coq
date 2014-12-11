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
                     | symLeInt : SymInt -> SymInt -> SymBool 
                     | symEqInt : SymInt -> SymInt -> SymBool 
                     | symNeg : SymBool -> SymBool 
                     | symAnd : SymBool -> SymBool -> SymBool .
  

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
  
End ImpModel .