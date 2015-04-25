
Module Type Utils .

  (* generic paths *)
  Definition GPath (T : Type) := nat -> option T.
  Definition wfGPath (T : Type) (rel : T -> T -> Prop) (tau : GPath T)
               : Prop :=
    (forall i j, i < j -> tau i = None -> tau j = None)
    /\
    (forall i,
       ((tau i <> None) /\ (tau (i + 1) <> None)) ->
       exists e e',
         tau i = Some e 
         /\ 
         tau (i+1) = Some e' /\ (rel e e')).

  Definition isInfiniteGPath (T : Type) (tau : GPath T) : Prop :=
    forall i, tau i <> None.
  
  Definition GPath_i (T : Type) (tau : GPath T) (i : nat) : GPath T :=
    fun j => tau (i+j).

End Utils.