Require Import Arith.

Module Type Utils .
  Import Wf_nat.
  
  Section Paths .
    (* generic paths *)
    Definition GPath (T : Type) := nat -> option T.
    Definition wfGPath (T : Type) (rel : T -> T -> Prop) (p : GPath T)
    : Prop :=
      (forall i j, i < j -> p i = None -> p j = None)
      /\
      (forall i,
         ((p i <> None) /\ (p (i + 1) <> None)) ->
         exists e e',
           p i = Some e 
           /\ 
           p (i+1) = Some e' /\ (rel e e')).
    
    Definition isInfiniteGPath (T : Type) (p : GPath T) : Prop :=
      forall i, p i <> None.
  
    Definition GPath_i (T : Type) (p : GPath T) (i : nat) : GPath T :=
      fun j => p (i+j).

    Definition lengthGPath (T : Type)
               (rel : T -> T -> Prop)
               (mu : GPath T) (n : nat) : Prop :=
      ~ isInfiniteGPath T mu /\ wfGPath T rel mu /\ 
      exists n phi,
        mu n = Some phi /\ mu (n + 1) = None.
    
  End Paths.


  Section InductionPrinciple.

      (* custom induction principle *)
   Lemma custom_lt_wf_ind :
     forall (P:nat -> Prop),
       P 0 ->
       (forall n,
          (forall m,
             m <= n -> P m) -> P (Datatypes.S n)) ->
       (forall n, P n).
   Proof.
     intros P H1 H2 n.
     apply lt_wf_ind.
     intros n0 H3.
     case_eq n0; intros; trivial.
     subst.
     apply H2.
     intros m H.
     apply H3.
     apply le_lt_n_Sm in H; trivial.
   Qed.
   
  End InductionPrinciple.

  
End Utils.