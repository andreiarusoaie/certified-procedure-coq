Require Import Arith.

Module Utils .
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
   

   (* sublist wf induction *)
   Inductive strictsublist {A : Type} : list A -> list A -> Prop :=
   | strictsublist_nil : forall h t, strictsublist nil (h :: t)
   | strictsublist_skip : forall l1 h t, strictsublist l1 t -> strictsublist l1 (h :: t)
   | strictsublist_cons : forall h t1 t2, strictsublist t1 t2 -> strictsublist (h :: t1) (h :: t2).
   

   Lemma strictsublist_wf (A : Type) :
     well_founded (strictsublist (A := A)).
   Proof.
     eapply well_founded_lt_compat with (f := (length (A := A))).
     intros l1 l2 H.
     induction H; simpl; auto with arith.
   Qed.
   
   Lemma strictsublist_wf_ind (A : Type) (P : list A -> Prop) :
     (forall l, (forall l', strictsublist l' l -> P l') -> P l) -> forall l: list A, P l.
   Proof.
     intros H1 l.
     elim (strictsublist_wf _ l).
     intros l' _ H3.
     apply H1.
     exact H3.
   Qed.
   

  End InductionPrinciple.

  
End Utils.