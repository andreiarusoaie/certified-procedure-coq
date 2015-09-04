Require Import List.
Require Import Classical.
Require Import Omega.

Module Type Formulas.
  Import ListNotations.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Definition Valuation : Type := Var -> Model .

  Parameter var_eq : Var -> Var -> bool .
  Axiom var_eq_spec_true : forall x y, var_eq x y = true <-> x = y .
  Axiom var_eq_spec_false : forall x y, var_eq x y = false <-> x <> y .
  Axiom var_eq_refl : forall x, var_eq x x = true .
  
  (* FOL *)
  (*
  Parameter FOLFormula : Type .
  Parameter TrueFOL : FOLFormula .
  Parameter NotFOL : FOLFormula -> FOLFormula .
  Parameter AndFOL : FOLFormula -> FOLFormula -> FOLFormula .
  Parameter ExistsFOL : list Var -> FOLFormula -> FOLFormula .

  Definition OrFOL (phi phi' : FOLFormula) : FOLFormula :=
    NotFOL (AndFOL (NotFOL phi) (NotFOL phi')) .

  Definition BigOrFOL (l : list FOLFormula) : FOLFormula :=
    fold_left OrFOL l (NotFOL TrueFOL) .
   *)
  (* FOL satisfaction *)
  (*
  Parameter SatFOL : Valuation -> FOLFormula -> Prop .
  Definition ValidFOL (phi : FOLFormula) : Prop :=
    forall rho, SatFOL rho phi.
  Definition SatisfiableFOL (phi : FOLFormula) : Prop :=
    exists rho, SatFOL rho phi .
  *)
  (* ML *)
  Parameter MLFormula : Type .
  Parameter TrueML : MLFormula .
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter NotML : MLFormula -> MLFormula.
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .
  Definition ImpliesML (phi phi' : MLFormula) : MLFormula :=
    NotML (AndML phi (NotML phi')) .


  (* ML satisfaction *)
  Parameter SatML : State -> Valuation -> MLFormula -> Prop .

  Axiom SatML_Exists :
    forall phi gamma rho V,
      SatML gamma rho (ExistsML V phi) <->
      exists rho',
        (forall v, ~In v V -> rho v = rho' v) /\
        SatML gamma rho' phi.

  Axiom SatML_And :
    forall gamma rho phi phi',
      SatML gamma rho (AndML phi phi') <->
      SatML gamma rho phi /\ SatML gamma rho phi'.

  Axiom SatML_Not :
    forall gamma rho phi,
      SatML gamma rho (NotML phi) <-> ~ SatML gamma rho phi.
  
  Definition ValidML (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.


  
  (* Free variables *)
  Parameter getFreeVars : MLFormula -> list Var .

  (* Modify valuation on set *)
  Definition modify_val_on_var(rho rho' : Valuation) (x : Var) : Valuation :=
    fun z => if (var_eq x z) then rho' x else rho z .

  Fixpoint modify_val_on_set(rho rho' : Valuation) (X : list Var) : Valuation :=
    match X with
      | [] => rho
      | x :: Xs => modify_val_on_var (modify_val_on_set rho rho' Xs) rho' x
    end.
  
  Lemma modify_in :
    forall V x rho rho',
      In x V -> (modify_val_on_set rho rho' V) x = rho' x.
  Admitted.
    
  
  Lemma modify_not_in :
    forall x V rho rho',
      ~ In x V -> (modify_val_on_set rho rho' V) x = rho x.
  Admitted.

  
  Lemma modify_Sat1 :
    forall gamma rho rho' phi V,
      SatML gamma rho' phi ->
      incl (getFreeVars phi) V ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Admitted.
  
  Lemma modify_Sat2 :
    forall gamma rho rho' phi V,
      SatML gamma rho phi ->
      (forall x, In x (getFreeVars phi) -> ~ In x V) ->
      SatML gamma (modify_val_on_set rho rho' V) phi.
  Admitted.
  
  
  (* renaming stuff *)
  Parameter rename_var : Var -> Var -> MLFormula -> MLFormula.

  Axiom new_var_is_free :
    forall x y phi,
      In x (getFreeVars phi) ->
      In y (getFreeVars (rename_var x y phi)) .

  Axiom new_or_old :
    forall x y z phi,
      In z (getFreeVars (rename_var x y phi)) ->
      z = y \/ (z <> y /\ In z (getFreeVars phi)) .
  
  
  Fixpoint rename_var_set (X Y : list Var)
           (phi : MLFormula) : MLFormula :=
    match X, Y with
      | x :: Xs, y :: Ys =>
        rename_var x y (rename_var_set Xs Ys phi)
(*        rename_var_set Xs Ys (rename_var x y phi) *)
      | _, _ => phi
    end.
          
  
  Definition rename_val (rho : Valuation) (x y : Var) : Valuation :=
    fun z => if (var_eq z y) then rho x else rho z .

  Lemma rename_val_not_in :
    forall z rho x y,
      z <> x ->  rename_val rho x y z = rho z.
  Admitted.
  
  
  Lemma rename_sat :
    forall gamma rho phi x y,
      SatML gamma rho phi ->
      ~ In y (getFreeVars phi) ->
      SatML gamma (rename_val rho x y) (rename_var x y phi) .
  Admitted.

  Fixpoint rename_val_set (rho : Valuation) (X Y : list Var) : Valuation :=
    match X, Y with 
      | x :: Xs, y :: Ys =>
        rename_val_set (rename_val rho x y) Xs Ys 
      | _, _ => rho
    end.

  Lemma rename_sat_set :
    forall gamma rho phi X Y,
      SatML gamma rho phi ->
      (forall y, In y Y -> ~ In y (getFreeVars phi)) ->
      SatML gamma (rename_val_set rho X Y) (rename_var_set X Y phi).
  Admitted.

  Lemma rename_val_set_not_in :
    forall v rho X Y,
      ~ In v X -> rename_val_set rho X Y v = rho v.
  Admitted.
  
  

  
(*
  Lemma rename_sat_Set :
    forall gamma rho phi X Y,
      SatML gamma rho phi <->
      SatML gamma rho (rename_vars X Y phi) .
  Proof.
    intros gamma rho phi X Y.
    split; intros H.
    - induction X.
      + simpl; trivial.
      + simpl.
  Admitted.
*)  

  Axiom rename_And :
    forall phi phi' X Y,
      rename_var_set X Y (AndML phi phi') =
      (AndML (rename_var_set X Y phi) (rename_var_set X Y phi')).

  Axiom rename_Not :
    forall phi X Y,
      rename_var_set X Y (NotML phi) =
      (NotML (rename_var_set X Y phi)).

  
  Parameter generate_var_not_in_set : list Var -> Var .
  Axiom new_var_not_in_set :
    forall X,
       ~ In (generate_var_not_in_set X) X.

  Fixpoint generate_vars (n : nat) (X : list Var) : list Var :=
    match n with
      | 0 => nil
      | S n' => let new_x := generate_var_not_in_set X in
                new_x :: generate_vars n' (new_x :: X)
    end.

  Lemma generate_vars_exact_n :
    forall n X,
      n = length (generate_vars n X) .
  Proof.
    induction n; simpl; trivial.
    intros X.
    apply eq_S.
    apply IHn.
  Qed.

    


  Lemma replace_all :
    forall phi Y X y,
      incl (getFreeVars phi) X ->
      length X = length Y ->
      (In y (getFreeVars (rename_var_set X Y phi)) <-> In y Y).
  Proof.
  Admitted.      
    


      
      
  
  Lemma generated_vars_not_in_set :
    forall n X y,
      In y (generate_vars n X) ->
      ~ In y X.
  Proof.
    induction n; intros.
    - simpl in H.
      contradict H.
    - simpl in H.
      destruct H as [H | H].
      + subst y.
        apply new_var_not_in_set.
      + apply IHn in H.
        unfold not in *.
        intros.
        apply H.
        simpl.
        right.
        trivial.
  Qed.

  Lemma generated_vars_not_in :
    forall n x X Y,
      In x X ->
      incl X Y ->
      ~ In x (generate_vars n Y) .
  Proof.
    induction n; intros.
    - simpl.
      unfold not.
      intros.
      trivial.
    - simpl.
      apply and_not_or.
      split.
      + assert (H1 : ~ In (generate_var_not_in_set Y) Y).
        * apply new_var_not_in_set.
        * unfold not.
          intros.
          subst x.
          unfold incl in H0.
          apply H0 in H.
          contradict H1.
          trivial.
      + apply IHn with (X := X); trivial.
        unfold incl.
        intros a Ha.
        simpl.
        right.
        unfold incl in H0.
        apply H0 in Ha; trivial.
  Qed.



  
  (* encoding: ML -> FOL *)
  (* Parameter encoding : MLFormula -> FOLFormula . *)
  Parameter encoding : MLFormula -> MLFormula .

  (* encoding properties *)
  (* 
    The following proposition, looks cleaner when 
    working with both FOL and ML:
    Axiom SatFOL_iff_SatML :
    forall phi rho,
      SatFOL rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.
   *)
  Axiom Proposition1 :
    forall gamma' phi rho,
      SatML gamma' rho (encoding phi) <->
      exists gamma, SatML gamma rho phi.

  
  Axiom enc_sat :
    forall gamma rho phi,
      SatML gamma rho (encoding phi) <->
      SatML gamma rho phi.
  

  Axiom rename_encoding :
    forall phi X Y,
      rename_var_set X Y (encoding phi) =
      (encoding (rename_var_set X Y phi)).
  
End Formulas.
