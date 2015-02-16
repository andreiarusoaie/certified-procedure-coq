Require Import List .
Require Import Classical.

Definition EmptySet_or_not {A : Type}(P : A -> Prop) : Prop :=
    (forall x, ~P x) \/ (exists x, P x).

Module Type Formulas.

  (* General *)
  Parameter State : Type .
  Parameter Model : Type .
  Parameter Term : Type .
  Parameter Var : Type .
  Parameter ModelEq : Model -> Model -> Prop.
  Definition Valuation : Type := Var -> Model .
  Axiom ModelEq_refl: forall m, ModelEq m m.

  (* FOL *)
  Parameter FOLFormula : Type .
  Parameter TrueFOL : FOLFormula .
  Parameter NotFOL : FOLFormula -> FOLFormula .
  Parameter OrFOL : FOLFormula -> FOLFormula -> FOLFormula .
  Definition AndFOL (phi phi' : FOLFormula) : FOLFormula :=
    NotFOL (OrFOL (NotFOL phi) (NotFOL phi')) .
  Definition FOLEquiv (phi phi' : FOLFormula) : FOLFormula :=
    (OrFOL (AndFOL phi phi') (AndFOL (NotFOL phi) (NotFOL phi'))) .
  
  Definition BigOrFOL (l : list FOLFormula) : FOLFormula :=
    fold_left OrFOL l (NotFOL TrueFOL) .
  Parameter SatFOL : Valuation -> FOLFormula -> Prop.

  Definition Sat (phi : FOLFormula) : Prop :=
    exists rho, SatFOL rho phi .

  Axiom SatFOLTrue: forall rho, SatFOL rho TrueFOL.
  Axiom SatFOLNot : forall rho phi,
                      SatFOL rho (NotFOL phi) <-> ~ SatFOL rho phi.

  
  (* ML *)
  Parameter MLFormula : Type .  
  Parameter MLFormula_eq : MLFormula -> MLFormula -> Prop .

  Axiom MLFormula_eq_refl : forall F, MLFormula_eq F F .
  Axiom MLFormula_eq_sym : forall F F' : MLFormula, MLFormula_eq F F' <-> MLFormula_eq F' F.
  
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .

  Parameter folenc : MLFormula -> FOLFormula .
  Parameter FolToML : FOLFormula -> MLFormula .
  (* Define SatFOL with model M *)
  Axiom simplEnc : forall phi rho,
                     SatFOL rho (FOLEquiv (folenc (FolToML (folenc phi))) (folenc phi)).
  Axiom SatFOL_equiv : forall phi phi' rho,
                         SatFOL rho (FOLEquiv phi phi') ->
                         SatFOL rho phi -> SatFOL rho phi'. 
  
  Parameter SatML : State -> Valuation -> MLFormula -> Prop .
  Parameter FreeVars : MLFormula -> list Var .

  Axiom SatMLExists :
    forall gamma rho X phi,
      SatML gamma rho (ExistsML X phi) <->
      exists rho', forall x, ~(In x X) -> (ModelEq (rho x) (rho' x) /\  SatML gamma rho' phi) .
  Axiom SatMLAnd :
    forall gamma rho phi phi',
      SatML gamma rho (AndML phi phi') <->
      SatML gamma rho phi /\ SatML gamma rho phi'.

  
  (* Paper *)
  Axiom Prop1 : forall varphi rho,
                  SatFOL rho (folenc varphi) <->
                  exists gamma, SatML gamma rho varphi .

  Axiom Prop3 : forall gamma rho phi Phi,
                  SatFOL rho Phi -> SatML gamma rho phi ->
                  SatML gamma rho (AndML (FolToML Phi) phi) .

End Formulas.


Module Soundness (F : Formulas).
  Require Import List .
  Require Import ZArith.
  Import F.

  Import ListNotations.
  
  Definition RLFormula := (MLFormula * MLFormula)%type .
  Notation "L => R" := (L, R) (at level 100).
  Notation lhs := fst .
  Notation rhs := snd .

  Lemma RL_decompose : forall F : RLFormula, F = ((lhs F) => (rhs F)).
  Proof.
    intros F.
    destruct F.
    simpl.
    reflexivity.
  Qed.
  
  Section RLSemantics.
    Definition TS_Spec := list RLFormula.
    Variable S : TS_Spec .

    Definition TS_S (gamma gamma' : State) : Prop :=
    exists phi phi' rho,
    In (phi => phi') S /\
    (SatML gamma rho phi) /\ (SatML gamma' rho phi').

    Notation "f =>S f'" := (TS_S f f') (at level 100).

    Definition Path := nat -> option State.
    
    Definition wfPath (tau : Path) : Prop :=
      (forall i j, i < j -> tau i = None -> tau j = None)
      /\
      (forall i,
         ((tau i <> None) /\ (tau (i + 1) <> None)) ->
       exists gamma gamma',
         tau i = Some gamma 
         /\ 
         tau (i+1) = Some gamma' /\ (gamma =>S gamma')).
         
    Definition isInfinite (tau : Path) : Prop :=
      forall i, tau i <> None.

    Definition Path_i (tau : Path) (i : nat) : Path :=
      fun j => tau (i+j).

    (*
    Definition insertBefore (gamma : State)
               (tau : Path) : Path :=
      fun i => if (beq_nat i 0) then Some gamma
               else tau (i - 1) .
     *)
    
    Definition startsFrom (tau : Path) (rho : Valuation) 
               (phi : MLFormula) : Prop :=
      exists gamma, tau 0 = Some gamma /\ SatML gamma rho phi .


    (* the input tau should be well-formed *)
    Definition SatRL (tau : Path) (rho : Valuation) 
               (F : RLFormula) : Prop :=
      (startsFrom tau rho (lhs F) 
        /\ 
        exists i gamma, tau i = Some gamma /\ SatML gamma rho (rhs F)) 
       \/ isInfinite tau .
    
    Definition SatTS_S (F : RLFormula) : Prop :=
      forall tau rho, wfPath tau -> startsFrom tau rho (lhs F) -> SatRL tau rho F .

    Definition sem_RL (F : RLFormula) : Path -> Prop :=
      fun tau => wfPath tau /\ exists rho, SatRL tau rho F .


    Lemma sem_RL_empty_or_not (F : RLFormula) :
      EmptySet_or_not (sem_RL F). 
    Proof.
      unfold EmptySet_or_not.
      assert ((forall x : Path, ~ sem_RL F x) \/ ~(forall x : Path, ~ sem_RL F x)) as [H | H].
      - apply classic.
      - tauto.
      - right.
        apply not_all_not_ex.
        exact H.
    Qed.
    
      
    Definition SDer (F : RLFormula) (f : RLFormula) : Prop :=
      MLFormula_eq (rhs F) (rhs f) /\
      (forall tau1 rho, wfPath tau1 ->
                        SatRL tau1 rho f -> 
                        exists tau, SatRL tau rho F /\ Path_i tau 1 = tau1).
    
    (* Delta : { D : list RLFormula | forall d, In d D -> SDer F d} *)
    Definition sem_SDerSet (Delta : list RLFormula)
               (F : RLFormula) : Path -> Prop :=
      fun tau => exists f, In f Delta /\ sem_RL f tau .

    Definition completeSDerSet (Delta : list RLFormula) 
               (F : RLFormula) : Prop :=
      (forall f, In f Delta -> SDer F f)
      /\
      forall f, 
        SDer F f -> forall tau, sem_RL f tau -> sem_SDerSet Delta F tau .
      
    Definition SDerivable (phi : MLFormula) : Prop :=
      exists gamma rho gamma', SatML gamma rho phi /\ (gamma =>S gamma') .


    Definition SynSDerML' (phi : MLFormula)
               (F : RLFormula)  : MLFormula :=
      (ExistsML (flat_map FreeVars [lhs F; rhs F])
              (AndML
                 (FolToML (folenc (AndML (lhs F) phi)))
                 (rhs F))) .
      
    Definition SynSDerML (phi : MLFormula) : list MLFormula := map (SynSDerML' phi) S .

    Definition SynSDerRL' (F : RLFormula) (phi1 : MLFormula) : RLFormula :=
      phi1 => rhs F .
    
    Definition SynSDerRL (F : RLFormula) : list RLFormula :=
      map (SynSDerRL' F) (SynSDerML (lhs F)) .

    
    (* Only 'half' of it *)
    Axiom Assumption_1 :
      forall phi phi_l phi_r x,
        In (phi_l => phi_r) S -> In x (FreeVars phi) -> ~ In x (FreeVars phi_l ++ FreeVars phi_r ++ nil).

    (* Modify given rho, s.t. rho(x) = rhoX(x), x in X *)
    Parameter extendVal : Valuation -> Valuation -> list Var -> Valuation .
    Axiom EV1 : forall rho rhoX x X, ~ (In x X) -> extendVal rho rhoX X x = rho x.
    Axiom SatExtend :
      forall gamma rho rhoX X phi,
        SatML gamma rhoX phi /\
        (forall x, In x (FreeVars phi) -> In x X) ->
        SatML gamma (extendVal rho rhoX X) phi.
    Axiom SatExtend' :
      forall gamma rho rhoX X phi,
        SatML gamma rho phi /\
        (forall x, In x (FreeVars phi) -> ~ In x X) ->
        SatML gamma (extendVal rho rhoX X) phi.
        
    

    Lemma CoverageStep :
      forall gamma gamma' rho phi,
        ((gamma =>S gamma') /\ SatML gamma rho phi) ->
        exists alpha,
          In alpha S /\ SatML gamma' rho (SynSDerML' phi alpha).
    Proof.
      intros gamma gamma' rho phi (H1 & H2).
      unfold TS_S in H1.

      destruct H1 as (phi_l & phi_r & rho' & H & H' & H'').
      exists (phi_l => phi_r).
      split.
      - assumption.
      - unfold SynSDerML'.
        simpl.
        rewrite -> SatMLExists.
        exists (extendVal rho rho' (FreeVars phi_l ++ FreeVars phi_r ++ [])).
        intros x H0.
        split.
        + assert (H1 : (extendVal rho rho' (FreeVars phi_l ++ FreeVars phi_r ++ []) x) = rho x).
          * apply EV1.
            assumption.
          * rewrite H1.
            apply ModelEq_refl.
        + clear x H0.
          assert (H0 : exists gamma0,  SatML gamma0 (extendVal rho rho' (FreeVars phi_l ++ FreeVars phi_r ++ [])) (FolToML (folenc (AndML phi_l phi)))).
          * apply Prop1.
           Admitted.
(*            rewrite simplEnc.
            apply Prop1.
            exists gamma.
            rewrite SatMLAnd.
            split.
            {
              apply SatExtend.
              split.
              - assumption.
              - intros x H0.
                apply in_app_iff.
                left.
                assumption.
            }
            apply SatExtend'.
            split.
            assumption.
            intros x H1.
            apply Assumption_1 with (phi := phi).
            assumption.
            assumption.
          * apply Prop1 in H0.
            rewrite simplEnc in H0.
            assert (H1 : SatML gamma' (extendVal rho rho' (FreeVars phi_l ++ FreeVars phi_r ++ [])) phi_r ).
            apply SatExtend.
            split.
            assumption.
            intros x H1.
            apply in_app_iff.
            right.
            apply in_app_iff.
            left.
            assumption.
            apply Prop3.
            split; assumption.
    Qed.
  *)        

    Lemma CoverageByDerivatives':
      forall tau rho phi,
        wfPath tau -> startsFrom tau rho phi
        -> 
        (forall i,
           i > 0
           ->
           (tau i <> None)
           ->
           exists phi_i gamma_i phi_i_1,
             tau i = Some gamma_i /\
             SatML gamma_i rho phi_i
             /\
             In phi_i (SynSDerML phi_i_1)).
    Proof.
      intros tau rho phi WF H i H' H''.
      assert (exists gamma, tau i = Some gamma).
      case_eq (tau i).
      intros s H0.
      exists s.
      reflexivity.
      intros H0.
      contradiction.

      revert H'.
      destruct i.
      - intros H'.
        contradict H'.
        omega.
      - intros _.
        induction i.
        unfold wfPath in WF.
        destruct WF as (WF1 & WF2).
        generalize (WF2 0).
        intros H1.
        clear WF2.
        assert (H2 : 0 < 1).
        omega.
        generalize (WF1 _ _ H2).
        intros.
        simpl in H1.
        case_eq (tau 0).
        intros s H4.
        assert (tau 0 <> None).
        congruence.
        clear H4.
        generalize (H1 (conj H5 H'')).
        intros (gamma & gamma' & H6 & H7 & H8).
        generalize (CoverageStep gamma gamma' rho phi).
        intros CS.
        unfold startsFrom in H.
        destruct H as (gamma'' & H9 & H10).
        assert (gamma = gamma'').
        congruence.
        subst gamma''.
        generalize (CS (conj H8 H10)).
        intros (alpha & H11 & H12).
        clear CS.
        exists (SynSDerML' phi alpha).
        exists gamma'.
        exists phi.
        split; trivial.
        split; trivial.
        unfold SynSDerML.
        rewrite in_map_iff.
        exists alpha.
        split; trivial.
        tauto.

        
        unfold wfPath in WF.
        destruct WF as (WF1 & WF2).
        assert (Datatypes.S i  <  Datatypes.S (Datatypes.S i)) as T.
        omega.
        generalize (WF1 _ _ T).
        intros H1.
        case_eq (Datatypes.S i) .
        intros i' Hi'.
        injection Hi'.
        intros.
        subst i'.
        clear Hi' T.
        destruct H0 as (gamma & H2).
        assert (tau (Datatypes.S i) <> None).
        tauto.
        generalize (IHi H0).
        clear IHi.
        intros IHi.
        assert (exists gamma0 : State, tau (Datatypes.S i) = Some gamma0) as Hg.
        case_eq (tau (Datatypes.S i)).
        intros s H3.
        exists s.
        trivial.
        intros.
        contradiction.
        generalize (IHi Hg).
        clear IHi.
        intros (phi_i & gamma_i & phi_i_1 & H3 & H4 & H5).
        generalize (WF2 (Datatypes.S i)).

        intros H6.
        rewrite plus_comm in H6.
        generalize (H6 (conj H0 H'')).
        clear H6.
        intros (gamma0 & gamma' & H6 & H7 & H8).
        generalize (CoverageStep gamma0 gamma' rho phi_i).
        intros CS.
        assert (gamma0 = gamma_i); try congruence; subst gamma_i.
        generalize (CS (conj H8 H4)).
        intros (alpha & H9 & H10).
        exists (SynSDerML' phi_i alpha).
        exists gamma'.
        exists phi_i.
        split; trivial.
        split; trivial.
        unfold SynSDerML.
        rewrite in_map_iff.
        exists alpha.
        split; trivial.
    Qed.
        
  End RLSemantics.
    
End Soundness.
