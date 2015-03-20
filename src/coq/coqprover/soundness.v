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
  Axiom FOLEquiv_comm : forall phi phi' rho,
                          SatFOL rho (FOLEquiv phi phi') <->
                          SatFOL rho (FOLEquiv phi' phi).
  
  Axiom SatFOL_equiv : forall phi phi' rho,
                         SatFOL rho phi ->
                         SatFOL rho (FOLEquiv phi phi') ->
                         SatFOL rho phi'. 

  
  (* ML *)
  Parameter MLFormula : Type .  
  Parameter MLFormula_eq : MLFormula -> MLFormula -> Prop .

  Axiom MLFormula_eq_refl : forall F, MLFormula_eq F F .
  Axiom MLFormula_eq_sym : forall F F' : MLFormula, MLFormula_eq F F' <-> MLFormula_eq F' F.
  
  Parameter AndML : MLFormula -> MLFormula -> MLFormula .
  Parameter NotML : MLFormula -> MLFormula.
  Parameter ExistsML : list Var -> MLFormula -> MLFormula .
  Definition ImpliesML (phi phi' : MLFormula) : MLFormula :=
    NotML (AndML phi (NotML phi')) .

          
  Parameter folenc : MLFormula -> FOLFormula .
  Parameter FolToML : FOLFormula -> MLFormula .
  (* Define SatFOL with model M *)
  Axiom simplEnc : forall phi rho,
                     SatFOL rho (FOLEquiv (folenc (FolToML (folenc phi))) (folenc phi)).
  
  Parameter SatML : State -> Valuation -> MLFormula -> Prop .
  Parameter SatML_dec : State -> Valuation -> MLFormula -> bool.

  Parameter FreeVars : MLFormula -> list Var .

  Axiom SatMLExists :
    forall gamma rho X phi,
      SatML gamma rho (ExistsML X phi) <->
      exists rho', forall x, ~(In x X) ->
                             (ModelEq (rho x) (rho' x) /\
                              SatML gamma rho' phi) .
  Axiom SatMLAnd :
    forall gamma rho phi phi',
      SatML gamma rho (AndML phi phi') <->
      SatML gamma rho phi /\ SatML gamma rho phi'.

  Definition SatML_Model (phi : MLFormula) : Prop :=
    forall gamma rho, SatML gamma rho phi.
  Parameter SatML_Model_dec : MLFormula -> bool .
  
  (* Paper *)
  Axiom Prop1 : forall varphi rho,
                  SatFOL rho (folenc varphi) <->
                  exists gamma, SatML gamma rho varphi .

  Axiom Prop3 : forall gamma rho phi Phi,
                  SatFOL rho Phi -> SatML gamma rho phi ->
                  SatML gamma rho (AndML (FolToML Phi) phi) .


  (* Additional axioms *)
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

  Parameter RLFormula_eq_dec : forall x y : RLFormula, {x = y} + {x <> y} .
  
  Lemma RL_decompose : forall F : RLFormula, F = ((lhs F) => (rhs F)).
  Proof.
    intros F.
    destruct F.
    simpl.
    reflexivity.
  Qed.

  Definition subset (A B : list RLFormula) : Prop :=
    forall a, In a A -> In a B.
  
  
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

    Definition terminating (gamma : State) :=
      forall gamma', not (gamma =>S gamma') .

    Definition complete (tau : Path) :=
      exists i gamma, tau i = Some gamma /\ terminating gamma.
    
    (* the input tau should be well-formed *)
    Definition SatRL (tau : Path) (rho : Valuation) 
               (F : RLFormula) : Prop :=
      (startsFrom tau rho (lhs F) /\ complete tau
        /\ 
        exists i gamma, tau i = Some gamma /\ SatML gamma rho (rhs F)) 
       \/ isInfinite tau .
    
    Definition SatTS_S (F : RLFormula) : Prop :=
      forall tau rho, wfPath tau -> (complete tau \/ isInfinite tau)
                      -> startsFrom tau rho (lhs F) -> SatRL tau rho F .

    Definition SatTS (G : TS_Spec) : Prop :=
      forall F, In F G -> SatTS_S F.
    
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

    Parameter SDerivable_dec : MLFormula -> bool .

    (*
    Axiom SDerivable_dec_impl : forall phi, SDerivable_dec phi = true -> SDerivable phi.
    *)

    Definition SynDerML' (phi : MLFormula)
               (F : RLFormula)  : MLFormula :=
      (ExistsML (flat_map FreeVars [lhs F; rhs F])
              (AndML
                 (FolToML (folenc (AndML (lhs F) phi)))
                 (rhs F))) .
    Definition SynDerRL' (F : RLFormula) (phi1 : MLFormula) : RLFormula :=
      phi1 => rhs F .

    
    Definition SynDerML (phi : MLFormula)
               (S' : TS_Spec) : list MLFormula :=
      map (SynDerML' phi) S'.
    
    Definition SynDerRL (S' : TS_Spec) (F : RLFormula) : list RLFormula :=
      map (SynDerRL' F) (SynDerML (lhs F) S').
    
    Definition SynSDerML (phi : MLFormula) : list MLFormula := map (SynDerML' phi) S .
    
    Definition SynSDerRL (F : RLFormula) : list RLFormula :=
      map (SynDerRL' F) (SynDerML (lhs F) S) .
    
    Fixpoint Delta (S' G' : TS_Spec) : TS_Spec :=
      match G' with
        | nil => nil
        | alpha :: G'' => (SynDerRL S' alpha) ++ (Delta S' G'')
      end.

    (* Some axioms needed in the proof *)
    
    (* Only 'half' of it *)
    Axiom Assumption_1 :
      forall phi phi_l phi_r x,
        In (phi_l => phi_r) S -> In x (FreeVars phi) -> ~ In x (FreeVars phi_l ++ FreeVars phi_r ++ nil).

        
    

    Lemma CoverageStep :
      forall gamma gamma' rho phi,
        ((gamma =>S gamma') /\ SatML gamma rho phi) ->
        exists alpha,
          In alpha S /\ SatML gamma' rho (SynDerML' phi alpha).
    Proof.
      intros gamma gamma' rho phi (H1 & H2).
      unfold TS_S in H1.
      destruct H1 as (phi_l & phi_r & rho' & H & H' & H'').
      exists (phi_l => phi_r).
      split.
      - assumption.
      - unfold SynDerML'.
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
            apply SatFOL_equiv with (phi := (folenc (AndML phi_l phi))).
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
            apply FOLEquiv_comm.
            apply simplEnc.
          * apply Prop1 in H0.
            assert (H0' : SatFOL (extendVal rho rho' (FreeVars phi_l ++ FreeVars phi_r ++ []))
                                 (folenc (AndML phi_l phi))).
            apply SatFOL_equiv with (phi := (folenc (FolToML (folenc (AndML phi_l phi))))).
            assumption.
            apply simplEnc.
            clear H0.
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
            assumption.
            assumption.
    Qed.
    
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
        exists (SynDerML' phi alpha).
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
        exists (SynDerML' phi_i alpha).
        exists gamma'.
        exists phi_i.
        split; trivial.
        split; trivial.
        unfold SynSDerML.
        rewrite in_map_iff.
        exists alpha.
        split; trivial.
    Qed.


    (* PROVE *)
    Variable G0 : TS_Spec.
    Inductive Result : Type := success | failure.

    Fixpoint chooseCirc (G0 : TS_Spec)
               (phi : MLFormula) : option RLFormula :=
      match G0 with
        | nil => None
        | (phi_c => phi_c') :: G0' =>
          if SatML_Model_dec
               (ImpliesML phi
                          (ExistsML (FreeVars phi_c) phi_c))
          then Some (phi_c => phi_c')
          else chooseCirc G0' phi
      end.

      

    
    Inductive Rstep : TS_Spec -> TS_Spec -> Prop :=
    | nil_case : Rstep [] []
    | base_case : forall G G', forall phi phi',
                    In (phi => phi') G ->
                    SatML_Model (ImpliesML phi phi') ->
                    G' = remove RLFormula_eq_dec (phi => phi') G ->
                    Rstep G G'
    | circ_case : forall G G', forall phi phi' phic phic', 
                    In (phi => phi') G ->
                    In (phic => phic') G0 ->
                    SatML_Model (ImpliesML phi (ExistsML (FreeVars phic) phic)) ->
                    G' = (remove RLFormula_eq_dec (phi => phi') G)
                           ++ (SynDerRL [phic => phic'] (phi => phi')) ->
                    Rstep G G'
    | deriv_case: forall G G', forall phi phi',
                    In (phi => phi') G ->
                    SDerivable phi ->
                    G' = (remove RLFormula_eq_dec (phi => phi') G)
                           ++ (SynDerRL S (phi => phi')) ->
                    Rstep G G'.
                                                                   
    Inductive Rstep_star : TS_Spec -> TS_Spec -> TS_Spec -> Prop :=
    | refl : forall G G', G = G' -> Rstep_star G G' G'
    | tranz : forall G G' F, forall G'',
                Rstep G G'' -> Rstep_star G'' G' F -> Rstep_star G G' (F ++ G).


    
    Lemma soundness : forall F,
                        Rstep_star (Delta S G0) nil F -> SatTS G0.
    Admitted.

    Lemma helper7 : forall F, Rstep_star (Delta S G0) nil F ->
                      forall phi phi', In (phi => phi') F ->
                             (SatML_Model (ImpliesML phi phi')
                                 \/
                             SDerivable phi).
    Admitted.

    Lemma helper8 : forall F, Rstep_star (Delta S G0) nil F ->
                              forall tau rho phi phi',
                                In (phi => phi') F ->
                                ~ isInfinite tau -> complete tau ->
                                startsFrom tau rho phi ->
                                SatRL tau rho (phi => phi').
    Admitted.

    

    Fixpoint step (G : TS_Spec) : option TS_Spec :=
      match G with
        | nil => Some G
        | (phi => phi') :: G' =>
          if (SatML_Model_dec (ImpliesML phi phi'))
          then Some G'
          else
            match chooseCirc G0 phi with
              | Some (phi_c => phi_c') =>
                Some (G' ++ (SynDerRL [phi_c => phi_c'] (phi => phi')))
              | None => if SDerivable_dec phi
                        then Some (G' ++ (SynDerRL S (phi => phi')))
                        else None
            end
      end.


    (* should be called only with prove(Delta_S G0)!!! *)
    Fixpoint prove (G GF : TS_Spec) (n : nat) : (Result * TS_Spec) :=
      match n with
        | 0 => (failure, GF)
        | Datatypes.S n' =>
          match step G with
            | None => (failure, GF)
            | Some G' => match G' with
                           | nil => (success, GF)
                           | _ => prove G' (GF ++ G) n'
                         end
          end
      end.

    Axiom Sat_dec : forall phi, SatML_Model_dec phi = true -> SatML_Model phi.
    Axiom SDer_dec : forall phi, SDerivable_dec phi = true -> SDerivable phi.

    Lemma helper0 : forall c phi, chooseCirc G0 phi = Some c -> In c G0.
    Admitted.
    Lemma helper1 : forall phic phic' phi, chooseCirc G0 phi = Some (phic => phic') -> SatML_Model (ImpliesML phi (ExistsML (FreeVars phic) phic)) .
    Admitted.
    

    Lemma step_Rstep : forall G G', Some G' = step G -> Rstep G G' .
    Proof.
      intros G G' H.
      case_eq G'.
      - intros H'.
        rewrite H' in H.
        unfold step in H.
        case_eq G.
        + intros H''.
          rewrite H'' in H.
          apply nil_case.
        + destruct r.
          intros l H''.
          rewrite H'' in H.
          case_eq (SatML_Model_dec (ImpliesML m m0)).
          * intros H0.
            rewrite H0 in H.
            apply base_case with (phi := m) (phi' := m0).
            simpl.
            left.
            reflexivity.
            apply Sat_dec.
            assumption.
            inversion H.
            simpl.
            admit.
            
          * intros H0.
            rewrite H0 in H.
            case_eq (chooseCirc G0 m).
            destruct r.
            intros C.
            rewrite C in H.
            inversion H.
            contradict H2.
            admit.
            
            intros H1.
            rewrite H1 in H.
            case_eq (SDerivable_dec m) .
            intros H2.
            rewrite H2 in H.
            inversion H.
            contradict H4.
            admit.

            intros H2.
            rewrite H2 in H.
            contradict H.
            congruence.
      - destruct r.
        intros l H'.
        unfold step in H.
        case_eq G.
        intros H0.
        rewrite H0 in H.
        + inversion H.
          contradict H'.
          rewrite H2.
          congruence.
        + destruct r.
          intros l0 H0.
          rewrite H0 in H.
          case_eq (SatML_Model_dec (ImpliesML m1 m2)).
          * intros H1.
            rewrite H1 in H.
            apply base_case with (phi := m1) (phi' := m2).
            simpl.
            left.
            reflexivity.
            apply Sat_dec.
            assumption.
            inversion H.
            rewrite <- H3.
            rewrite H'.
            admit.
            
          * intros H1.
            rewrite H1 in H.
            case_eq (chooseCirc G0 m1).
            destruct r.
            intros H2.
            apply circ_case with (phi := m1) (phi' := m2) (phic := m3) (phic' := m4).
            simpl.
            left.
            reflexivity.
            apply helper0 with (phi := m1).
            assumption.
            apply helper1 with (phic' := m4).
            assumption.
            rewrite H2 in H.
            inversion H.
            rewrite <- H'.
            rewrite H4.
            admit.

            intros H2.
            rewrite H2 in H.
            case_eq (SDerivable_dec m1).
            intros H3.
            rewrite H3 in H.
            inversion H.
            apply deriv_case with (phi := m1) (phi' := m2).
            simpl.
            left.
            reflexivity.
            apply SDer_dec.
            assumption.
            rewrite <- H'.
            rewrite H5.
            admit.

            intros H3.
            rewrite H3 in H.
            contradict H.
            congruence.
    Qed.

    Lemma non_empty_der : forall G, G <> nil -> Delta S G <> [] .
    Admitted.
      
    Lemma prove_Rstep_star : forall n F,
                               G0 <> nil ->
                               prove (Delta S G0) G0 n = (success, F) ->
                               Rstep_star (Delta S G0) nil F.
    Admitted.

  End RLSemantics.

End Soundness.
