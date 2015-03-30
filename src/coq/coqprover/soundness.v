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
  Axiom Sat_dec : forall phi, SatML_Model_dec phi = true -> SatML_Model phi.

  (* Probably turn this into a Lemma *)
  Axiom impl_sat : forall gamma rho phi phi', SatML gamma rho phi /\ SatML_Model (ImpliesML phi phi') -> SatML gamma rho phi'.

  
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
  Axiom RLFormula_eq_dec_refl : forall x, RLFormula_eq_dec x x = left eq_refl.
  
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

    Axiom S_not_empty : S <> nil.
    
    Definition TS_S (gamma gamma' : State) : Prop :=
    exists phi phi' rho,
    In (phi => phi') S /\
    (SatML gamma rho phi) /\ (SatML gamma' rho phi').

    Notation "f =>S f'" := (TS_S f f') (at level 100).

    Definition total : Prop :=
      forall phi gamma rho,  SatML gamma rho phi ->
                             exists gamma' , gamma =>S gamma'.
    
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

    
    Definition startsFrom (tau : Path) (rho : Valuation) 
               (phi : MLFormula) : Prop :=
      exists gamma, tau 0 = Some gamma /\ SatML gamma rho phi .

    Definition terminating (gamma : State) :=
      forall gamma', not (gamma =>S gamma') .

    Definition complete (tau : Path) :=
      isInfinite tau \/
      exists i gamma, tau i = Some gamma /\ terminating gamma.
    
    (* the input tau should be well-formed *)
    Definition SatRL (tau : Path) (rho : Valuation) 
               (F : RLFormula) : Prop :=
      (startsFrom tau rho (lhs F) /\ complete tau
        /\ 
        exists i gamma, tau i = Some gamma /\ SatML gamma rho (rhs F)) 
       \/ isInfinite tau .
    
    Definition SatTS_S (F : RLFormula) : Prop :=
      forall tau rho, wfPath tau -> complete tau ->
                      startsFrom tau rho (lhs F) -> SatRL tau rho F .

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
    Axiom SDer_dec : forall phi, SDerivable_dec phi = true -> SDerivable phi.

    
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


    (* Section: Rstep -> |= G0 *)
    
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


    Fixpoint remove_first (x : RLFormula) (l : list RLFormula)
    : list RLFormula := 
      match l with
        | nil => nil
        | y :: tl => if RLFormula_eq_dec x y
                     then tl
                     else remove_first x tl
      end.

    (* Rstep G G' iff G' = step G *)
    Inductive Rstep : TS_Spec -> TS_Spec -> TS_Spec -> Prop :=
    | nil_case : forall G0, Rstep [] [] G0
    | base_case : forall G G' G0, forall phi phi',
                    In (phi => phi') G ->
                    SatML_Model (ImpliesML phi phi') ->
                    G' = remove_first (phi => phi') G ->
                    Rstep G G' G0
    | circ_case : forall G G' G0, forall phi phi' phic phic', 
                    In (phi => phi') G ->
                    In (phic => phic') G0 ->
                    SatML_Model (ImpliesML phi (ExistsML (FreeVars phic) phic)) ->
                    G' = (remove_first (phi => phi') G)
                           ++ (SynDerRL [phic => phic'] (phi => phi')) ->
                    Rstep G G' G0
    | deriv_case: forall G G' G0, forall phi phi',
                    In (phi => phi') G ->
                    SDerivable phi ->
                    G' = (remove_first (phi => phi') G)
                           ++ (SynDerRL S (phi => phi')) ->
                    Rstep G G' G0.

    
    Definition list_eq (S1 S2 : list RLFormula) :=
      incl S1 S2 /\ incl S2 S1.
    
    Inductive Rstep_star : TS_Spec -> TS_Spec
                           -> TS_Spec -> TS_Spec -> nat -> Prop :=
    | refl : forall G G' F G0 n, list_eq G G' -> Rstep_star G G' F G0 n
    | tranz : forall G G' F G0 n F' G'',
                Rstep G G'' G0 ->
                Rstep_star G'' G' F G0 n ->
                list_eq F' (F ++ G) -> Rstep_star G G' F' G0 (Datatypes.S n).

(*
    Fixpoint len (G G' F G0 : TS_Spec) (steps : Rstep_star G G' F G0) : nat :=
      match steps with
        | refl _ _ _ _ _ => 0
        | tranz _ _ _ _ _ _ _ _ _ => 1
      end.
 *)

    Lemma g_in_goals :
      forall G G' G'' F F0 G0 g n,
        Rstep G G' G0 ->
        Rstep_star G' G'' F0 G0 n ->
        list_eq F (F0 ++ G) ->
        In g F
        ->
        (In g G /\ ~ In g F0) \/ (In g F0).
    Proof.
      intros G G' G'' F F0 G0 g n H0 H1 H2 H3.
      unfold list_eq in H2.
      destruct H2 as (H2 & H2').
      unfold incl in H2.
      assert (((In g G /\ ~ In g F0) \/ (In g F0))
              \/
              ~ ((In g G /\ ~ In g F0) \/ (In g F0))).
      apply classic.
      destruct H.
      - assumption.
      - apply not_or_and in H.
        destruct H as (H & H').
        apply not_and_or in H.
        destruct H.
        + apply H2 in H3.
          apply in_app_or in H3.
          contradict H3.
          apply and_not_or.
          split; assumption.
        + right.
          apply NNPP in H.
          assumption.
    Qed.

    
    Lemma exists_G :
      forall n G F G0 g,
        G <> nil ->
        Rstep_star G nil F G0 (Datatypes.S n) ->
        In g F ->
        exists G' G'',
          Rstep G' G'' G0 /\ In g G' /\ ~ (In g G'') .
    Proof.
    Admitted.


    

    Lemma helper7 :
      forall G0 F n,
        Rstep_star (Delta S G0) nil F G0 n ->
        forall phi phi', In (phi => phi') F ->
                         (SatML_Model (ImpliesML phi phi')
                          \/
                          SDerivable phi).
    Proof.
      intros G0 F H phi phi' H'.
    Admitted.

    
            
    
    Lemma helper8' :
      forall F G0 n, G0 <> nil -> total ->
                     Rstep_star (Delta S G0) nil F G0 n ->
                     forall i tau rho phi phi',
                       (* wfPath tau *)
                       In (phi => phi') F ->
                       (exists gamma, tau i = Some gamma /\ terminating gamma) ->
                       startsFrom tau rho phi ->
                       SatRL tau rho (phi => phi').
    Proof.
      intros F G0 n NE T H.
      induction i using lt_wf_ind.
      intros tau rho phi phi' H01 H2 H3.

      Lemma exists_G' : forall F G0 n phi phi',
                         Rstep_star (Delta S G0) [] F G0 n ->
                         In (phi => phi') F ->
                         exists G G',
                           Rstep G G' G0 /\ In (phi => phi') G /\ ~ In (phi => phi') G'.
      Proof.
      Admitted.

      apply exists_G'  with (phi := phi) (phi' := phi') in H.
      destruct H as (G & (G' & (H4 & (H5 & H6)))).

      inversion H4.
      - contradict H5.
        rewrite <- H.
        apply in_nil.
      - subst G1 G'0 G2.
        case_eq G.
        + intros H8.
          rewrite H8 in H5.
          contradict H5.
        + rewrite H7 in H6.
          unfold remove_first in H6.
          intros r l H8.
          rewrite H8 in H6.
          fold remove_first in H6.
          case_eq (RLFormula_eq_dec (phi0 => phi'0) r).
          * intros e H9.
            rewrite H9 in H6.
            rewrite H8 in H5.
    Admitted.
            
  
      
    Lemma helper8 : forall F G0 n,
                      total -> G0 <> nil ->
                      Rstep_star (Delta S G0) nil F G0 n ->
                      forall tau rho phi phi',
                        (* wfPath tau *)
                        In (phi => phi') F ->
                        complete tau ->
                        startsFrom tau rho phi ->
                        SatRL tau rho (phi => phi').
      Proof.
      intros F G0 n T H' H tau rho phi phi' H0 H1 H2.
      unfold complete in H1.
      destruct H1 as [H1 | H1].
      - unfold SatRL. right. exact H1.
      - destruct H1 as (i & (gamma & (H1 & H3))).
        apply helper8' with (F := F) (G0 := G0) (i := i) (n := n).
        + exact H'.
        + exact T.
        + exact H.
        + exact H0.
        + auto. exists gamma. split; assumption.
        + exact H2.
    Qed.
         
                 
          
                         
                  
       
      Lemma star_soundness :
        forall G0 F n,
          total -> incl G0 F ->
          Rstep_star (Delta S G0) nil F G0 n -> SatTS G0.
      Proof.
        intros G0 F n T I H.
        unfold SatTS.
        intros alpha H'.
        unfold SatTS_S.
        intros tau rho H0 H1.
        case_eq G0.
        - intros H2.
          rewrite H2 in H'.
          contradict H'.
        - destruct alpha.
          simpl.
          intros r l H2 H3.
          apply helper8 with (F := F) (G0 := G0) (n := n).
          + exact T.
          + rewrite H2.
            congruence.
          + exact H.
          + unfold incl in I.
            apply I.
            exact H'.
          + exact H1.
          + exact H3.
      Qed.




    
    (* Section prove -> Rstep *)

    Fixpoint step (G G0 : TS_Spec) : option TS_Spec :=
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


    (* the first arg of prove is (Delta_S G0)!!! *)
    Fixpoint prove (G GF : TS_Spec) (n : nat) (G0 : TS_Spec) : (Result * TS_Spec) :=
      match n with
        | 0 => (failure, GF)
        | Datatypes.S n' =>
          match step G G0 with
            | None => (failure, GF ++ G)
            | Some G' => match G' with
                           | nil => (success, GF ++ G)
                           | _ => prove G' (GF ++ G) n' G0
                         end
          end
      end.


    Lemma helper0 : forall c phi G0, chooseCirc G0 phi = Some c -> In c G0.
    Proof.
      intros c phi G0 H.
      unfold chooseCirc in H.
      induction G0.
      - inversion H.
      - fold chooseCirc in H.
        fold chooseCirc in IHG0.
        destruct a.
        case_eq (SatML_Model_dec (ImpliesML phi (ExistsML (FreeVars m) m))).
        + intros H'.
          rewrite H' in H.
          inversion H.
          simpl.
          left.
          reflexivity.
        + intros H'.
          rewrite H' in H.
          simpl.
          right.
          apply IHG0.
          assumption.
    Qed.
        
      
    Lemma helper1 : forall phic phic' phi G0, chooseCirc G0 phi = Some (phic => phic') -> SatML_Model (ImpliesML phi (ExistsML (FreeVars phic) phic)) .
    Proof.
      intros phic phic' phi G0 H.
      unfold chooseCirc in H.
      induction G0.
      - inversion H.
      - fold chooseCirc in H.
        fold chooseCirc in IHG0.
        destruct a.
        case_eq (SatML_Model_dec (ImpliesML phi (ExistsML (FreeVars m) m))).
        + intros H'.
          rewrite H' in H.
          inversion H.
          rewrite <- H1.
          apply Sat_dec.
          assumption.
        + intros H'.
          rewrite H' in H.
          apply IHG0.
          assumption.
    Qed.
    

    Lemma step_Rstep : forall G G' G0, Some G' = step G G0 -> Rstep G G' G0.
    Proof.
      intros G G' G0 H.
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
          case_eq (SatML_Model_dec (ImpliesML m m0)); intros H0; rewrite H0 in H.
          * apply base_case with (phi := m) (phi' := m0).
            simpl.
            left.
            reflexivity.
            apply Sat_dec.
            assumption.
            inversion H.
            simpl.
            rewrite RLFormula_eq_dec_refl.
            reflexivity.
          * case_eq (chooseCirc G0 m).
            destruct r.
            intros C.
            rewrite C in H.
            inversion H.
            contradict H2.
            apply app_cons_not_nil.
            
            intros H1.
            rewrite H1 in H.
            case_eq (SDerivable_dec m) .
            intros H2.
            rewrite H2 in H.
            inversion H.
            contradict H4.
            unfold SynDerRL.
            simpl.
            case_eq S.
            intros S0.
            simpl.
            rewrite app_nil_r.
            contradict S0.
            apply S_not_empty.
            intros r l0 H3.
            apply app_cons_not_nil.
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
            simpl.
            rewrite RLFormula_eq_dec_refl.
            reflexivity.
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
            apply helper1 with (phic' := m4) (G0 := G0).
            assumption.
            rewrite H2 in H.
            inversion H.
            rewrite <- H'.
            rewrite H4.
            simpl.
            rewrite RLFormula_eq_dec_refl.
            reflexivity.
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
            simpl.
            rewrite RLFormula_eq_dec_refl.
            reflexivity.
            intros H3.
            rewrite H3 in H.
            contradict H.
            congruence.
    Qed.

    Lemma incl_G_F : forall n G F0 G0 F,
                     prove G F0 n G0 = (success, F)
                     ->
                     incl (F0 ++ G) F.
    Proof.
      induction n.
      - intros G F0 G0 F H.
        simpl in H.
        discriminate H.
      - intros G F0 G0 F H.
        unfold prove in H.
        fold prove in H.
        case_eq (step G G0).
        + intros t H0.
          rewrite H0 in H.
          case_eq t.
          * intros H1.
            rewrite H1 in H.
            inversion H.
            apply incl_refl.
          * intros r l H1.
            rewrite H1 in H.
            apply IHn in H.
            rewrite <- H1 in H.
            unfold incl in H.
            unfold incl.
            intros a H2.
            apply H.
            apply in_app_iff.
            left.
            apply H2.
        + intros H'.
          rewrite H' in H.
          discriminate H.
    Qed.


    Lemma prove_Rstep_star_gen :
      forall n G0 G F0 F,
        incl G F ->
        prove G F0 n G0 = (success, F) ->
        Rstep_star G nil F G0 n.
    Proof.
      induction n.
      - intros G0 G F0 F H' H.
        unfold prove in H.
        discriminate H.
      - intros G0 G F0 F H' H.
        unfold prove in H.
        fold prove in H.
        case_eq (step G G0).
        + intros t H0.
          rewrite H0 in H.
          case_eq t.
          * intros H1.
            rewrite H1 in H.
            injection H.
            intros H2.
            subst t.
            eapply tranz.
            apply step_Rstep.
            instantiate (1 := []).
            (* symmetry. *)
            congruence.
            apply refl.
            unfold list_eq.
            split; apply incl_refl.
            rewrite <- H2.
            instantiate (1 := F0).
            unfold list_eq.
            split;
            apply incl_refl.
          * intros r l H1.
            subst t.
            apply IHn in H.
            eapply tranz.
            apply step_Rstep.
            instantiate (1 := (r :: l)).
            congruence.
            instantiate (1 := F).
            exact H.
            unfold list_eq.
            split.
            apply incl_appl.
            apply incl_refl.
            apply incl_app.
            apply incl_refl.
            exact H'.
            apply incl_G_F in H.
            unfold incl in H.
            unfold incl.
            intros a H1.
            apply H.
            apply in_app_iff.
            right.
            apply H1.
        + intros H0.
          rewrite H0 in H.
          discriminate H.
    Qed.
    
    
    Lemma prove_Rstep_star :
      forall n G0 F,
        prove (Delta S G0) G0 n G0 = (success, F) ->
        Rstep_star (Delta S G0) nil F G0 n.
    Proof.
      intros n G0 F H.
      apply prove_Rstep_star_gen
      with (n := n) (F0 := G0).
      assert (H' : incl (G0 ++ (Delta S G0)) F).
      - apply incl_G_F with (n := n) (G0 := G0).
        exact H.
      - unfold incl in H'.
        unfold incl.
        intros a H0.
        apply H'.
        apply in_app_iff.
        right.
        exact H0.
      - exact H.
    Qed.


 

    (* Main theorem - maybe? *)
    Theorem soundness : forall n G0 F,
                          total ->
                          prove (Delta S G0) G0 n G0 = (success, F) ->
                          SatTS G0.
    Proof.
      intros n G0 F T H.
      eapply star_soundness.
      - exact T.
      - instantiate (1 := F).
        assert (H' : incl (G0 ++ (Delta S G0)) F).
        + apply incl_G_F with (n := n) (G0 := G0).
          exact H.
        + unfold incl in H'.
          unfold incl.
          intros a H''.
          apply H'.
          apply in_app_iff.
          left.
          exact H''.
      - eapply prove_Rstep_star.
        instantiate (1 := n).
        exact H.
    Qed.


    
  End RLSemantics.


  
End Soundness.
