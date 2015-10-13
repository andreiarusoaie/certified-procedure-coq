Require Import formula.
Require Import util.
Require Import rldefs.
Require Import definition.
Require Import List.
Require Import ListSet.
Require Import Classical.
Require Arith.
Require Import Omega.

Module Type Soundness
       (U : Utils) (F : Formulas)
       (R : RL F U) (Def : Definitions U F R) .
  Import U F R Def.
  Import ListNotations.
  Import Wf_nat.

  (* G0 *)
  Variable G0 : list RLFormula.
  
  
  (* Section procedure *)
  Inductive step (G G': list RLFormula)
            (g : RLFormula) : Prop :=
  | impl :
      In g G ->
      ValidML (ImpliesML (lhs g) (rhs g)) ->
      G' = remove RLFormula_eq_dec g G ->
      step G G' g
  | circ :
      forall c c',
        In g G -> In c G0 ->
        RL_alpha_equiv c c' -> disjoint_vars_RL g c' ->
        ValidML (ImpliesML (lhs g) (EClos (lhs c))) ->
        G' = (remove RLFormula_eq_dec g G) ++ (SynDerRL [c'] g) ->
        step G G' g
  | der :
      forall S', 
        In g G -> SDerivable (lhs g) -> 
        RL_alpha_equiv_S S S' -> disjoint_vars_rules S' g ->
        G' = (remove RLFormula_eq_dec g G) ++ (SynDerRL S' g) ->
      step G G' g.
  
  Inductive steps : list RLFormula -> Prop :=
    | base : steps []
    | tranz : forall G G' g,
                step G G' g ->
                steps G' ->
                steps G.


  (* Definition: g in F *)
  Inductive inF (g : RLFormula) : Prop :=
  | init : In g G0 -> inF g
  | in_step : forall G G',
                step G G' g ->
                (forall g', In g' G' -> inF g') ->
                inF g.
  

      
    
  (* Coverage one step *)
  Lemma cover_step :
    forall gamma gamma' rho phi S,
      (forall F, In F S -> disjoint_set_RL F (getFreeVars phi)) ->
      (forall F, In F G0 -> wfFormula F) ->
      (forall F, In F S -> wfFormula F) ->
      (TS S gamma gamma') ->
      SatML gamma rho phi ->
      exists alpha phi',
        In alpha S /\ phi' = SynDerML' phi alpha /\ SatML gamma' rho phi'.
  Proof.
    intros gamma gamma' rho phi S D WFF1 WFF2 H H'.
    unfold TS in H.
    destruct H as (phi_l & phi_r & rho' & H0 & H1 & H2).
    exists (phi_l => phi_r), (SynDerML' phi (phi_l => phi_r)).
    repeat split; trivial.
    unfold SynDerML'.
    apply SatML_Exists.
    set (vars := (FreeVars [phi_l; phi_r])).
    simpl in *.
    exists (modify_val_on_set rho rho' vars).
    split.
    - intros v V.
      symmetry.
      apply modify_not_in; trivial.
    - apply SatML_And.
      split.
      + apply Proposition1.
        exists gamma.
        apply SatML_And.
        split.
        * apply modify_Sat1; trivial.
          subst vars.
          apply incl_appl.
          apply incl_refl.
        * apply modify_Sat2; trivial.
          intros x Hx.
          subst vars.
          apply D in H0.
          unfold disjoint_set_RL in H0.
          apply H0 in Hx.
          simpl in *.
          trivial.
      + apply modify_Sat1; trivial.
        subst vars.
        unfold FreeVars.
        apply incl_appr.
        rewrite app_nil_r.
        apply incl_refl.
  Qed.

  (* helper *)
  Lemma valid_impl :
    forall gamma rho phi phi',
      ValidML (ImpliesML phi phi') ->
      SatML gamma rho phi ->
      SatML gamma rho phi'.
  Proof.
    intros gamma rho phi phi' H H'.
    unfold ValidML in H.
    unfold ImpliesML in H.
    assert (H0 : SatML gamma rho (NotML (AndML phi (NotML phi')))); trivial.
    clear H.
    rewrite SatML_Not in H0.
    rewrite SatML_And in H0.
    apply not_and_or in H0.
    destruct H0 as [H0 | H0].
    - contradiction.
    - rewrite SatML_Not in H0.
      apply NNPP; trivial.
  Qed.
    

  (* Important: implication or S-derivable *)
  Lemma impl_or_der :
    forall phi phi',
      total -> 
      inF (phi => phi') ->
      (forall p p', In (p => p') G0 -> SDerivable p) ->
      (exists gamma rho, SatML gamma rho phi) ->
      ValidML (ImpliesML phi phi') \/ SDerivable phi .
  Proof.
    intros phi phi' T H0 H' H1.
    inversion H0.
    - right.
      apply H' with (p' := phi'); trivial.
    - inversion H; simpl in H3.
      + left; trivial.
      + right.
        simpl in *.
        destruct c, c'.
        simpl in *.
        destruct H1 as (gamma & rho & H1).
        apply valid_impl with (phi := phi) (gamma := gamma) (rho := rho) (phi' := (EClos m)) in H7; trivial.
        unfold EClos in H7.
        apply SatML_Exists in H7.
        destruct H7 as (rho' & H9 & H10).
        apply H' in H4.
        unfold total in T.
        apply T with (gamma := gamma) (rho := rho') in H4; trivial.
        destruct H4 as (gamma' & H4).
        unfold SDerivable.
        exists gamma, rho, gamma'.
        split; trivial.
      + right; trivial.
  Qed.


  (* helper *)
  Lemma shift_index :
    forall tau j k,
      Path_i tau j k = tau (k + j).
  Proof.
    intros tau j k.
    unfold Path_i, GPath_i.
    rewrite plus_comm; trivial.
  Qed.
                         


  (* helper *)
  Lemma wf_subpath : forall tau j,
                       wfPath tau -> wfPath (Path_i tau j) .
  Proof.
    intros tau j H.
    unfold wfPath, wfGPath in *.
    destruct H as (H & H').
    split.
    - intros i j0 H0 H1.
      rewrite shift_index in *.
      apply H with (i := (i + j)); trivial.
      omega.
    - intros i H0.
      do 2 rewrite shift_index in *.
      rewrite <- plus_assoc, (plus_comm 1), plus_assoc in *.
      apply H'; trivial.
  Qed.
  

  (* helper *)
  Lemma first_step_gamma :
    forall tau n gamma,
      wfPath tau ->
      completeN tau (Datatypes.S n) ->
      tau 0 = Some gamma ->
      exists gamma', tau 1 = Some gamma'.
  Proof.
    intros tau n gamma WF C H.
    case_eq n.
    - intros n0; subst n.
      unfold complete in C.
      destruct C as (gamma' & H0 & H1).
      auto. exists gamma'; trivial.
    - intros n0 H0.
      unfold wfPath, wfGPath in WF.
      destruct WF as (WF & WF').
      case_eq (tau 1).
      + intros s H2.
        exists s; trivial.
      + intros H1.
        subst n.
        contradict C.
        unfold complete.
        unfold not.
        intros H0.
        destruct H0 as (gamma0 & H0 & H2).
        apply WF with
        (j := (Datatypes.S (Datatypes.S n0))) in H1.
        * rewrite H1 in H0.
          inversion H0.
        * omega.
  Qed.

  (* helper *)
  Lemma one_step_less :
    forall tau n n0,
      wfPath tau ->
      completeN tau (Datatypes.S n) ->
      completeN (Path_i tau 1) n0 ->
      n0 = n.
  Proof.
    intros tau n n0 WF H H'.
    unfold complete in *.
    destruct H as(gamma & H0 & H1).
    destruct H' as(gamma' & H0' & H1').
    unfold wfPath, wfGPath in WF.
    destruct WF as (WF & WF').
    rewrite shift_index in H0'.
    assert (Sn : n + 1 = Datatypes.S n); try omega.
    assert (Sn' : n0 + 1 = Datatypes.S n0); try omega.
    apply NNPP.
    intros H.
    apply not_eq in H.
    destruct H as [H | H].
    - apply plus_lt_compat_r with (p := 1) in H.
      assert (H2: tau ((n0 + 1) + 1) = None).
      + apply NNPP.
        intros H2.
        assert (H3 : tau (n0 + 1) <> None /\ tau ((n0 + 1) + 1) <> None).
        * split.
          intros H3. rewrite H3 in H0'. inversion H0'.
          exact H2.
         * apply WF' in H3.
           destruct H3 as (e & e' & H4 & H5 & H6).
           rewrite H0' in H4.
           inversion H4. clear H4.
           unfold terminating in H1'.
           subst gamma'.
           contradict H6.
           apply H1'.
       + rewrite Sn in H.
         apply lt_n_Sm_le in H.
         apply plus_le_compat_r with (p := 1) in H.
         apply le_lt_or_eq in H.
         destruct H as [H | H].
         * apply WF in H.
           rewrite Sn in H.
           rewrite H in H0.
           inversion H0.
           exact H2.
         * rewrite H in H2.
           rewrite Sn in H2.
           rewrite H2 in H0.
           inversion H0.
     - apply plus_lt_compat_r with (p := 1) in H.
       assert (H2: tau ((n + 1) + 1) = None).
       + apply NNPP.
         intros H2.
         assert (H3 : tau (n + 1) <> None /\ tau ((n + 1) + 1) <> None).
         * split.
           intros H3. rewrite Sn in H3. rewrite H3 in H0. inversion H0.
           exact H2.
         * apply WF' in H3.
           destruct H3 as (e & e' & H4 & H5 & H6).
           rewrite Sn in H4.
           rewrite H0 in H4.
           inversion H4. clear H4.
           unfold terminating in H1.
           subst gamma.
           contradict H6.
           apply H1.
       + rewrite Sn' in H.
         apply lt_n_Sm_le in H.
         apply plus_le_compat_r with (p := 1) in H.
         apply le_lt_or_eq in H.
         destruct H as [H | H].
         * apply WF in H.
           rewrite H in H0'.
           inversion H0'.
           exact H2.
         * rewrite H in H2.
           rewrite H2 in H0'.
           inversion H0'.
   Qed.


  (* helper *)
  Lemma is_infinite :
    forall tau i,
      wfPath tau ->
      isInfinite (Path_i tau i) -> isInfinite tau.
  Proof.
    intros tau i H H'.
    unfold isInfinite, isInfiniteGPath in *.
    intros j.
    unfold wfPath, wfGPath in H.
    destruct H as (H & H'').
    assert (C : (i < j) \/ ~(i < j)).
    apply classic.
    destruct C as [C | C].
    - rewrite <- le_plus_minus_r with (n := i) (m := j); try omega.
      rewrite plus_comm.
      rewrite <- shift_index.
      apply H'.
    - unfold not in *.
      intros.
      apply H' with (i0 := 0).
      rewrite shift_index.
      simpl.
      assert (C' : (i = j) \/ ~ (i = j)).
      apply classic.
      destruct C' as [C' | C'].
      + subst; trivial.
      + eapply H.
        instantiate (1 := j).
        omega.
        trivial.
  Qed.


  
  (* helper: subpath satisfies F -> path satisfies F *)
  Lemma one_step :
    forall tau rho phi phi',
      wfPath tau ->
      startsFrom tau rho phi ->
      (exists phi1,
         In phi1 (SynDerML phi S) /\
         SatRL (Path_i tau 1) rho (phi1 => phi')) ->
      SatRL tau rho (phi => phi').
  Proof.
    intros tau rho phi phi' WF H H'.
    destruct H' as (phi1 & H' & H'').
    unfold SatRL.
    split; trivial.
    unfold SatRL in H''.
    destruct H'' as (H0 & [H1 | H1]).
    simpl in *.
    destruct H1 as (n & i & gamma & H1 & H2 & H3 & H4).
    left.
    exists (n + 1), (i + 1), gamma.
    split; trivial.
    - omega.
    - split.
      + unfold complete in *.
        destruct H2 as (gamma_n & H5 & H6).
        exists gamma_n.
        split; trivial.
        rewrite <- shift_index; trivial.
      + split; trivial.
        rewrite <- shift_index; trivial.
    -right. apply is_infinite with (i := 1); trivial.
  Qed.
  

  (* helper *)
  Lemma complete_shift :
    forall tau i n',
      completeN (Path_i tau (i + 1)) n' ->
      completeN (Path_i tau 1) (n' + i) .
  Proof.
    intros tau i n' H.
    unfold completeN in *.
    destruct H as (gamma & H & H').
    exists gamma.
    split; trivial.
    rewrite shift_index in *.
    rewrite plus_assoc in H; trivial.
  Qed.


  (* helper *)
  Lemma remove_other :
    forall G g g',
      In g G ->
      g' <> g ->
      In g (remove RLFormula_eq_dec g' G).
  Proof.
    induction G; intros.
    - contradict H.
    - simpl in H.
      destruct H as [H | H].
      + subst.
        simpl.
        case_eq (RLFormula_eq_dec g' g); intros.
        * contradiction.
        * simpl; left; trivial.
      + simpl.
        case_eq (RLFormula_eq_dec g' a); intros.
        subst.
        apply IHG; trivial.
        simpl. right.
        apply IHG; trivial.
  Qed.


  (* Important: any G is in F *)
  Lemma G_in_F :
    forall g G,
      steps G ->
      In g G ->
      inF g.
  Proof.
    intros g G H.
    revert g.
    induction H; intros.
    - contradict H.
    - assert (H3 : (g = g0) \/ ~(g = g0)).
      + apply classic.
      + destruct H3 as [H3 | H3].
        * subst.
          apply in_step with (G := G) (G' := G'); trivial.
        * apply IHsteps.
          inversion H; subst.
          apply remove_other; trivial.
          apply in_app_iff.
          left; apply remove_other; trivial.
          apply in_app_iff.
          left; apply remove_other; trivial.
  Qed.
  
  (* helper *)
  Lemma der_in_Delta :
    forall phi phi' alpha,
      In alpha S ->
      In (phi => phi') G0 ->
      In (SynDerML' phi alpha => phi') (Delta S G0).
  Proof.
    intros phi phi' alpha H0 H1.
    induction G0.
    - contradict H1.
    - unfold Delta.
      simpl in H1.
      destruct H1 as [H1 | H1].
      + subst.
        rewrite in_app_iff.
        left.
        unfold SynDerRL, SynDerRL'.
        rewrite in_map_iff.
        exists (SynDerML' phi alpha).
        split.
        * simpl.
          reflexivity.
        * unfold SynDerML.
          rewrite in_map_iff.
          exists alpha.
          simpl.
          split; trivial.
      + fold Delta.
        rewrite in_app_iff.
        right.
        apply IHl; trivial.
  Qed.
  
  (* helper *)
  Lemma first_transition :
    forall tau rho phi n,
      wfPath tau ->
      completeN tau (Datatypes.S n) ->
      startsFrom tau rho phi ->
      exists gamma gamma',
        tau 0 = Some gamma /\ tau 1 = Some gamma' /\
        (gamma =>S gamma').
  Proof.
    intros tau rho phi n W H H'.
    unfold startsFrom in H'.
    destruct H' as (gamma & H0 & H1).
    exists gamma.
    assert (H2 : (exists gamma' : State, tau 1 = Some gamma')).
    - apply first_step_gamma with (n := n) (gamma := gamma); trivial.
    - destruct H2 as (gamma' & H2).
      exists gamma'.
      repeat split; trivial.
      unfold wfPath, wfGPath in W.
      destruct W as (W & W').
      assert (H3: tau 0 <> None /\ tau (0 + 1) <> None).
      + split; unfold not; intros H3.
        * rewrite H3 in *; inversion H0.
        * simpl in H3; rewrite H3 in *; inversion H2.
      + apply W' in H3.
        destruct H3 as (e & e' & H3 & H4 & H5).
        simpl in H4.
        rewrite H3 in H0;inversion H0.
        rewrite H4 in H2; inversion H2.
        subst e e'.
        trivial.
  Qed.

  (* helper *)
  Lemma disjoint_component :
    forall phi phi' F,
      wfFormula F ->
      disjoint_vars_RL (phi => phi') F ->
      disjoint_set_RL F (getFreeVars phi).
  Proof.
    intros phi phi' F H H'.
    unfold disjoint_vars_RL, disjoint_vars in H'.
    unfold disjoint_set_RL.
    intros x Hx.
    simpl in *.
    rewrite app_nil_r.
    apply H' in Hx.
    unfold not in *.
    intros H1.
    apply Hx.
    rewrite <- wf_free.
    - instantiate (1 := (rhs F));trivial.
    - destruct F; simpl; trivial.
  Qed.
  



  (* Important: MAIN LEMMA *)
  Lemma finite_sound :
    forall n tau rho phi phi',
      G0 <> [] -> 
      wfPath tau ->
      inF (phi => phi') ->
      completeN tau n ->
      steps (Delta S G0) ->
      startsFrom tau rho phi ->
      total ->
      (forall p p', In (p => p') G0 -> SDerivable p) ->
      (forall F, In F G0 -> wfFormula F) ->
      (forall F, In F S -> wfFormula F) ->
      (forall g, In g G0 -> disjoint_vars_rules S g) ->
      SatRL tau rho (phi => phi').
  Proof.
    induction n using custom_lt_wf_ind.
    - intros tau rho phi phi' NE WF H' H0 H H1 T Ax WFF1 WFF2 D.
      assert (SF : startsFrom tau rho phi); trivial.
      unfold startsFrom in SF.
      destruct SF as (g & SF & SF').
      apply impl_or_der in H'; trivial.
      + destruct H' as [H' | H'].
        * unfold SatRL.
          simpl.
          split; trivial.
          assert (C : completeN tau 0); trivial.
          unfold complete in H0.
          destruct H0 as (gamma & H0 & H3).
          left.
          exists 0, 0, gamma.
          repeat split; trivial.
          apply valid_impl with (phi := phi); trivial.
          unfold startsFrom in H1.
          destruct H1 as (gamma0 & H1' & H1).
          rewrite H1' in H0.
          inversion H0.
          subst; trivial.
        * unfold complete in H0.
          destruct H0 as (gamma & H2 & H3).
          unfold total in T.
          apply T  with
          (gamma := gamma) (rho := rho) in H'; trivial.
          destruct H' as (gamma' & H').
          unfold terminating in H3.
          contradict H'.
          apply H3; trivial.
          unfold startsFrom in H1.
          destruct H1 as (gamma0 & (H1 & H1')).
          rewrite H2 in H1.
          inversion H1; trivial.
      + exists g, rho; trivial.
    - intros tau rho phi phi' NE WF H' H0 H1 H2 T Ax WFF1 WFF2 D.
      inversion H'.
      + (* case 1: the goal in F is in G0 *)
        (* get the first transition *)
        assert (H5: exists gamma gamma' : State,
                      tau 0 = Some gamma /\ tau 1 = Some gamma' /\ (gamma =>S gamma')).
        apply first_transition with (rho := rho) (phi := phi) (n := n); trivial.
        (* prepare cover_step *)
        assert (SF : startsFrom tau rho phi); trivial.
        destruct H5 as (gamma & gamma' & T0 & T1 & H5).
        unfold startsFrom in H2.
        destruct H2 as (gamma0 & H2' & H2).
        rewrite T0 in H2'.
        inversion H2'.
        subst gamma0.
        
        (* apply cover_step *)
        assert (H6 : exists (alpha : RLFormula) (phi' : MLFormula),
                       In alpha S /\
                       phi' = SynDerML' phi alpha /\ SatML gamma' rho phi').
        apply cover_step with (gamma := gamma); trivial.
        intros F HF.
        assert (HF' : In F S); trivial.
        apply D in H3.
        unfold disjoint_vars_rules in H3.
        apply H3 in HF.
        apply disjoint_component with (phi' := phi') ; trivial.
        apply WFF2; trivial.
        apply disjoint_vars_RL_sym; trivial.
        destruct H6 as (alpha & phi1 & H6 & H7 & H8).
        
        (* apply one step *)
        apply one_step; trivial.
        exists phi1.
        split.
        unfold SynDerML.
        rewrite in_map_iff.
        exists alpha; split; trivial.
        subst phi1.
        trivial.
        
        (* inductive hypothesis *)
        apply H with (tau := (Path_i tau 1)) (m := n); trivial.
        apply wf_subpath; trivial.
        subst phi1.
        apply G_in_F with (G := (Delta S G0)); trivial.
        apply der_in_Delta; trivial.
        unfold startsFrom.
        exists gamma'.
        split; trivial.
      + (* case 2 : goal is in F, but not in G0 *)
        generalize H1.
        intros Step.
        clear H1.
        rename G' into G''.
        rename G into G'.
        inversion H3. 
        * (* goal eliminated by implication *)
          simpl in H6.
          unfold SatRL.
          split; try simpl; try exact H2.
          unfold startsFrom in H2.
          destruct H2 as (gamma & H2 & H8).
          apply valid_impl with
          (gamma := gamma) (rho := rho) (phi' := phi') in H8; trivial.
          left.
          exists (Datatypes.S n), 0, gamma.
          simpl;split; trivial.
          omega.
          repeat split; trivial.
        * (* goal eliminated by circularity *)
          assert (SF: startsFrom tau rho phi); trivial.
          unfold startsFrom in H2.
          destruct H2 as (gamma & (H2 & H2')).
          rename H9 into H10.
          rename H8 into H9.
          simpl in H9.
          apply valid_impl
          with (gamma := gamma) (phi' := (EClos (lhs c)))
                                (phi := phi) (rho := rho) in H9; trivial.
          unfold EClos in H9.
          apply SatML_Exists in H9.
          destruct H9 as (rho' & H9 & H9').
          
          (* preparing the first application of IH *)
          (* get the first transition *)
          assert (H12 : exists gamma gamma' : State,
                          tau 0 = Some gamma /\ tau 1 = Some gamma' /\
                          (gamma =>S gamma')).
          apply first_transition with (rho := rho) (phi := phi) (n := n); trivial.
          
          (* cover step for circularity *)
          destruct H12 as (gamma0 & gamma' & T0 & T1 & H12).
           rewrite T0 in *.
           inversion H2.
           subst gamma0.
           apply cover_step with (rho := rho') (phi := (lhs c)) in H12; trivial.
           destruct H12 as (alpha & phic_1 & H12 & H13 & H14).
           
           (* inductive hypothesis for a shorter path (covered by circ) *)
           assert (H17 : SatRL (Path_i tau 1) rho' (phic_1 => (rhs c))).
           {
             apply H with (m := n); trivial.
             - apply wf_subpath; trivial.
             - apply G_in_F with (G := (Delta S G0)); trivial.
               subst phic_1.
               apply der_in_Delta; trivial.
               destruct c; simpl; trivial.
             - unfold startsFrom.
               exists gamma'.
               rewrite shift_index.
               simpl.
               split; trivial.
           }
           
           (* prepare for the second application of the inductive hypothesis *)
           unfold SatRL in H17.
           destruct H17 as (H17' & [H17 | H17]).
           simpl in H17.
           destruct H17 as (n0 & i & gamma_i & H17 & H18 & H19 & H20).
           
           
           (* goal: gamma_i starts from  Delta_c(phi) *)
           assert (H21 : SatML gamma_i rho (SynDerML' (phi) c')).
           {
             assert (H21' : (wfFormula c')).
             apply RL_alpha_equiv_wf with (F := c); trivial.
             apply WFF1; trivial.
             destruct c as (phic & phic'), c' as (c_ & c_').
             simpl in *.
             apply RL_alpha_equiv_ML with (rho := rho') in H6.
             destruct H6 as (rho_ & H6 & H6').
             unfold SynDerML'.
             simpl.
             rewrite SatML_Exists.
             set (vars := ((getFreeVars c_))).
             exists (modify_val_on_set rho rho_ vars).
             split.
             - intros v H21.
               rewrite modify_not_in.
               reflexivity.
               unfold not in *.
               intros Hv.
               apply H21.
               subst vars.
               simpl.
               rewrite app_nil_r; trivial.
               apply in_app_iff.
               left. trivial.
             - apply SatML_And.
               split; trivial.
               + rewrite Proposition1.
                 exists gamma.
                 apply SatML_And.
                 split; trivial.
                 * apply modify_Sat1; trivial.
                   subst vars.
                   apply SatML_val_relation with (varphi := phic) (rho := rho'); trivial.
                   subst vars.
                   apply incl_refl.
                 * apply modify_Sat2; trivial.
               + apply modify_Sat1; trivial.
                 apply SatML_val_relation with (varphi := phic') (rho := rho'); trivial.  
           }

           (* apply the inductive hypothesis for the subpath starting at i *)
           assert (H20' : SatRL (Path_i tau (i + 1)) rho
                                ((SynDerML' phi c') => phi')).
           {
             assert (H21' : n0 = n).
             apply one_step_less with (tau := tau); trivial.
             subst n0.
             apply H with (m := n - i); trivial.
             - omega.
             - apply wf_subpath; trivial.
             - apply H4.
               rewrite H10.
               apply in_app_iff.
               right.
               unfold SynDerRL.
               simpl.
               left.
               unfold SynDerRL'.
               simpl; trivial.
             - unfold complete.
               unfold complete in H0.
               destruct H0 as (gamma0 & H0 & H1').
               exists gamma0.
               split;trivial.
               + rewrite shift_index.
                 assert (H22: (n - i + (i + 1)) = Datatypes.S n).
                 * omega.
                 * rewrite H22; trivial.
             - unfold startsFrom.
               exists gamma_i.
               split; trivial.
               rewrite <- H19.
               repeat rewrite shift_index; trivial.
           }

           unfold SatRL in H20'.
           destruct H20' as (S & [H20' | H20']).
           simpl in H20'.
           destruct H20' as (n1 & j & gamma_j & H21' & H22 & H23 & H24).
           unfold SatRL.
           split; try simpl; trivial.
           left.
           exists (Datatypes.S n), (j + (i + 1)), gamma_j.
           split; trivial.
           apply complete_shift in H22.
           apply one_step_less with (n := n) in H22; trivial.
           apply plus_le_compat_r with (p := i) in H21'.
           rewrite H22 in H21'.
           rewrite plus_assoc.
           omega.
           split; trivial.
           split; try rewrite shift_index in H23; trivial.
           apply D in H5.
           unfold disjoint_vars_rules in H5.
           apply is_infinite in H20'.
           unfold SatRL.
           split; trivial.
           right; trivial.
           trivial.
           apply is_infinite in H17.
           unfold SatRL.
           split; trivial.
           right; trivial.
           trivial.
           intros F HF.
           assert (H13 : wfFormula F).
           apply WFF2. trivial.
           apply D in H5.
           unfold disjoint_vars_rules in H5.
           apply H5 in HF.
           unfold disjoint_vars_RL, disjoint_vars in HF.
           unfold disjoint_set_RL, disjoint_vars.
           intros x Hx.
           unfold not.
           intros HH.
           destruct F.
           apply wf_free with (x := x) in H13.
           unfold FreeVars in HH.
           simpl in *.
           rewrite app_nil_r in HH.
           rewrite H13 in HH.
           apply HF in HH.
           contradiction.
         * (* third case *)
           (* get the first transition *)
           simpl in H5.
           assert (SF:  startsFrom tau rho phi); trivial.
           unfold startsFrom in H2.
           destruct H2 as (gamma & H2 & H8').
           assert (H9 : exists gamma', tau 1 = Some gamma').
           apply first_step_gamma with (n := n) in H2; trivial.
           destruct H9 as (gamma' & H9).
           assert (H10 : gamma =>S gamma').
           {
             unfold wfPath, wfGPath in WF.
             destruct WF as (WF & WF').
             assert (H10: tau 0 <> None /\ tau (0 + 1) <> None).
             {
               split; unfold not; intros H10.
               - rewrite H10 in *.
                 inversion H2.
               - simpl in H10.
                 rewrite H10 in *.
                 inversion H9.
             }
             apply WF' in H10.
             destruct H10 as (e & e' & H10 & H11 & H12).
             simpl in H11.
             rewrite H10 in H2.
             rewrite H11 in H9.
             inversion H2.
             inversion H9.
             subst e e'.
             assumption.
           }

           (* First transition with S' : gamma =>S' gamma' *)
           unfold TS in H10.
           destruct H10 as (phi_l & phi_r & rho' & H10 & h1 & h2).
           unfold RL_alpha_equiv_S in H6.
           assert (H10': In (phi_l => phi_r) S); trivial.
           apply H6 in H10.
           destruct H10 as (F' & HS' & E).
           assert (H10 : TS S' gamma gamma').
           {
             destruct F'.
             unfold TS.
             apply RL_alpha_equiv_ML with (rho := rho') in E.
             destruct E as (rho'' & E & E').
             exists m, m0, rho''.
             split; trivial.
             split.
             apply SatML_val_relation with (gamma := gamma) in E; trivial.
             apply SatML_val_relation with (gamma := gamma') in E'; trivial.
           }
           
           (* cover step *)
           apply cover_step with (rho := rho) (phi := phi) in H10; trivial.
           destruct H10 as (alpha & phi1 & H10 & H11 & H12).

           (* apply the inductive hypothesis on a shorter path *)
           assert (H13: SatRL (Path_i tau 1) rho (phi1 => phi')).
           {
             apply H with (m := n); trivial.
             - apply wf_subpath; trivial.
             - apply H4.
               rewrite H8.
               apply in_app_iff.
               right.
               unfold SynDerRL, SynDerRL', SynDerML.
               rewrite in_map_iff.
               exists phi1.
               split; trivial.
               rewrite in_map_iff.
               exists alpha. 
               split; trivial.
               subst phi1.
               reflexivity.
             - unfold startsFrom.
               exists gamma'.
               split; trivial.
           }
           
           unfold SatRL.
           split; trivial.
           unfold SatRL in H13.
           destruct H13 as (S & [H13 | H13]).
           simpl in H13.
           destruct H13 as (n0 & j & gamma_j & Hj & H14 & H15 & H16).
           left.
           exists (Datatypes.S n), (j + 1), gamma_j.
           split.
           rewrite one_step_less with
           (tau := tau) (n := n) in Hj; trivial.
           omega.
           repeat split; trivial.
           rewrite shift_index in H15; trivial.
           right.
           apply is_infinite in H13; trivial.
           intros F HF.
           unfold disjoint_vars_rules in H7.
           assert (HF' : In F S'); trivial.
           apply H7 in HF'.
           unfold disjoint_set_RL.
           unfold disjoint_vars_RL, disjoint_vars in HF'.
           intros x Hx.
           unfold not in *.
           intros HH.
           apply HF' with (x := x).
           unfold FreeVars in HH.
           rewrite app_nil_r in HH.
           rewrite wf_free with (x := x) in HH; trivial.
           apply H6 in HF.
           destruct HF as (F1 & FS & EE).
           apply RL_alpha_equiv_wf with (F := F1).
           apply WFF2; trivial.
           destruct F; simpl.
           apply RL_alpha_equiv_sym; trivial.
           simpl; trivial.
           intros F HF.
           apply H6 in HF.
           destruct HF as (F1 & FS & EE).
           apply RL_alpha_equiv_wf with (F := F1).
           apply WFF2; trivial.
           apply RL_alpha_equiv_sym; trivial.
  Qed.
  

  (* The soundness theorem *)
  Theorem sound : total ->
                  (forall g, In g G0 -> disjoint_vars_rules S g) ->
                  (forall p p', In (p => p') G0 -> SDerivable p) ->
                  (forall F, In F G0 -> wfFormula F) ->
                  (forall F, In F S -> wfFormula F) ->
                  steps (Delta S G0) ->
                  SatTS_G G0.
  Proof.
    intros T D Ax WFF1 WFF2 H g H0 tau rho H1 H2 H3.
    case_eq G0.
    - intros H'.
      rewrite H' in H0.
      contradict H0.
    - intros r l NE.
      unfold complete in H3.
      destruct H3 as [H3 | (NI & n & H3)].
      + unfold SatRL.
        split; trivial.
        right; trivial.
      + apply finite_sound with (n := n); trivial.
        * intros H'.
          rewrite H' in NE.
          inversion NE.
        * destruct g.
          apply init; assumption.
  Qed.
  
End Soundness.
