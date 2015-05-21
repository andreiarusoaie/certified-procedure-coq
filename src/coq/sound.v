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
  Variable G0 : list RLFormula .

  Axiom all_G0_der :
    forall phi phi',
      In (phi => phi') G0 -> SDerivable phi.


  (* Section step *)
  
  Inductive step (G G': list RLFormula)
            (g : RLFormula) : Prop :=
  | base_case : In g G ->
                ValidML (ImpliesML (lhs g) (rhs g)) ->
                G' = remove RLFormula_eq_dec g G ->
                step G G' g
  | circ_case : forall c, 
                  In g G -> In c G0 ->
                  ValidML (ImpliesML (lhs g) (EClos (lhs c))) ->
                  G' = (remove RLFormula_eq_dec g G)
                         ++ (SynDerRL [c] g) ->
                  step G G' g
  | deriv_case: In g G -> SDerivable (lhs g) ->
                G' = (remove RLFormula_eq_dec g G)
                       ++ (SynDerRL S g) ->
                step G G' g.
  
  Inductive step_star : list RLFormula -> list RLFormula ->
                        list RLFormula -> Prop :=
    | refl : step_star [] [] G0
    | tranz : forall G G' G'' g F,
                step G G'' g ->
                step_star G'' G' F ->
                step_star G G' (g :: F).


    
(*
  Check step_star_ind.

  Check le_ind.

  Inductive step_lt  (G G' : list RLFormula) : Prop :=
  | step_lt_base: forall g, step G G' g -> step_lt G G'
  | step_lt_step: forall g G'', step G G'' g -> step_lt G'' G' -> step_lt G G'.
  
  Lemma step_star_reverse_ind :
    forall P : list RLFormula -> list RLFormula -> list RLFormula -> Prop,
    forall G G' F,
      P G G' F ->
      (forall G'' G' F' g,
         F = g :: F' ->
         step G G'' g -> step_star G G' F -> P G G' F -> P G'' G' F' )
      ->
      forall G'', step_lt G'' G -> P G'' [] G0.
 
  Comment: this is not enough; I need a relation between "step_star"s , 
   themselves to write the conclusion of the induction principle. 
  Still thinking.
  
  Inductive step_star' : list RLFormula -> list RLFormula ->
                        list RLFormula -> Prop :=
  | refl' : step_star [] [] G0
  | tranz' : forall G G' g F,
               step G' [] g ->
               step_star' G G' F ->
               step_star' G [] (F ++ [g]).
  

  Lemma helper :
    forall G g F,
      step_star G [] F ->
      ~ In g G0 ->
      exists G' G'' F0, step G' G'' g /\ step_star G'' [] F0 /\ incl F0 F.
  Proof.
    intros.
    induction H.
    - contradiction.
    - simpl in H1.
      destruct H1 as [H1 | H].
      + subst g0.
   *)            
  
  Lemma helper_1 : forall G g F0,
                     ~ In g G0 ->
                     step_star G [] (g::F0) ->
                     exists G',
                       step G G' g /\ step_star G' [] F0 .
  Proof.
    intros G g F0 H H0.
    inversion H0.
    - rewrite H2 in H.
      simpl in H.
      contradict H.
      left.
      reflexivity.
    - subst g G1 G' F.
      exists G''.
      split; assumption.
  Qed.

  Lemma helper_2 : forall F G g,
                     step_star G [] F ->
                     In g F ->
                     ~ In g G0 ->
                     exists G' F0, step_star G' [] (g::F0).
  Proof.
    induction F; intros.
    - contradict H0.
    - simpl in H0.
      destruct H0 as [H0 | H0].
      + subst a.
        exists G, F.
        assumption.
      + inversion H.
        * rewrite H3 in H1.
          simpl in H1.
          assert (a = g \/ ~(a = g)).
          apply classic.
          destruct H4 as [H4 | H4].
          {
            exists G, F.
            rewrite H4 in *.
            assumption.
          }
          {
            contradict H1.
            right.
            assumption.
          }
        * apply IHF with (G := G'');
          assumption.
  Qed.

  (* End Section step *)


  (* Section Valuations *)

  (* TODO: wfFormula *)
  Lemma rhs_vars_in_lhs :
    forall x F,
      In x (FreeVars [(lhs F); (rhs F)]) <-> In x (FreeVars [lhs F]).
  Admitted.

  (* TODO: alpha equivalence *)
  Lemma disjoint_domain_2 :
    forall phi v c,
      In c G0 ->
      In v (FreeVars [phi]) ->
      ~ In v (FreeVars [lhs c]).
  Admitted.

  Axiom disjoint_vars :
    forall gamma rho rho' phi,
      SatML gamma rho phi ->
      (forall v : Var, In v (FreeVars [phi]) -> rho v = rho' v) ->
      SatML gamma rho' phi.
  
   (* End Section Valuations *)


  

  Lemma cover_step :
    forall gamma gamma' rho phi,
      (gamma =>S gamma') ->
      SatML gamma rho phi ->
      exists alpha phi',
        In alpha S /\
        phi' = SynDerML' phi alpha /\
        SatML gamma' rho phi' .
  Proof.
    intros gamma gamma' rho phi H H'.
    unfold TS in H.
    destruct H as (phi_l & phi_r & rho' & H0 & H1 & H2).
    exists (phi_l => phi_r), (SynDerML' phi (phi_l => phi_r)).
    split; trivial.
    split.
    - reflexivity.
    - unfold SynDerML'.
      simpl.
      apply SatML_Exists.
      exists (modify_val_on_set rho rho' (FreeVars [phi_l; phi_r])) .
      split.
      + intros v V.
        rewrite modify_2; trivial.
      + apply SatML_And.
        split.
        * apply Proposition1.
          exists gamma.
          apply SatML_And.
          split.
          apply modify_Sat1; trivial.
          intros x V.
          simpl.


          
          
          rewrite <- modify_1.
    
  Qed.

  Lemma impl_sder : forall phi c,
                      In c G0 ->
                      ValidML (ImpliesML phi (EClos (lhs c))) ->
                      SDerivable (lhs c) ->
                      SDerivable phi.
  Proof.
  Admitted.

  

  Lemma impl_or_der :
    forall F G phi phi',
      step_star G [] F ->
      In (phi => phi') F ->
      ValidML (ImpliesML phi phi') \/ SDerivable phi .
  Proof.
    intros F G phi phi' H H0.
    assert (In (phi => phi') G0 \/ ~(In (phi => phi') G0)).
    - apply classic.
    - destruct H1 as [H1 | H1].
      + right.
        apply all_G0_der with (phi' := phi'); trivial.
      + apply helper_2 with (g := (phi => phi')) in H; trivial.
        destruct H as (G' & (F0 & H)).
        apply helper_1 in H; trivial.
        clear G.
        destruct H as (G & (H & H')).
        clear H'.
        inversion H; simpl in H3.
        * left; trivial.
        * simpl in H4.
          right.
          apply impl_sder with (c := c); trivial.
          apply all_G0_der with (phi' := (rhs c)).
          destruct c; trivial.
        * right; trivial.
  Qed.

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
     induction n0; trivial.
     apply H2.
     intros m H.
     apply H3.
     apply le_lt_n_Sm in H; trivial.
   Qed.


   Lemma shift_index :
     forall tau j k,
       Path_i tau j k = tau (k + j).
   Proof.
     intros tau j k.
     unfold Path_i, GPath_i.
     rewrite plus_comm; trivial.
   Qed.
                         
   
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

   

   Lemma alpha_to_S :
     forall phi phi1 alpha,
       In alpha S ->
       phi1 = SynDerML' phi alpha ->
       In phi1 (SynDerML phi S).
   Proof.
     intros phi phi1 alpha H H'.
     unfold SynDerML.
     rewrite in_map_iff.
     exists alpha.
     split; trivial.
     rewrite H'; trivial.
   Qed.


   Lemma first_step_gamma :
     forall tau n gamma,
       wfPath tau ->
       complete tau (Datatypes.S n) ->
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

   Lemma one_step_less :
     forall tau n n0,
       wfPath tau ->
       complete tau (Datatypes.S n) ->
       complete (Path_i tau 1) n0 ->
       n0 = n.
   Proof.
     intros tau n n0 WF H H'.
     unfold complete in *.
     destruct H as(gamma & H0 & H1).
     destruct H' as(gamma' & H0' & H1').
     unfold wfPath, wfGPath in WF.
     destruct WF as (WF & WF').
     rewrite shift_index in H0'.
     assert (Sn : n + 1 = Datatypes.S n). { simpl. omega. }
     assert (Sn' : n0 + 1 = Datatypes.S n0). { simpl. omega. }
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

   Lemma one_step :
     forall tau rho phi phi',
       startsFrom tau rho phi ->
       (exists phi1,
          In phi1 (SynDerML phi S) /\
          SatRL (Path_i tau 1) rho (phi1 => phi')) ->
       SatRL tau rho (phi => phi').
   Proof.
     intros tau rho phi phi' H H'.
     destruct H' as (phi1 & H' & H'').
     unfold SatRL.
     split; trivial.
     unfold SatRL in H''.
     destruct H'' as (H0 & H1).
     simpl in *.
     destruct H1 as (n & i & gamma & H1 & H2 & H3 & H4).
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
   Qed.
   

   
   Lemma complete_shift :
     forall tau i n',
       complete (Path_i tau (i + 1)) n' ->
       complete (Path_i tau 1) (n' + i) .
   Proof.
     intros tau i n' H.
     unfold complete in *.
     destruct H as (gamma & H & H').
     exists gamma.
     split; trivial.
     rewrite shift_index in *.
     rewrite plus_assoc in H; trivial.
   Qed.


   Lemma first_step : forall phi phi' phi1 F,
                        step_star (Delta S G0) [] F ->
                        In (phi => phi') G0 ->
                        In phi1 (SynDerML phi S) ->
                        In (phi1 => phi') F.
   Admitted.

   
   Lemma finite_sound :
     forall n tau rho phi phi' F,
       wfPath tau ->
       In (phi => phi') F ->
       complete tau n ->
       step_star (Delta S G0) [] F ->
       startsFrom tau rho phi ->
       total ->
       SatRL tau rho (phi => phi').
   Proof.
     induction n using custom_lt_wf_ind.
     - intros tau rho phi phi' F WF H' H0 H H1 T.
       apply impl_or_der with
       (phi := phi) (phi' := phi') in H.
       + destruct H as [H | H].
         * unfold SatRL.
           split.
           {simpl.
             unfold startsFrom.
             unfold complete in H0.
             destruct H0 as (gamma & H0 & H3).
             exists gamma.
             split.
            - rewrite <- H0.
              reflexivity.
            - unfold startsFrom in H1.
              destruct H1 as (gamma0 & H1 & H4).
              rewrite H0 in H1.
              inversion H1.
              assumption. }
           unfold startsFrom in H1.
           destruct H1 as (gamma & (H1 & H2)).
           exists 0, 0, gamma.
           split; trivial.
           split; trivial.
           split; trivial.
           simpl.
           apply valid_impl with (phi := phi);assumption.
         * unfold complete in H0.
           destruct H0 as (gamma & H2 & H3).
           unfold total in T.
           apply T with
           (gamma := gamma) (rho := rho) in H.
           destruct H as (gamma' & H).
           unfold terminating in H3.
           contradict H.
           apply H3.
           unfold startsFrom in H1.
           destruct H1 as (gamma0 & (H1 & H1')).
           rewrite H2 in H1.
           inversion H1.
           exact H1'.
       + exact H'.
     - intros tau rho phi phi' F WF H' H0 H1 H2 T.
       assert (In (phi => phi') G0 \/ ~ (In (phi => phi') G0)); trivial.
       + apply classic.
       + destruct H3 as [H3 | H3].
         * apply one_step; trivial.
           unfold startsFrom in H2.
           destruct H2 as (gamma & H2 & H4).
           assert (H5 : exists gamma', tau 1 = Some gamma').
           { apply first_step_gamma with (n := n) (gamma := gamma); trivial. }
           destruct H5 as (gamma' & H5).

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
                 inversion H5.
             }
             apply WF' in H10.
             destruct H10 as (e & e' & H10 & H11 & H12).
             simpl in H11.
             rewrite H10 in H2.
             rewrite H11 in H5.
             inversion H2.
             inversion H5.
             subst e e'.
             assumption.
           }
           assert (H6 : exists (alpha : RLFormula) (phi1 : MLFormula),
                          In alpha S /\ phi1 = SynDerML' phi alpha /\ SatML gamma' rho phi1).
           { apply cover_step with (gamma := gamma); trivial. }
           destruct H6 as (alpha & phi1 & H6 & H7 & H8).
           exists phi1.
           split.
           apply alpha_to_S with (alpha := alpha); trivial.
           apply H with (tau := (Path_i tau 1)) (m := n) (F := F); trivial.
           apply wf_subpath; trivial.
           apply first_step with (phi := phi); trivial.
           subst phi1.
           unfold SynDerML.
           rewrite in_map_iff.
           exists alpha; split; trivial.
           unfold startsFrom.
           exists gamma'.
           split; trivial.

         * generalize H1.
           intros Step.
           apply helper_2 with (g := (phi => phi')) in H1; trivial.
           
           destruct H1 as (G' & (F0 & H1)).
           apply helper_1 in H1; trivial.
           destruct H1 as (G'' & (H1 & H4)).
           {
             inversion H1. 
             - simpl in H6.
               unfold SatRL.
               split.
               + simpl.
                 exact H2.
               + unfold startsFrom in H2.
                 destruct H2 as (gamma & H2 & H8).
                 apply valid_impl with
                 (gamma := gamma) (rho := rho) (phi' := phi') in H8.
                 exists (Datatypes.S n), 0, gamma.
                 simpl.
                 split; trivial.
                 omega.
                 split; trivial.
                 split; trivial.
                 * exact H6.
             - simpl in H7.
               unfold startsFrom in H2.
               destruct H2 as (gamma & (H2 & H2')).
               apply valid_impl with
               (gamma := gamma) (phi' := (EClos (lhs c)))
                                (phi := phi) (rho := rho) in H7; trivial.
               unfold EClos in H7.
               apply SatML_Exists in H7.
               destruct H7 as (rho' & (H7 & H7')).

               (* first part *)
               assert (H9 : exists gamma', tau 1 = Some gamma').
               {
                 apply first_step_gamma with
                 (n := n) (gamma := gamma); trivial.
               }
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

               apply cover_step with
               (rho := rho') (phi := (lhs c)) in H10; trivial.
               
               destruct H10 as (alpha & phic_1 & H11 & H12 & H13).
                 
               assert (H14 : SatRL (Path_i tau 1) rho' (phic_1 => (rhs c))).
               {
                 apply H with (m := n)  (F := F); trivial.
                 - apply wf_subpath; trivial.
                 - apply first_step with (phi := (lhs c)); trivial.
                   + destruct c.
                     simpl; trivial.
                   + apply alpha_to_S with (alpha := alpha); trivial.
                 - unfold startsFrom.
                   exists gamma'.
                   rewrite shift_index.
                   simpl.
                   split; trivial.
               }
               unfold SatRL in H14.
               simpl in H14.
               destruct H14 as (H14 & n0 & i & gamma_i & H15 & H16 & H17 & H18).
               
               assert (H19 : SatML gamma_i rho (SynDerML' phi c)).
               {
                 unfold SynDerML'.
                 rewrite SatML_Exists.
                 exists rho'.
                 split.
                 - intros v H20.
                   apply H7.
                   rewrite <- rhs_vars_in_lhs; trivial.
                 - apply SatML_And.
                   split; trivial.
                   rewrite Proposition1.
                   exists gamma.
                   apply SatML_And.
                   split; trivial.
                   apply disjoint_vars with (rho := rho); trivial.
                   intros v H19.
                   apply disjoint_domain_2 with (c := c) in H19; trivial.
                   apply H7 in H19; trivial.
               }

               clear H18 H13 H14 H7 H7' rho'.
               assert (H20 : SatRL (Path_i tau (i + 1)) rho
                                       ((SynDerML' phi c) => phi')).
               {
                 assert (H21 : n0 = n).
                 apply one_step_less with (tau := tau); trivial.
                 subst n0.
                 apply H with (m := n - i)(F := F); trivial.
                 - omega.
                 - apply wf_subpath; trivial.
                 - admit.
                 - unfold complete.
                   unfold complete in H0.
                   destruct H0 as (gamma0 & H0 & H1').
                   exists gamma0.
                   split.
                   + rewrite shift_index.
                     assert (H22: (n - i + (i + 1)) = Datatypes.S n).
                     * omega.
                     * rewrite H22.
                       exact H0.
                   + exact H1'.
                 - unfold startsFrom.
                   exists gamma_i.
                   split.
                   + rewrite <- H17.
                     rewrite shift_index.
                     rewrite shift_index.
                     simpl.
                     reflexivity.
                   + exact H19.
               }

               unfold SatRL in H20.
               simpl in H20.
               destruct H20 as (H20 & n1 & j & gamma_j & H21 & H22 & H23 & H24).
               unfold SatRL.
               split.
               + simpl.
                 unfold startsFrom.
                 exists gamma.
                 split; trivial.
               + auto. exists (Datatypes.S n), (j + (i + 1)), gamma_j.
                 split; trivial.
                 apply complete_shift in H22.
                 apply one_step_less with (n := n) in H22; trivial.
                 apply plus_le_compat_r with (p := i) in H21.
                 rewrite H22 in H21.
                 rewrite plus_assoc.
                 omega.
                 split; trivial.
                 split.
                 * rewrite shift_index in H23.
                   exact H23.
                 * simpl. exact H24.
             - simpl in H6.
               unfold startsFrom in H2.
               destruct H2 as (gamma & H2 & H8).

               assert (H9 : exists gamma', tau 1 = Some gamma').
               { apply first_step_gamma with (n := n) in H2; trivial. }
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

               apply cover_step with (rho := rho) (phi := phi) in H10.
               destruct H10 as (alpha & phi1 & H10 & H11 & H12).

               assert (H13: SatRL (Path_i tau 1) rho (phi1 => phi')).
               {
                 apply H with (m := n)(F := F); trivial.
                 - apply wf_subpath; trivial.
                 - admit.
                 - unfold startsFrom.
                   exists gamma'.
                   split; trivial.
               }
               unfold SatRL.
               split.
               + simpl.
                 unfold startsFrom.
                 exists gamma.
                 split; trivial.
               + unfold SatRL in H13.
                 simpl in H13.
                 destruct H13 as (H13 & n0 & j & gamma_j & Hj & H14 & H15 & H16).
                 exists (Datatypes.S n), (j + 1), gamma_j.
                 split.
                 rewrite one_step_less with
                 (tau := tau) (n := n) in Hj; trivial.
                 * omega.
                 * repeat split; trivial.
                   rewrite shift_index in H15; trivial.
               + assumption.
           }
   Qed.
   

   Lemma all_G0_in_F:
     forall g G F,
       In g G0 ->
       step_star G [] F ->
       In g F.
   Proof.
     intros g G F H H'.
     induction H'; trivial; simpl; tauto.
   Qed.
   
   Lemma sound : forall F,
                   total ->
                   step_star (Delta S G0) [] F ->
                   SatTS_G G0.
   Proof.
     intros F T H g H0 tau rho n H1 H2 H3.
     apply finite_sound with (n := n) (F := F); trivial.
     destruct g.
     apply all_G0_in_F with (G := (Delta S G0)); trivial.
   Qed.
              
End Soundness.
