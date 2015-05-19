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

  

  Lemma cover_step :
    forall gamma gamma' rho phi,
      (gamma =>S gamma') ->
      SatML gamma rho phi ->
      exists alpha phi',
        In alpha S /\
        phi' = SynDerML' phi alpha /\
        SatML gamma' rho phi' .
  Proof.
    admit.
  Qed.
   
  

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
        apply all_G0_der with (phi' := phi').
        exact H1.
      + apply helper_2 with (g := (phi => phi')) in H.
        * destruct H as (G' & (F0 & H)).
          apply helper_1 in H.
          clear G.
          destruct H as (G & (H & H')).
          {
            clear H'.
            inversion H; simpl in H3.
            - left.
              exact H3.
            - simpl in H4.
              right.
              admit.
            - right.
              exact H3.
          }
          exact H1.
        * exact H0.
        * exact H1.
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
     induction n0.
     - exact H1.
     - apply H2.
       intros m H.
       apply H3.
       apply le_lt_n_Sm in H.
       exact H.
   Qed.


   Lemma shift_index :
     forall tau j k,
       Path_i tau j k = tau (k + j).
   Proof.
     intros tau j k.
     unfold Path_i, GPath_i.
     rewrite plus_comm.
     reflexivity.
   Qed.
                         
   
   Lemma valid_impl :
     forall gamma rho phi phi',
       ValidML (ImpliesML phi phi') ->
       SatML gamma rho phi ->
       SatML gamma rho phi'.
   Admitted.

   
   

                   

   (* axiom ? *)
   Lemma rhs_vars_in_lhs :
     forall x F,
       In x (FreeVars [(lhs F); (rhs F)]) <-> In x (FreeVars [lhs F]).
   Admitted.

   Lemma wf_subpath : forall tau j,
                        wfPath tau -> wfPath (Path_i tau j) .
   Admitted.

   Lemma first_step : forall phi phi' phi1 G F,
                        step_star G [] F ->
                        In (phi => phi') G0 ->
                        In phi1 (SynDerML phi S) ->
                        In (phi1 => phi') F.
   Admitted.

   Lemma alpha_to_S :
     forall phi phi1 alpha,
       In alpha S ->
       phi1 = SynDerML' phi alpha ->
       In phi1 (SynDerML phi S).
   Admitted.


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
           

   (* Are these axioms ? *)
   Lemma disjoint_domain :
     forall phi c gamma rho rho',
       In c G0 ->
       (forall v, ~ In v (FreeVars [(lhs c)]) -> rho v = rho' v) ->
       (forall v, In v (FreeVars [phi]) -> ~ In v (FreeVars [(lhs c)])) ->
       SatML gamma rho phi ->
       SatML gamma rho' phi.
   Admitted.
   
   Lemma disjoint_domain_1 :
     forall phi v c,
       In c G0 ->
       In v (FreeVars [lhs c]) ->
       ~ In v (FreeVars [phi]).
   Admitted.
   
   Lemma disjoint_domain_2 :
     forall phi v c,
       In c G0 ->
       In v (FreeVars [phi]) ->
       ~ In v (FreeVars [lhs c]).
   Admitted.

   
   Lemma finite_sound :
     forall n tau rho phi phi' G F,
       wfPath tau ->
       In (phi => phi') F ->
       complete tau n ->
       step_star G [] F ->
       startsFrom tau rho phi ->
       total ->
       SatRL tau rho (phi => phi').
   Proof.
     induction n using custom_lt_wf_ind.
     - intros tau rho phi phi' G F WF H' H0 H H1 T.
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
     - intros tau rho phi phi' G F WF H' H0 H1 H2 T.
       assert (In (phi => phi') G0 \/ ~ (In (phi => phi') G0)); trivial.
       + apply classic.
       + destruct H3 as [H3 | H3].
         * admit.
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
                 apply H with (m := n) (G := G) (F := F); trivial.
                 - apply wf_subpath; trivial.
                 - apply first_step with (phi := (lhs c)) (G := G); trivial.
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
                   split.
                   + exact H7'.
                   + apply disjoint_domain with (c := c) (rho := rho); trivial.
                     intros v.
                     apply disjoint_domain_2; trivial.
               }

               clear H18 H13 H14 H7 H7' rho'.
               
               assert (H20 : SatRL (Path_i tau (i + 1)) rho
                                       ((SynDerML' phi c) => phi')).
               {
                 assert (H21 : n0 = n).
                 apply one_step_less with (tau := tau); trivial.
                 subst n0.
                 apply H with (m := n - i)
                                (G := G) (F := F); trivial.
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
                   rewrite plus_assoc in H.
                   exact H.
                 Qed.

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
             - admit.
           }
   Qed.
   
                     
                     
                   
                 
   Admitted.               


   Lemma all_G0_in_F : forall g G F,
                         In g G0 ->
                         step_star G [] F ->
                         In g F.
   Admitted.

   Lemma  len_finite_path :
     forall tau,
       ~isInfinite tau ->
       (forall i j, i < j -> tau i = None -> tau j = None) ->
       exists n, tau n <> None /\ tau (Datatypes.S n) = None.
   Admitted.

   
   Lemma not_infinite : forall tau,
                          wfPath tau ->
                          ~ (isInfinite tau) ->
                          exists n, complete tau n.
   Proof.
     intros tau H H'.
     generalize H'.
     intros H1.
     apply len_finite_path in H'.
     - destruct H' as (n & H2 & H3).
       exists n.
       unfold complete.
       split; trivial.
       unfold wfPath, wfGPath in H.
       destruct H as (H & H4).
       destruct H2 as (H2 & H5).
       assert (H6 : exists gamma', tau n = Some gamma').
       admit.
       destruct H6 as (gamma & H6).
       exists gamma.
       split; trivial.
       unfold terminating.
       intros gamma' H7.
   Admitted.
       
       
   
   Lemma sound : forall F,
                   total ->
                   step_star (Delta S G0) [] F ->
                   SatTS_G G0.
   Proof.
     intros F T H g H0 tau rho WF H1.
     assert (H' : isInfinite tau \/ ~ (isInfinite tau)).
     { apply classic. }
     destruct H' as [H' | H'].
     - unfold SatRL.
       split.
       + exact H1.
       + left.
         exact H'.
     - eapply finite_sound.
       + exact WF.
       + exact H'.
       + instantiate (1 := F).
         destruct g.
         apply all_G0_in_F with (Delta S G0); trivial.
       + unfold complete.
   Admitted.

              
End Soundness.
       