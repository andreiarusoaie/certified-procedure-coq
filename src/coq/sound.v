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

   Lemma valid_impl :
     forall gamma rho phi phi',
       ValidML (ImpliesML phi phi') ->
       SatML gamma rho phi ->
       SatML gamma rho phi'.
   Admitted.

   
   Lemma complete_subpath :
     forall tau n j,
       wfPath tau ->
       complete tau (n + j) ->
       complete (Path_i tau j) n.
   Proof.
     intros tau n j WF H.
     unfold complete in *.
     destruct H as (I & gamma & H').
     split.
     - apply not_infinite_subpath.
       exact I.
     - auto. exists gamma.
       rewrite shift_index.
       exact H'.
   Qed.
   
   Lemma first_step :
     forall (phi phi' phi1 : MLFormula) (G F : list RLFormula),
       step_star G [] F ->
       In (phi => phi') G0 ->
       In phi1 (SynDerML phi S) ->
       In (phi1 => phi') F .
   Admitted.

   Lemma starts_first_step :
     forall tau rho phi,
       startsFrom tau rho phi ->
       exists phi1,
         In phi1 (SynDerML phi S) ->
         startsFrom (Path_i tau 1) rho phi1.
   Admitted.


   
   Lemma complete_path :
     forall tau j n,
       ~ isInfinite tau ->
       wfPath tau ->
       complete (Path_i tau j) n ->
       complete tau (n + j).
   Proof.
     intros tau j n I WF H.
     unfold complete in *.
     destruct H as (H2 & gamma & H0 & H1).
     split; trivial.
     exists gamma.
     split.
     - rewrite <- shift_index.
       exact H0.
     - exact H1.
   Qed.

   (* S total -> S |= Delta_S (G0) -> S |= G0 *)
   Lemma G1_sat_G0_sat :
     forall tau rho phi phi',
       wfPath tau ->
       startsFrom tau rho phi ->
       (forall phi1,
          In phi1 (SynDerML phi S) ->
          SatRL (Path_i tau 1) rho (phi1 => phi')) ->
       SatRL tau rho (phi => phi').
   Proof.
   Admitted.
   
   Lemma wf_subpath : forall tau j,
                        wfPath tau ->
                        wfPath (Path_i tau j).
   Admitted.


   Lemma cover_step :
     forall gamma gamma' rho phi,
       SatML gamma rho phi ->
       (gamma =>S gamma') ->
       exists phi' alpha,
         In alpha S /\
         phi' = SynDerML' phi alpha /\
         SatML gamma' rho phi' .
   Admitted.   
                   
   Lemma alpha_to_S : forall alpha phi phi1,
                        In alpha S ->
                        phi1 = SynDerML' phi alpha ->
                        In phi1 (SynDerML phi S).
   Admitted.

   (* axiom ? *)
   Lemma rhs_vars_in_lhs :
     forall x F,
       In x (FreeVars [(lhs F); (rhs F)]) <-> In x (FreeVars [lhs F]).
   Admitted.
   
   Lemma finite_sound :
     forall n tau rho phi phi' G F,
       wfPath tau ->
       ~ isInfinite tau -> 
       In (phi => phi') F ->
       complete tau n ->
       step_star G [] F ->
       startsFrom tau rho phi ->
       total ->
       SatRL tau rho (phi => phi').
   Proof.
     induction n using custom_lt_wf_ind.
     - intros tau rho phi phi' G F WF I H' H0 H H1 T.
       apply impl_or_der with
       (phi := phi) (phi' := phi') in H.
       + destruct H as [H | H].
         * unfold SatRL.
           split.
           {simpl.
             unfold startsFrom.
             unfold complete in H0.
             destruct H0 as (H3 & gamma & H0 & H2).
             exists gamma.
             split.
             - exact H0.
             - unfold startsFrom in H1.
               destruct H1 as (gamma0 & H1 & H4).
               rewrite H0 in H1.
               inversion H1.
               assumption. }
           right.
           unfold startsFrom in H1.
           destruct H1 as (gamma & (H1 & H2)).
           exists 0, 0, gamma.
           split.
           omega.
           split.
           exact H0.
           split.
           exact H1.
           simpl.
           apply valid_impl with (phi := phi);assumption.
         * unfold complete in H0.
           destruct H0 as (I' & gamma & H2 & H3).
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
     - intros tau rho phi phi' G F WF I H' H0 H1 H2 T.
       assert (In (phi => phi') G0 \/ ~ (In (phi => phi') G0)).
       + apply classic.
       + destruct H3 as [H3 | H3].
         * assert (H4 : forall phi1,
                          In phi1 (SynDerML phi S) ->
                          SatRL (Path_i tau 1) rho (phi1 => phi')).
           {
             intros phi1 H5.
             apply H with (m := n) (G := G) (F := F).
             - omega.
             - apply wf_subpath.
               exact WF.
             - apply not_infinite_subpath.
               exact I.
             - apply first_step with (phi := phi);assumption.
             - Check complete_subpath.
               eapply complete_subpath.
               exact WF.
               assert (h : n + 1 = Datatypes.S n). omega.
               rewrite h.
               exact H0.
             - exact H1.
             - apply starts_first_step with (phi := phi).
               + exact H2.
               + exact H5.
             - exact T.
           }
           apply G1_sat_G0_sat .
           exact WF.
           exact H2.
           exact H4.
         * generalize H1.
           intros Step.
           apply helper_2 with (g := (phi => phi')) in H1.
           
           destruct H1 as (G' & (F0 & H1)).
           apply helper_1 in H1.
           destruct H1 as (G'' & (H1 & H4)).
           {
             inversion H1; clear H4.
             - simpl in H6.
               unfold SatRL.
               split.
               + simpl.
                 exact H2.
               + right.
                 unfold startsFrom in H2.
                 destruct H2 as (gamma & (H2 & H8)).
                 apply valid_impl with (phi' := phi') in H8.
                 exists (Datatypes.S n), 0, gamma.
                 simpl.
                 split.
                 * omega.
                 * split.
                   exact H0.
                   split;assumption.
                 * exact H6.
             - simpl in H7.
               unfold startsFrom in H2.
               destruct H2 as (gamma & (H2 & H2')).
               apply valid_impl with
               (gamma := gamma) (phi' := (EClos (lhs c)))
                                (phi := phi) (rho := rho) in H7.
               + unfold EClos in H7.
                 apply SatML_Exists in H7.
                 destruct H7 as (rho' & (H7 & H7')).
                 unfold total in T.
                 generalize H7'.
                 intros H7''.
                 generalize H7'.
                 intros SFC.
                 apply T in H7'.
                 destruct H7' as (gamma' & H7').
                 apply cover_step with (gamma' := gamma') in H7''.
                 destruct H7'' as (phic_1 & alpha & H9 & H10 & H11).
                 
                 assert (H12 : SatRL (Path_i tau 1) rho' (phic_1 => (rhs c))).
                 {
                   apply H with (m := n) (G := G) (F := F).
                   - omega.
                   - apply wf_subpath.
                     exact WF.
                   - apply not_infinite_subpath.
                     exact I.
                   - apply first_step with (phi := (lhs c)).
                     + destruct c.
                       simpl.
                       assumption.
                     + apply alpha_to_S with (alpha := alpha).
                       * exact H9.
                       * exact H10.
                   - apply complete_subpath.
                     + exact WF.
                     + assert (h : n + 1 = Datatypes.S n).
                       omega.
                       rewrite h.
                       exact H0.
                   - exact Step.
                   - apply starts_first_step with (phi := (lhs c)).
                     unfold startsFrom.
                     exists gamma.
                     split; trivial.
                     apply alpha_to_S with (alpha := alpha).
                     exact H9.
                     exact H10.
                   - exact T.
                 }
                 

                 unfold SatRL in H12.
                 simpl in H12.
                 destruct H12 as (H12 & [H13 | (n0 & i & gamma_n & C & H13 & H14 & H15)]).
                 * contradict H13.
                   apply not_infinite_subpath.
                   exact I.
                 * rewrite shift_index in H14.
                   assert (H16 : SatML gamma_n rho (SynDerML' phi c)).
                   {
                     unfold SynDerML'.
                     rewrite SatML_Exists.
                     exists rho'.
                     split.
                     - intros v H16.
                       apply H7.
                       rewrite <- rhs_vars_in_lhs.
                       exact H16.
                     - apply SatML_And.
                       split.
                       admit.
                       exact H15.
                   }

                   assert (H17 : SatRL (Path_i tau i) rho
                                       ((SynDerML' phi c) => phi')).
                   {
                     apply H with (m := n0) (G := G) (F := F).
                     
                     
                     
                   
                 
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
       