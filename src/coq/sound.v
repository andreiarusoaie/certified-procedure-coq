Require Import formula.
Require Import util.
Require Import rldefs.
Require Import definition.
Require Import List.
Require Import ext.
Require Import ListSet.
Require Import Classical.
Require Arith.
Require Import Omega.

Module Type Soundness
       (U : Utils) (F : Formulas)
       (R : RL F U) (Def : Definitions U F R)
       (E : External F U R Def).
  Import U F R Def E.
  Import ListNotations.
  Import Wf_nat.
  
  (* G0 *)
  Variable G0 : list RLFormula .

  Axiom all_G0_der :
    forall phi phi', In (phi => phi') G0 -> DerivableS phi.


  
  Inductive step (G G': list RLFormula)(g : RLFormula) : Prop :=
    | base_case : In g G -> Valid g ->
                  G' = remove RLFormula_eq_dec g G ->
                  step G G' g
    | circ_case : forall c, 
                    In g G -> In c G0 ->
                    Valid ((lhs g) => (EClos (lhs c))) ->
                    G' = (remove RLFormula_eq_dec g G)
                           ++ (SynDerRL [c] g) ->
                    step G G' g
    | deriv_case: In g G -> DerivableS (lhs g) ->
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


  
  Lemma V_or_D : forall F G phi phi',
                   step_star G [] F ->
                   In (phi => phi') F ->
                   (Valid (phi => phi') \/ DerivableS phi).
  Proof.
    intros F G phi phi' H H0.
    assert (H' : In (phi => phi') G0 \/ ~(In (phi => phi') G0)).
    - apply classic.
    - destruct H' as [H' | H'].
      + right.
        apply all_G0_der with (phi' := phi').
        assumption.
      + apply helper_2 with (g := (phi => phi')) in H.
        destruct H as (G' & (F0 & H)).
        apply helper_1 in H.
        clear G.
        destruct H as (G'' & (H & H'')).
        inversion H.
        * left.
          assumption.
        * simpl in H3.
          assert (H8 : DerivableS (lhs c)).
          apply all_G0_der with (phi' := (rhs c)).
          simpl.
          rewrite <- RL_decompose.
          assumption.
          apply prop2 in H8.
          apply prop1 with (phi := phi) in H8.
          right.
          assumption.
          assumption.
        * simpl in H2.
          right.
          assumption.
        * assumption.
        * assumption.
        * assumption.
  Qed.


  (* startsFromSymPath - def using Valid set *)
  Definition startsFromSymPathV (mu : SymPath)
             (phi : MLFormula) : Prop :=
    exists phi0,
      mu 0 = Some phi0 /\ Valid (phi0 => phi).

  
  Definition SatV (mu : SymPath)
             (phi phi' : MLFormula) : Prop :=
    startsFromSymPathV mu phi
    /\
    (isInfiniteSym mu
     \/
     exists j phi_j,
       mu j = Some phi_j /\ Valid (phi_j => phi')).

  (* Cover 2 : symb covers symb *)
  Definition scover (mu mu' : SymPath) : Prop :=
    forall i, exists phi phi',
      mu i = Some phi /\ mu' i = Some phi' /\
      Valid (phi' => phi).

  
  Lemma cover_finite_symb_path :
    forall mu' n phi0' phi0,
      mu' 0 = Some phi0' -> ValidML (ImpliesML phi0' phi0) ->
      completeSymPathFinite mu' n ->
      exists mu,
        mu 0 = Some phi0 /\ scover mu mu'/\
        completeSymPathFinite mu n.
  Admitted.

  Lemma zero_subpath : forall mu i,
                         SymPath_i mu 0 i = mu i.
    intros.
    unfold SymPath_i.
    unfold GPath_i.
    simpl.
    reflexivity.
  Qed.


  Lemma index_shift : forall mu k j o,
                        SymPath_i mu k j = o <->
                        mu (k + j) = o .
  Proof.
    intros.
    split. 
    - intros H.
      unfold SymPath_i in H.
      unfold GPath_i in H.
      assumption.
    - intros H.
      unfold SymPath_i.
      unfold GPath_i.
      assumption.
  Qed.

  Lemma infinite_subpath : forall j mu,
                             isInfiniteSym (SymPath_i mu j) ->
                             wfSymPath mu ->
                             isInfiniteSym mu.
  Proof.
    induction j.
    - intros.
      unfold isInfiniteSym in *.
      unfold isInfiniteGPath in *.
      intros i.
      rewrite <- zero_subpath.
      apply H.
    - intros mu H H'.
      apply IHj.
      + unfold isInfiniteSym in H.
        unfold isInfiniteGPath in H.
        unfold wfSymPath in H'.
        unfold wfGPath in H'.
        destruct H' as (H' & H1).
        assert (H0 : forall i, SymPath_i mu (1 + j) i <> None -> SymPath_i mu j i <> None).
        * intros i H2.
          unfold not.
          unfold not in H2.
          intros.
          apply H2.
          rewrite index_shift in *.
          apply H' with (i := j + i).
          apply Plus.plus_lt_compat_r.
          simpl.
          apply Lt.lt_n_Sn.
          assumption.
        * unfold isInfiniteSym.
          unfold isInfiniteGPath.
          intros i.
          apply H0.
          apply H.
      + assumption.
  Qed.
    
  
  Lemma first_step : forall phi phi' phi1 mu,
                       SatV ((SymPath_i mu) 1) phi1 phi' ->
                       startsFromSymPathV mu phi ->
                       wfSymPath mu ->
                       SatV mu phi phi'.
  Proof.
    intros phi phi' phi1 mu H1 H2 H3.
    unfold SatV in H1.
    destruct H1 as (H1 & H1').
    destruct H1' as [H1' | H1'].
    - apply infinite_subpath in H1'.
      unfold SatV.
      split.
      + assumption.
      + left.
        assumption.
      + assumption.
    - unfold SatV.
      split.
      + assumption.
      + right.
        destruct H1' as (j & (phi_j & (H4' & H4))).
        exists (1 + j), phi_j.
        split.
        * apply index_shift in H4'.
          assumption.
        * assumption.
  Qed.

  
        
  Lemma valid_starts_satv : forall phi phi' mu,
                              startsFromSymPathV mu phi ->
                              Valid (phi => phi') ->
                              SatV mu phi phi'.
  Proof.
    intros.
    unfold SatV.
    split.
    - assumption.
    - right.
      unfold startsFromSymPathV in H.
      destruct H as (phi0 & (H & H0')).
      exists 0, phi0.
      split.
      + assumption.
      + apply prop3 with (phi' := phi); assumption.
  Qed.      


  Lemma wf_subPath : forall mu j,
                       wfSymPath mu ->
                       wfSymPath (SymPath_i mu j).
  Proof.
    intros mu j H.
    unfold wfSymPath in *.
    unfold wfGPath in *.
    destruct H as (H & H').
    split.
    - intros i j0 H1 H2.
      apply index_shift.
      rewrite index_shift in H2.
      apply plus_lt_compat_l with (p := j) in H1.
      apply H in H1; assumption.
    - intros i H''.
      rewrite index_shift in H''.
      rewrite index_shift in H''.
      rewrite <- plus_assoc_reverse in H''.
      apply H' in H''.
      destruct H'' as (e & (e' & (H0 & (H1 & H2)))).
      exists e, e'.
      split.
      + rewrite index_shift.
        assumption.
      + rewrite index_shift.
        split.
        * rewrite <- plus_assoc_reverse.
          assumption.
        * assumption.
  Qed.
  
  Lemma helper_3 : forall mu n j,
                     completeSymPathFinite mu n ->
                     j <= n ->
                     wfSymPath mu ->
                     completeSymPathFinite (SymPath_i mu j) (n - j) .
  Proof.
    intros mu n j H H3 H4.
    unfold completeSymPathFinite in *.
    destruct H as (H & (phi & (H0 & (H1 & H2)))).
    split.
    - unfold isInfiniteSym in *.
      unfold isInfiniteGPath in *.
      apply not_all_not_ex in H.
      destruct H as (n0 & H).
      apply ex_not_not_all.
      exists (n0 - j).
      unfold not.
      intros H'.
      apply H'.
      rewrite index_shift.
      assert (H'' : j + (n0 - j) = n0).
      + apply Minus.le_plus_minus_r.
        unfold wfSymPath in H4.
        unfold wfGPath in H4.
        destruct H4 as (H4 & H4').
        assert (H5 : n < n0).
        * assert ( n < n0 \/ ~( n < n0)).
          apply classic.
          destruct H5 as [H5 | H5].
          assumption.                  
          assert (H6: n0 < n \/ n = n0).
          {
            apply Compare_dec.not_lt in H5.
            omega.
          }
          destruct H6 as [H6 | H6].
          {
            apply H4 in H6.
            rewrite H6 in H0.
            inversion H0.
            assumption.
          }
          subst n.
          rewrite H0 in H.
          inversion H.
        * apply le_lt_trans with (p := n0) in H3.
          omega.
          assumption.
      + rewrite H''.
        assumption.
    - auto. exists phi.
      split.
      + apply index_shift.
        assert (H' : j + (n - j) = n).
        * omega.
        * rewrite H'.
          assumption.
      + split.
        * assumption.
        * intros k.
          assert (H5 : exists phi', mu (j + k) = Some phi' /\ (j + k) < n /\ SDerivable phi').
          apply H2.
          destruct H5 as (phi' & (H6 & (H7 & H8))).
          exists phi'.
          split.
          apply index_shift.
          assumption.
          split.
          omega.
          assumption.
  Qed.

  Lemma startsFrom_i : forall j mu phi_j,
                         mu j = Some phi_j ->
                         startsFromSymPathV (SymPath_i mu j) phi_j.
  Proof.
    intros j mu phi_j H0.
    unfold startsFromSymPathV.
    exists phi_j.
    split.
    - apply index_shift.
      rewrite <- plus_n_O.
      assumption.
    - apply prop4.
  Qed.

  Lemma all_G_in_F : forall G F g,
                       step_star G [] F ->
                       In g G ->
                       In g F.
  Admitted.

  Lemma G1_in_Delta : forall phi phi' phi_1 mu,
                        In (phi => phi') G0 ->
                        startsFromSymPathV mu phi ->
                        mu 1 = Some phi_1 ->
                        In (phi_1 => phi') (Delta S G0).
  Admitted.

   Lemma complete_wf : forall mu n,
                         completeSymPathFinite mu n ->
                         wfSymPath mu ->
                         forall j,
                           j > n -> mu j = None.
   Admitted.

   Lemma helper_4 : forall mu n phi1,
                      completeSymPathFinite mu n ->
                      wfSymPath mu ->
                      mu 1 = Some phi1 ->
                      1 <= n.
   Proof.
     intros mu n phi1 H W H0.
     assert (H18: 1 <= n \/ ~(1 <= n)).
     apply classic.
     destruct H18 as [H18 | H18].
     - assumption.
     - apply not_le in H18.
       assert (n = 0).
       + omega.
       + clear H18.
         subst n.
         assert (H20 : mu 1 = None).
         * apply complete_wf with (n := 0).
           assumption.
           assumption.
           omega.
         * rewrite H0 in H20.
           inversion H20.
   Qed.

   Lemma wf_scover : forall mu mu',
                       wfSymPath mu ->
                       scover mu' mu ->
                       wfSymPath mu'.
   Admitted.

   
  Lemma mu_satV_phi_phi' :
    forall n mu phi phi' F,
      completeSymPathFinite mu n ->
      wfSymPath mu ->
      startsFromSymPathV mu phi ->
      In (phi => phi') F ->
      step_star (Delta S G0) [] F ->
      SatV mu phi phi'.
  Proof.

    induction n using lt_wf_ind.
    intros.
    
    unfold completeSymPathFinite in H0.
    destruct H0 as (H0 & (phi_n & (H5 & (H6 & H8)))).
    
    assert (H7 : In (phi => phi') G0 \/ ~(In (phi => phi') G0)).
    - apply classic.
    - destruct H7 as [H7 | H7].
      + case_eq n.
        * intros n0.
          subst n.
          apply V_or_D with
          (G := Delta S G0) (phi := phi) (phi' := phi')
            in H4.
          destruct H4 as [H4 | H4].
          apply valid_starts_satv; assumption.
(*          apply der_D in H2. *)
          unfold startsFromSymPathV in H2.
          destruct H2 as (phi0 & (H2 & H2')).

          rewrite H2 in H5.
          inversion H5.
          clear H5.
          subst phi0.
          contradict H6.
          assert (H5 : DerivableS phi_n).
          apply prop1 with (phi' := phi); assumption.
          apply der_D.
          assumption.
          assumption.
        * intros n0 N.
          assert (H8' : exists phi' : MLFormula, mu 1 = Some phi' /\ 1 < n /\ SDerivable phi').
          {
            apply H8 with (i := 1).
          }
          destruct H8' as (phi_1 & (H8' & (H9 & H10))).

          apply first_step with (phi1 := phi_1).
          {
            apply H with (m := n0) (F := F).
            - subst n.
              apply Lt.lt_n_Sn.
            - assert (H11 : n0 = n - 1).
              omega.
              rewrite H11.
              apply helper_3.
              + unfold completeSymPathFinite.
                split.
                assumption.
                exists phi_n.
                split.
                assumption.
                split.
                assumption.
                assumption.
              + omega.
              + assumption.
            - apply wf_subPath.
              assumption.
            - apply startsFrom_i.
              assumption.
            - apply all_G_in_F with (g := phi_1 => phi') in H4.
              + assumption.
              + apply G1_in_Delta with (phi := phi) (mu := mu);
                assumption.
            - assumption.
          }
          assumption.
          assumption.


      + assert (H4' :  step_star (Delta S G0) [] F).
        assumption.
        apply helper_2 with (g := phi => phi') in H4.
        * destruct H4 as (G & (F0 & H4)).
          apply helper_1 with (G := G) (F0 := F0) in H7.
          {
            destruct H7 as (G' & (H7 & H7')).
            inversion H7.
            - apply valid_starts_satv; assumption.
            - simpl in H11.
              unfold startsFromSymPathV in H2.
              destruct H2 as (phi0 & (H2 & H2')).
              apply cover_finite_symb_path with
              (phi0 :=  EClos (lhs c)) (n := n) in H2.
              + destruct H2 as (mu' & (H2 & (H13 & H14))).
                unfold scover in H13.
                assert (H15 : exists phi1 phi'0,
                                mu' 1 = Some phi1 /\
                                mu 1 = Some phi'0 /\
                                Valid (phi'0 => phi1)).
                * apply H13.
                * destruct H15 as (phi1' & (phi1 & (H15 & (H16 & H17)))).
                  assert (H18: SatV (SymPath_i mu' 1) phi1' (rhs c)).
                  {
                    apply H with (m := n-1) (F := F).
                    - apply plus_lt_reg_l with (p := 1).
                      rewrite le_plus_minus_r.
                      omega.
                      apply helper_4 with
                      (mu := mu) (phi1 := phi1).
                      + unfold completeSymPathFinite.
                        split.
                        * assumption.
                        * simpl. exists phi_n.
                          split.
                          assumption.
                          split; assumption.
                      + assumption.
                      + assumption.
                    - apply helper_3.
                      assumption.
                      apply helper_4 with
                      (mu := mu) (phi1 := phi1).
                      + unfold completeSymPathFinite.
                        split.
                        * assumption.
                        * simpl. exists phi_n.
                          split.
                          assumption.
                          split; assumption.
                      + assumption.
                      + assumption.
                      + apply wf_scover with (mu := mu).
                        assumption.
                        unfold scover.
                        intros i.
                        apply H13.
                    - apply wf_subPath.
                      apply wf_scover with (mu := mu).
                      assumption.
                      unfold scover.
                      intros i.
                      apply H13.
                    - apply startsFrom_i.
                      assumption.
                    -

                     (* 
                      The problem is that phi1' => (rhs c) needs to be in
                      F in order to apply the inductive hypothesis. 
                     *)
                      admit.
                    - assumption.
                  }
                  admit.
              + apply prop3 with
                (phi := phi0) (phi' := phi) (phi'' := (EClos (lhs c)))
                                   
                  in H2'.
                apply impl_V in H2'.
                assumption.
                assumption.
              + unfold completeSymPathFinite.
                split.
                * assumption.
                * auto. exists phi_n. split. assumption. split; assumption.


              
            - simpl in H10.
              inversion H7.
              unfold startsFromSymPathV in H2.
              destruct H2 as (phi0 & (H2 & H2')).
              apply cover_finite_symb_path with
              (phi0 := phi0) (n := n) in H2.
              + destruct H2 as (mu' & (H2 & (H15 & H15'))).
                unfold scover in H15.
                assert (H16 : exists phi1 phi'0,
                                mu' 1 = Some phi1 /\
                                mu 1 = Some phi'0 /\
                                Valid (phi'0 => phi1)).
                * auto.
                * destruct H16 as (phi1 & (phi_1 & (H17 & (H18 & H19)))).
                  assert (H20: SatV (SymPath_i mu 1) phi_1 phi_n).
                  {
                    apply H with (m := n-1) (F := F).
                    - apply plus_lt_reg_l with (p := 1).
                      rewrite le_plus_minus_r.
                      omega.
                      apply helper_4 with
                      (mu := mu) (phi1 := phi_1).
                      + unfold completeSymPathFinite.
                        split.
                        * assumption.
                        * simpl. exists phi_n.
                          split.
                          assumption.
                          split; assumption.
                      + assumption.
                      + assumption.
                    - apply helper_3.
                       + unfold completeSymPathFinite.
                        split.
                        * assumption.
                        * simpl. exists phi_n.
                          split.
                          assumption.
                          split; assumption.
                       + apply helper_4 with (mu := mu) (phi1 := phi_1).
                         * unfold completeSymPathFinite.
                           split.
                           assumption.
                           simpl. exists phi_n.
                           split.
                           assumption.
                           split; assumption.
                         * assumption.
                         * assumption.
                       + assumption.
                    - apply wf_subPath.
                      assumption.
                    - apply startsFrom_i.
                      assumption.
                    - unfold wfSymPath in H1.
                      unfold wfGPath in H1.
                      apply all_G_in_F with (G := (Delta S G0)).
                      assumption.

(*
                      Lemma in_Delta : forall phi phi1 phi',
                                         In phi1 (SynDerML phi S) ->
                                         In (phi1 => phi') (Delta S G0).
                      Admitted.

                      apply in_Delta with (phi := phi).
                      
                      
                      Lemma first_in_Delta : forall mu phi phi1,
                                               wfSymPath mu ->
                                               startsFromSymPathV mu phi ->
                                               mu 1 = Some phi1 ->
                                               In phi1 (SynDerML phi S).
                      Admitted.

                      apply first_in_Delta with (mu := mu).
                      assumption.
                      unfold startsFromSymPathV.
                      exists 
*)                


                      
  
End Soundness.
       