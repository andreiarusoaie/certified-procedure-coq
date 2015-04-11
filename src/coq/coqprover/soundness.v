Require Import List .
Require Import Classical.
Require Import Coq.Arith.Minus.

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




    (* lists *)
    Fixpoint in_list (x : RLFormula)
             (l : list RLFormula) : bool := 
      match l with
        | nil => false
        | y :: tl => if RLFormula_eq_dec x y
                     then true
                     else in_list x tl
      end.
    
    Fixpoint remove (x : RLFormula) (l : list RLFormula)
    : list RLFormula := 
      match l with
        | nil => nil
        | y :: tl => if RLFormula_eq_dec x y
                     then remove x tl
                     else y :: (remove x tl)
      end.
    
    Fixpoint union (l l' : list RLFormula) : list RLFormula :=
      match l with
        | nil => l'
        | x :: l'' => if (in_list x l')
                      then (union l'' l')
                      else x :: (union l'' l')
      end.
    
    Fixpoint mynth (n : nat) (l : list RLFormula) : option RLFormula :=
      match n, l with
        | 0, x :: l' => Some x
        | 0, _ => None
        | Datatypes.S m, [] => None
        | Datatypes.S m, x :: t => mynth m t
      end.
    

    Lemma app_mynth2 : forall l l' n,
                         mynth (length l + n) (l ++ l') = mynth n l'.
    Proof.
      induction l; intros l' n; simpl.
      - reflexivity.
      - apply IHl.
    Qed.






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


    
      
    (* Rstep G G' iff G' = step G *)
    Inductive Rstep : TS_Spec -> TS_Spec -> RLFormula
                      -> option RLFormula -> TS_Spec -> Prop :=
    | base_case : forall G G' G0, forall phi phi',
                    In (phi => phi') G ->
                    SatML_Model (ImpliesML phi phi') ->
                    G' = remove (phi => phi') G ->
                    Rstep G G' (phi => phi') None G0
    | circ_case : forall G G' G0, forall phi phi' phic phic', 
                    In (phi => phi') G ->
                    In (phic => phic') G0 ->
                    (phi => phi') <> (phic => phic') ->
                    SatML_Model (ImpliesML phi (ExistsML (FreeVars phic) phic)) ->
                    G' = union 
                           (remove (phi => phi') G)
                           (SynDerRL [phic => phic'] (phi => phi')) ->
                    Rstep G G' (phi => phi') (Some (phic => phic')) G0
    | deriv_case: forall G G' G0, forall phi phi',
                    In (phi => phi') G ->
                    SDerivable phi ->
                    G' = union
                           (remove (phi => phi') G)
                           (SynDerRL S (phi => phi')) ->
                    Rstep G G' (phi => phi') None G0.


    Inductive Rstep_star : TS_Spec -> TS_Spec -> list RLFormula ->
                           list (option RLFormula) -> 
                           TS_Spec -> nat -> TS_Spec -> Prop :=
    | refl : forall G0, Rstep_star [] [] [] [] G0 0 G0
    | tranz : forall G G' G'' g circ F n S1 S2 G0,
                Rstep G G'' g circ G0 ->
                Rstep_star G'' G' S1 S2 F n G0 ->
                Rstep_star G G' (S1 ++ [g]) (S2 ++ [circ]) (F ++ [g]) (Datatypes.S n) G0.

    
    Definition eliminated_at (g : RLFormula) (n : nat)
               (S1 : TS_Spec) (S2 : list (option RLFormula))
               (G0 : TS_Spec) : Prop :=
      exists G S1' S2' F' c,
        Rstep_star G [] S1' S2' F' n G0 /\
        Some g = mynth (n - 1) S1' /\
        c = nth (n - 1) S2' None /\
        S1' = firstn n S1 /\
        S2' = firstn n S2 /\
        n <= length S1 .
    
    Definition eliminated_max (g : RLFormula) (n : nat )
               (S1 : TS_Spec) (S2 : list (option RLFormula))
               (G0 : TS_Spec) : Prop :=
      eliminated_at g n S1 S2 G0 /\ forall m S1' S2', eliminated_at g m S1' S2' G0 -> m <= n .

    Definition max (g : RLFormula) (S1 : TS_Spec)
               (S2 : list (option RLFormula)) (G0 : TS_Spec) :
      {n : nat | eliminated_max g n S1 S2 G0}.
    Proof.
    Admitted.

    Definition Max (g : RLFormula)  (S1 : TS_Spec)
               (S2 : list (option RLFormula))
               (G0 : TS_Spec) : nat :=
      proj1_sig (max g S1 S2 G0).

    Definition is_circ_for (c g: RLFormula)
               (S2 : list (option RLFormula)) (G0 : TS_Spec) :=
      exists G S1' S2' n F,
        Rstep_star G [] S1' S2' F n G0 /\
        Some c = nth (n - 1) S2' None /\
        Some g = mynth (n - 1) S1' /\
        S2' = firstn n S2.

    Definition prec (S1 : list RLFormula)
               (S2 : list (option RLFormula))
               (G0 : TS_Spec) (f1 f2 : RLFormula)  :=
      Max f1 S1 S2 G0 > Max f2 S1 S2 G0 \/ (is_circ_for f1 f2 S2 G0) .


    Lemma max_less_n : forall g G0 S1 S2 F n,
                         Rstep_star G0 [] S1 S2 F n G0 ->
                         eliminated_max g (Max g S1 S2 G0) S1 S2 G0 ->
                         (Max g S1 S2 G0) <= n.
    Proof.
    Admitted.

    Lemma minus_n_0 : forall n, n - 0 = n.
    Proof.
      induction n; simpl; reflexivity.
    Qed.

    
    Lemma is_circ : forall G S0 S1 S2 S3 F1 F f n n' G0 circ phic phic',
                      Rstep_star G [] (S0 ++ [f]) (S3 ++ [circ]) (F1 ++ [f]) (Datatypes.S n') G0 ->
                      Rstep_star G0 [] S1 S2 F n G0 ->
                      length S0 = n' ->
                      length S3 = n' ->
                      S3 ++ [circ] = firstn (Datatypes.S n') S2 ->
                      Some (phic => phic') = circ ->
                      is_circ_for (phic => phic') f S2 G0.
    Proof.
      intros G S0 S1 S2 S3 F1 F f n n' G0 circ phic phic' H0 H L1 L2 L C.
      unfold is_circ_for.
      exists G, (S0 ++ [f]), (S3 ++ [circ]), (Datatypes.S n'), (F1 ++ [f]).
      split.
      - assumption.
      - split.
        + simpl.
          rewrite minus_n_0 with (n := n').
          rewrite <- L2.
          rewrite app_nth2.
          * rewrite minus_diag.
            simpl.
            assumption.
          * apply le_n.
        + split.
          * simpl.
            rewrite minus_n_0 with (n := n').
            rewrite <- plus_0_r with (n := n').
            rewrite <- L1.
            rewrite app_mynth2.
            simpl.
            reflexivity.
          * assumption.
    Qed.
    
    Lemma Sat_trans : forall phi1 phi2 phi3,
                        SatTS_S (phi1 => phi2) ->
                        SatTS_S (phi2 => phi3) ->
                        SatTS_S (phi1 => phi3).
    Proof.
    Admitted.

    Lemma Sat_delta : forall phi phi',
                        total ->
                        (forall f, In f (Delta S [phi => phi']) -> SatTS_S f) ->
                        SatTS_S (phi => phi').
    Admitted.

    
    Lemma Sat_circ : forall phi phi1 phi2,
                       SatTS_S (phi1 => phi2) ->
                       SatML_Model (ImpliesML phi (ExistsML (FreeVars phi1) phi1)) ->
                       SatTS_S (phi => (SynDerML' phi (phi1 => phi2))).
    Admitted.

    Lemma singleton_circ :
      forall f f' phic phic',
        In f' (Delta [phic => phic'] [f]) -> f' = ((SynDerML' (lhs f) (phic => phic')) => (rhs f)).
    Proof.
      intros f f' phic phic' H.
      unfold Delta in H.
      simpl in H.
      destruct H as [H | H].
      - unfold SynDerRL' in H.
        subst f'.
        reflexivity.
      - contradict H.
    Qed.


    Lemma G0_in_F : forall c G0 F S1 S2 n,
                      Rstep_star G0 [] S1 S2 F n G0 ->
                      In c G0 ->
                      In c F.
    Proof.
      intros c G0 F S1 S2 n H H'.
      induction H.
      - assumption.
      - apply IHRstep_star in H'.
        apply in_or_app.
        left.
        assumption.
    Qed.
      
    Parameter wf_prec : forall S1 S2 G0, well_founded (prec S1 S2 G0).
    Definition P (f : RLFormula) (F : TS_Spec) :=
      In f F -> SatTS_S f.




    Lemma n_steps : forall n G0 G1 F S1 S2,
                      Rstep_star G0 [] S1 S2 F n G1 ->
                      length S1 = n /\ length S2 = n.
    Proof.
      induction n; intros; inversion H.
      - simpl.
        split;reflexivity.
      - subst G G' S1 S2 F n G2.
        apply IHn in H7.
        split.
        + destruct H7 as (H7 & H7').
          assert (H' : length [g] = 1).
          simpl.
          reflexivity.
          * assert (H2 : length S0 + length [g] = Datatypes.S n0).
            rewrite H7.
            rewrite H'.
            omega.
            rewrite <- H2.
            apply app_length.
        + destruct H7 as (H7' & H7).
          assert (H' : length [circ] = 1).
          simpl.
          reflexivity.
          * assert (H2 : length S3 + length [circ] = Datatypes.S n0).
            rewrite H7.
            rewrite H'.
            omega.
            rewrite <- H2.
            apply app_length.
    Qed.


    
    Lemma Sat_impl : forall phi phi', SatML_Model (ImpliesML phi phi') -> SatTS_S (phi => phi') .
      intros phi phi' H.
      unfold SatTS_S.
      intros tau rho W C H'.
      simpl in H'.
      unfold startsFrom in H'.
      destruct H' as (gamma & (H' & H'')).
      unfold SatRL.
      left.
      split.
      - unfold startsFrom.
        simpl.
        exists gamma.
        split; assumption.
      - split.
        + assumption.
        + exists 0, gamma.
          split.
          * assumption.
          * simpl.
            apply impl_sat with (phi := phi).
            split; assumption.
    Qed.

    Lemma circ_is_prec : forall f phic phic' S1 S2 G0,
                           is_circ_for (phic => phic') f S2 G0 ->
                           prec S1 S2 G0 (phic => phic') f.
    Proof.
      intros f phic phic' S1 S2 G0 H.
      unfold prec.
      right.
      exact H.
    Qed.

    Lemma exists_max : forall G0 S1 S2 F n' f,
                         Rstep_star G0 [] S1 S2 F n' G0 ->
                         eliminated_max f (Max f S1 S2 G0) S1 S2 G0 ->
                         
                         exists G S1' S2' F' n c,
                           Rstep_star G [] S1' S2' F' n G0 /\
                           Some f = mynth (n - 1) S1' /\
                           c = nth (n - 1) S2' None /\
                           S1' = firstn n S1 /\
                           S2' = firstn n S2 /\
                           n <= n'.
    Proof.
      intros G0 S1 S2 F n' f H H'.
      unfold eliminated_max in H'.
      destruct H' as (H1 & H1').
      unfold eliminated_at in H1.
      destruct H1 as (G & (S1' & (S2' & (F' & (c & (H1 & (H2 & (H3 & H4 & (H5 & H6))))))))).
      exists G, S1', S2', F', (Max f S1 S2 G0), c.
      split.
      - assumption.
      - split.
        + assumption.
        + split.
          * assumption.
          * split.
            assumption.
            split.
            assumption.
            apply n_steps in H.
            destruct H as (H & H').
            subst n'.
            assumption.
    Qed.

    Lemma minus_Sn_1 : forall n, Datatypes.S n - 1 = n.
    Proof.
      induction n; simpl; reflexivity.
    Qed.

    Lemma Sn_1 : forall n m,
                   Datatypes.S n = m + 1 -> n = m.
    Proof.
      induction n; intros m; simpl; omega.
    Qed.
    
    Lemma elim_after1: forall G0 S1 S2 F n f S1' S2' F' n' circ c G G',
                         Rstep_star G0 [] S1 S2 F n G0 ->
                         Rstep_star G [] S1' S2' F' n' G0 ->
                         Some f = mynth (n' - 1) S1' ->
                         S1' = firstn n' S1 ->
                         Rstep G G' f circ G0 ->
                         G' = union (remove f G) (Delta [c] [f]) ->
                         Some c = circ ->
                         forall f', In f' (Delta [c] [f]) ->
                                    prec S1 S2 G0 f' f.
    Admitted.

    Lemma in_F1: forall G0 S1 S2 F n f S1' S2' F' n' circ c G G',
                         Rstep_star G0 [] S1 S2 F n G0 ->
                         Rstep_star G [] S1' S2' F' n' G0 ->
                         Some f = mynth (n' - 1) S1' ->
                         S1' = firstn n' S1 ->
                         Rstep G G' f circ G0 ->
                         G' = union (remove f G) (Delta [c] [f]) ->
                         Some c = circ ->
                         forall f', In f' (Delta [c] [f]) ->
                                    In f' F.
    Admitted.

        
    Lemma elim_after2: forall G0 S1 S2 F n f S1' S2' F' n' G G',
                         Rstep_star G0 [] S1 S2 F n G0 ->
                         Rstep_star G [] S1' S2' F' n' G0 ->
                         Some f = mynth (n' - 1) S1' ->
                         S1' = firstn n' S1 ->
                         Rstep G G' f None G0 ->
                         G' = union (remove f G) (Delta S [f]) ->
                         forall f', In f' (Delta S [f]) ->
                                    prec S1 S2 G0 f' f.
    Admitted.

    Lemma in_F2: forall G0 S1 S2 F n f S1' S2' F' n' G G',
                         Rstep_star G0 [] S1 S2 F n G0 ->
                         Rstep_star G [] S1' S2' F' n' G0 ->
                         Some f = mynth (n' - 1) S1' ->
                         S1' = firstn n' S1 ->
                         Rstep G G' f None G0 ->
                         G' = union (remove f G) (Delta S [f]) ->
                         forall f', In f' (Delta S [f]) ->
                                    In f' F.
    Admitted.
    
    Lemma mynth_len : forall f g l n n',
                        Some f = mynth (n - 1) (l ++ [g]) ->
                        length l = n' ->
                        n = Datatypes.S n' ->
                        f = g.
    Proof.
      intros f g l n n' H H1 H2.
      rewrite H2 in H.
      rewrite minus_Sn_1 with (n := n') in H.
      rewrite <- plus_0_r with (n := n') in H.
      rewrite <- H1 in H.
      rewrite app_mynth2 in H.
      simpl in H.
      inversion H.
      reflexivity.
    Qed.
    
    Lemma soundness : forall G0 F S1 S2 n,
                        total ->
                        Rstep_star G0 [] S1 S2 F n G0 ->
                        forall f, (P f F) .
    Proof.
      intros G0 F S1 S2 n T H.
      apply (well_founded_ind (wf_prec S1 S2 G0)).
      intros f H0.
      unfold P in *.
      intros H1.
      generalize (proj2_sig (max f S1 S2 G0)). intros H2.
      replace (proj1_sig (max f S1 S2 G0)) with (Max f S1 S2 G0) in H2; auto.
      assert (H' : Rstep_star G0 [] S1 S2 F n G0).
      assumption.
      apply exists_max with (f := f) in H'.
      - destruct H' as (G & (S1' & (S2' & (F' & (n' & (c & (H3 & (H4 & (H5 & (h5 & (h6 & H5'))))))))))).
        inversion H3.
        + rewrite <- H11 in H4.
          rewrite <- H8 in H4.
          simpl in H4.
          inversion H4.
        + subst G1 G' S1' S2' F' G2.
          rewrite <- H10 in H4.
          apply mynth_len with (n' := n0) in H4.
          subst g.

          inversion H6.
          * apply Sat_impl.
            assumption.
          *  subst G1 G' G2.
             assert (H3' : Rstep_star G [] (firstn n' S1) (S3 ++ [circ]) (F0 ++ [f]) n' G0).
             rewrite H11.
             assumption.
             rewrite <- H10 in H3.
             rewrite <- H13 in H3.
             rewrite H13 in H3.
             rewrite <- H11 in H3.
             rewrite <- H13 in H3.
             apply is_circ
             with (S1 := S1)
                    (S2 := S2) (F := F) (n := n)
                    (phic := phic) (phic' := phic') in H3.
             apply circ_is_prec with (S1 := S1) in H3.
             
             apply H0 in H3.

             assert (A1 : forall f',
                             In f' (Delta [phic => phic'] [f]) ->
                             prec S1 S2 G0 f' f).
             {
               apply elim_after1 with
               (F := F) (n := n) (S1' := S0 ++ [f])
                        (S2' := S3 ++ [circ])
                        (F' := F0 ++ [f])
                        (n' := n') (circ := circ)
                        (G := G) (G' := G'').
               assumption.
               rewrite <- H10 in H3'.
               assumption.
               rewrite <- H13.
               rewrite minus_Sn_1 with (n := n0).
               rewrite <- plus_0_r with (n := n0).

               assert (H' : n' = length (S0 ++ [f])).
               rewrite H10.
               rewrite firstn_length.
               apply n_steps in H.
               destruct H as (H & H').
               rewrite <- H in H5'.
               apply min_l in H5'.
               rewrite H5'.
               reflexivity.
               rewrite <- H13 in H'.
               rewrite app_length in H'.
               simpl in H'.
               apply Sn_1 in H'.
               rewrite H'.
               rewrite app_mynth2.
               simpl.
               reflexivity.
               assumption.
               assumption.
               unfold Delta.
               rewrite app_nil_r.
               rewrite <- H17.
               assumption.
               assumption.
             }

             assert (A2 : forall f',
                             SatTS_S (phic => phic') ->
                             In f' (Delta [phic => phic'] [f]) ->
                             SatTS_S (phi => phi')).
             {
               intros f' H21 H22.
               assert (H23 : f' = (SynDerML' phi (phic => phic') => phi')).
               apply singleton_circ in H22.
               subst f.
               simpl in *.
               assumption.
               apply A1 in H22.
               subst f'.
               apply Sat_circ with (phi := phi) in H21.
               apply Sat_trans with (phi2 := (SynDerML' phi (phic => phic'))). assumption.

               apply H0.
               assumption.

               apply in_F1 with (F := F) (n := n) (S1' := S0 ++ [f])
                        (S2' := S3 ++ [circ])
                        (F' := F0 ++ [f])
                        (n' := n') (circ := circ)
                        (G := G) (G' := G'')
                        (G0 := G0) (S1 := S1) (S2 := S2)
                        (f := f) (c := (phic => phic')).
               assumption.
               rewrite H10.
               assumption.
               rewrite <- H13.
               rewrite minus_Sn_1 with (n := n0).
               rewrite <- plus_0_r with (n := n0).

               assert (H' : n' = length (S0 ++ [f])).
               rewrite H10.
               rewrite firstn_length.
               apply n_steps in H.
               destruct H as (H & H').
               rewrite <- H in H5'.
               apply min_l in H5'.
               rewrite H5'.
               reflexivity.
               rewrite <- H13 in H'.
               rewrite app_length in H'.
               simpl in H'.
               apply Sn_1 in H'.
               rewrite H'.
               rewrite app_mynth2.
               simpl.
               reflexivity.
               assumption.
               assumption.
               rewrite <- H17.
               assumption.
               assumption.
               unfold Delta.
               simpl.
               left.
               rewrite <- H17.
               simpl.
               reflexivity.
               assumption.
             }

             apply A2 with
             (f' := ((SynDerML' phi (phic => phic')) => phi')).
            assumption.
            simpl.
            rewrite <- H17.
            simpl.
            unfold SynDerRL'.
            simpl.
            left.
            reflexivity.
            apply G0_in_F with (c := (phic => phic')) in H.
            assumption.
            assumption.
            assumption.
            apply n_steps in H3.
            destruct H3 as (H3 & H3'').
            symmetry in H3.
            rewrite app_length in H3.
            simpl in H3.
            apply Sn_1 in H3.
            symmetry.
            assumption.
            apply n_steps in H3.
            destruct H3 as (H3 & H3'').
            symmetry in H3''.
            rewrite app_length in H3''.
            simpl in H3''.
            apply Sn_1 in H3''.
            symmetry.
            assumption.
            
            rewrite H13.
            assumption.
            assumption.
            
          * subst G1 G'' G2.
            
            assert (A1 : forall f', In f' (Delta S [f]) -> prec S1 S2 G0 f' f).
            {
              apply elim_after2 with
              (G := G) (G' := G') (F := F) (n := n)
                       (S1' := S0 ++ [f]) (S2' := S3 ++ [circ])
                       (n' := n') (F' := F0 ++ [f]).
              assumption.
              rewrite H11, H10.
              assumption.
              rewrite <- H13.
              rewrite minus_Sn_1.
              rewrite <- plus_0_r with (n := n0).
              assert (H' : n' = length (S0 ++ [f])).
              rewrite H10.
              rewrite firstn_length.
              apply n_steps in H.
              destruct H as (H & H').
              rewrite <- H in H5'.
              apply min_l in H5'.
              rewrite H5'.
              reflexivity.
              rewrite <- H13 in H'.
              rewrite app_length in H'.
              simpl in H'.
              apply Sn_1 in H'.
              rewrite H'.
              rewrite app_mynth2.
              simpl.
              reflexivity.
              assumption.
              rewrite H14.
              rewrite H16.
              assumption.
              rewrite H15 in H14.
              unfold Delta.
              rewrite app_nil_r.
              assumption.
            }

            assert (A2 : forall f', In f' (Delta S [f]) -> SatTS_S f').
            {
              intros f' H'.
              assert (Hf : In f' (Delta S [f])).
              assumption.
              apply A1 in H'.
              apply H0 in H'.
              assumption.

              apply in_F2 with
              (n := n) (S1' := S0 ++ [f])
                       (S2' := S3 ++ [circ])
                       (F' := F0 ++ [f])
                       (n' := n') (G := G) (G' := G')
                       (G0 := G0) (S1 := S1) (S2 := S2)
                       (f := f) .
              assumption.
              rewrite H10, H11.
              assumption.
              rewrite <- H13.
              rewrite minus_Sn_1.
              rewrite <- plus_0_r with (n := n0).
              assert (H'' : n' = length (S0 ++ [f])).
              rewrite H10.
              rewrite firstn_length.
              apply n_steps in H.
              destruct H as (H & H'').
              rewrite <- H in H5'.
              apply min_l in H5'.
              rewrite H5'.
              reflexivity.
              rewrite <- H13 in H''.
              rewrite app_length in H''.
              simpl in H''.
              apply Sn_1 in H''.
              rewrite H''.
              rewrite app_mynth2.
              simpl.
              reflexivity.
              assumption.
              subst G'.
              subst circ.
              assumption.
              unfold Delta.
              rewrite app_nil_r.
              subst f.
              assumption.
              assumption.
            }

            apply Sat_delta with (phi := phi) (phi' := phi') in T.
            assumption.
            subst f.
            apply A2.
          * apply n_steps in H7.
            destruct H7 as (H7 & H7').
            assumption.
          * subst n'.
            reflexivity.
      - assumption.
    Qed.

  End RLSemantics.
  
End Soundness.
