From iris.algebra Require Import gmap_view gmap gset mono_nat excl_auth mra.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Export obligation.
From liveness Require Import bcred.

(* All following definitions in this file are internal to [fancy_updates] with the
   exception of what's in the [osatGS] module. The module [osatGS] is thus exported in
   [fancy_updates], where [osat] is only imported. *)
Module osatGS.
  Class osatGpreS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Π : Type) (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_goal : inG Σ (gmap_viewR obl_id (prodR (agreeR $ ps_propO Π) (agreeR $ (laterO (iPropO Σ)))));
        osatGpreS_state : inG Σ (gmapUR obl_id (prodUR (prodUR bcredUR mono_natUR) mono_natUR));
      }.

  Class osatGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Π : Type) (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS Π Σ;
        goal_name : gname;
        state_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} Π : gFunctors :=
    #[GFunctor (gmap_viewTRF obl_id (prodTRF (agreeTRF $ ps_propO Π) (agreeTRF $ (laterTF idTF))));
      GFunctor (gmapTRF obl_id (prodTRF (prodTRF bcredUR mono_natUR) mono_natUR))
      ].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} {Π} {Σ} : subG (osatΣ Π) Σ → (osatGpreS Π Σ).
  Proof.
    (* FIXME : solve_inG fails because it lacks support for subG (5 < args). *)
    intros;
      lazymatch goal with
      | H:subG (?xΣ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
      end;
      repeat match goal with
        | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
        end;
      repeat match goal with
        | H:subG _ _ |- _ => move : (H) ; apply subG_inG in H || clear H
        end; intros; simpl in *; try assumption; split; assumption || by apply _.
  Qed.

End osatGS.
Import osatGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG osatGpreS_goal osatGpreS_state.

Definition goal_unfold `{SI : indexT} {Σ} (R : iProp Σ) : later (iProp Σ) :=
  Next R.
Definition oblG_goal `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) (P : ps_prop Π) (R : iProp Σ) : iProp Σ :=
  own goal_name
    (gmap_view_frag i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)).
Global Typeclasses Opaque oblG_goal.
Global Instance: Params (@goal_unfold) 2 := {}.
Global Instance: Params (@oblG_goal) 10 := {}.

Definition oblG_elem `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) : iProp Σ :=
  ∃ P R, oblG_goal i P R.
Global Typeclasses Opaque oblG_elem.
Global Instance: Params (@oblG_elem) 10 := {}.

Definition oblS_idle `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN{#q} 0, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_idle.
Global Instance: Params (@oblS_idle) 10 := {}.

Definition oblS_active_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active_auth.
Global Instance: Params (@oblS_active_auth) 10 := {}.

Definition oblS_active `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ◯MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active.
Global Instance: Params (@oblS_active) 10 := {}.

Definition oblS_live `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN{#q} 0) ]} : gmap _ _).
Global Typeclasses Opaque oblS_live.
Global Instance: Params (@oblS_live) 10 := {}.

Definition oblS_done_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done_auth.
Global Instance: Params (@oblS_done_auth) 10 := {}.

Definition oblS_done `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ◯MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done.
Global Instance: Params (@oblS_done) 10 := {}.

Definition oblS_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_credit.
Global Instance: Params (@oblS_credit) 10 := {}.

Definition oblS_bound `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ} (i : obl_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit_bound a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_bound.
Global Instance: Params (@oblS_bound) 10 := {}.

Definition osat `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ}
  (Ω : obl_states) : iProp Σ :=
  locked
    (∃ (Obls : gmap positive (obl_state * (ps_prop Π * iProp Σ))%type),
        (⌜Ω = fst <$> Obls⌝) ∗
        (own goal_name
           (gmap_view_auth (DfracOwn 1)
              ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> (snd <$> Obls)))) ∗
        ([∗ map] i ↦ oQ ∈ Obls,
           match oQ with
           | (obl_init a, _) =>
               (∃ a', ⌜leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_idle i (1/2) ∗ oblS_live i (1/2))
           | (obl_live a, _) =>
               (∃ a', ⌜leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_active_auth i ∗ oblS_live i (1/2))
           | (obl_done P1, (P2, R)) =>
               (⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblS_active_auth i ∗ oblS_done_auth i)
           end)
    )%I.

Section osat.
  Context `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGS Π Σ}.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive i P : Contractive (@oblG_goal SI _ _ _ _ WF Π Σ _ i P).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_persistent i P R : Persistent (oblG_goal i P R).
  Proof. rewrite /oblG_goal. apply _. Qed.
  Global Instance oblG_elem_persistent i : Persistent (oblG_elem i).
  Proof. rewrite /oblG_elem. apply _. Qed.

  Global Instance oblS_active_persistent i : Persistent (oblS_active i).
  Proof. rewrite /oblS_active. apply _. Qed.
  Global Instance oblS_done_persistent i : Persistent (oblS_done i).
  Proof. rewrite /oblS_done. apply _. Qed.
  Global Instance oblS_bound_persistent i (a : A) : Persistent (oblS_bound i a).
  Proof. rewrite /oblS_bound. apply _. Qed.

  Local Infix "/=" := OrderedCM.eq (at level 70).
  Local Infix "/≤" := leR (at level 70).
  Local Infix "/+" := addO (at level 70).
  Local Infix "/<" := ltR (at level 70).
  Local Notation "/0" := OrderedCM.unit.

  Lemma oblS_idle_active_false i q :
    oblS_idle i q ∗ oblS_active i ⊢ False.
  Proof.
    rewrite /oblS_idle /oblS_active. iIntros "[Hi Ha]".
    iCombine "Hi Ha" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro.
    apply singleton_valid in V. rewrite pair_valid in V. destruct V as [V _].
    rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblS_active_auth_active i :
    oblS_active_auth i ⊢ oblS_active i.
  Proof.
    rewrite /oblS_active_auth /oblS_active. apply own_mono.
    apply singleton_included, option_included. right.
    do 2 eexists. split; [eauto|]. split; [eauto|]. right.
    apply prod_included. simpl. split; [|done].
    apply prod_included. split; [done | apply mono_nat_included].
  Qed.

  Lemma oblS_idle_to_active i :
    oblS_idle i 1 ⊢ |==> oblS_active_auth i.
  Proof.
    rewrite /oblS_idle /oblS_active_auth. apply own_update.
    apply singleton_update, prod_update; [|done].
    apply prod_update; [done|]. simpl. apply mono_nat_update. auto.
  Qed.

  Lemma oblS_idle_div_2 i q :
    oblS_idle i (q/2) ∗ oblS_idle i (q/2) ⊣⊢ oblS_idle i q.
  Proof.
    rewrite /oblS_idle -own_op. iSplit; iIntros "H"; iApply own_mono. 2, 4 : iFrame.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2. done.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2. done.
  Qed.

  Lemma oblS_live_done_false i q :
    oblS_live i q ∗ oblS_done i ⊢ False.
  Proof.
    rewrite /oblS_live /oblS_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro.
    apply singleton_valid in V. rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblS_done_auth_done i :
    oblS_done_auth i ⊢ oblS_done i.
  Proof.
    rewrite /oblS_done_auth /oblS_done. apply own_mono.
    apply singleton_included, option_included. right.
    do 2 eexists. split; [eauto|]. split; [eauto|]. right.
    apply prod_included. simpl. split; [done | apply mono_nat_included].
  Qed.

  Lemma oblS_live_to_done i :
    oblS_live i 1 ⊢ |==> oblS_done_auth i.
  Proof.
    rewrite /oblS_live /oblS_done_auth. apply own_update.
    apply singleton_update, prod_update; [done|].
    simpl. apply mono_nat_update. auto.
  Qed.

  Lemma oblS_live_div_2 i q :
    oblS_live i (q/2) ∗ oblS_live i (q/2) ⊣⊢ oblS_live i q.
  Proof.
    rewrite /oblS_live -own_op. iSplit; iIntros "H"; iApply own_mono. 2, 4 : iFrame.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2. done.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2. done.
  Qed.

  Lemma oblS_credit_eq i a0 a1 :
    a0 /= a1 →
    oblS_credit i a0 = oblS_credit i a1.
  Proof.
    intros EQ. rewrite /oblS_credit. by erewrite credit_eq.
  Qed.

  Lemma oblS_credit_mon i a0 a1 :
    a0 /≤ a1 →
    oblS_credit i a1 ⊢ |==> oblS_credit i a0.
  Proof.
    intros LE. rewrite /oblS_credit. apply own_update.
    apply singleton_update.
    apply prod_update; [simpl | reflexivity]. apply prod_update; [simpl | reflexivity].
    by apply credit_update.
  Qed.

  Lemma oblS_credit_split i a0 a1 :
    oblS_credit i (a0 /+ a1) ⊣⊢ oblS_credit i a0 ∗ oblS_credit i a1.
  Proof.
    rewrite /oblS_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite singleton_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite credit_split). iFrame.
  Qed.

  Lemma oblS_credit_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    oblS_credit i a2 ⊢ |==> oblS_credit i a0 ∗ oblS_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply oblS_credit_split. iApply oblS_credit_mon; done.
  Qed.

  Lemma oblS_bound_mon i a0 a1 :
    a0 /≤ a1 →
    oblS_bound i a0 ⊢ |==> oblS_bound i a1.
  Proof.
    intros LE. rewrite /oblS_bound. apply own_update.
    apply singleton_update.
    apply prod_update; [simpl | reflexivity]. apply prod_update; [simpl | reflexivity].
    by apply cmra_update_included, credit_bound_included.
  Qed.

  Lemma oblS_credit_spend i a0 a1 :
    oblS_bound i a0 ∗ oblS_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ oblS_bound i a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite singleton_op -!pair_op !left_id.
      eapply (singleton_updateP
                (λ k, ∃ a2, (k = (credit_bound a2, ε, ε)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (credit_bound a2, ε, ε)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply (prod_updateP (λ k, ∃ a2, (k = (credit_bound a2, ε)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
        { eapply (prod_updateP (λ k, ∃ a2, (k = credit_bound a2) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
          { eapply credit_spend. }
          { eapply cmra_update_updateP. reflexivity. }
          { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
        }
        { eapply cmra_update_updateP. reflexivity. }
        { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
      }
      { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma oblS_credit_induction i a P :
    oblS_bound i a ∗ □(∃ c, ⌜/0 /< c⌝ ∧ ((oblS_credit i c ==∗ P) ==∗ P)) ⊢ |==> P.
  Proof.
    iIntros "[#Hb (%c & %LTc & #HI)]".
    iStopProof. pattern a. revert a. apply (well_founded_induction WFOrderedCM.lt_wf).
    intros a IND. iIntros "[#Hb #HI]".
    iApply "HI". iIntros "Hc".
    iMod (oblS_credit_spend with "[Hb Hc]") as "(%a' & %LE & #Hb')"; [iFrame; done |].
    iClear "Hb". iApply (IND a'); [| iModIntro; iSplit; done].
    apply WFOrderedCM.lt_exists_left. exists c. split; [auto | by rewrite OrderedCM.add_comm_le ].
  Qed.

  Lemma oblG_goal_lookup (Obls : gmap positive (obl_state (Π:=Π) * (ps_prop Π * iProp Σ))) i P R :
    own goal_name
      (gmap_view_auth (DfracOwn 1)
         ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> (snd <$> Obls))) ∗
    own goal_name (gmap_view_frag i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)) ⊢
    ∃ o P' R', ⌜Obls !! i = Some (o, (P', R'))⌝ ∗ ⌜P' = P⌝ ∗ ▷ (R' ≡ R).
  Proof.
    rewrite -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (Obls !! i)=> [oQ|] /=; last first.
    { iDestruct "HQ'" as %?. done. }
    destruct oQ as (o&P'&R'). iDestruct "HQ'" as %[= <-]. iExists o, P', R'; iSplit; first done.
    rewrite prod_includedI !to_agree_includedI; simpl. iDestruct "Hincl" as "[H1 H2]".
    rewrite /goal_unfold -later_equivI. iSplit.
    - iPoseProof (internal_eq_sym with "H1") as "H1". iPoseProof (discrete_eq with "H1") as "%HG". done.
    - iPoseProof (internal_eq_sym with "H2") as "H2". done.
  Qed.

  Lemma oblG_elem_unfold i : oblG_elem i ⊢ ∃ P R, oblG_goal i P R.
  Proof. done. Qed.

  Lemma osat_oblG_elem i Ω :
    osat Ω ∗ oblG_elem i ⊢ ⌜i ∈ dom Ω⌝.
  Proof.
    rewrite /osat -!lock. iIntros "(Ho & He)". iPoseProof (oblG_elem_unfold with "He") as "(%&%&Hg)".
    iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iPoseProof (oblG_goal_lookup with "[Hoa Hg]") as "(%&%&%&%&%&_)"; [iFrame; done |].
    iPureIntro. subst. apply elem_of_dom_2 in H. set_solver.
  Qed.

  Lemma osat_obl_is_init Ω i q :
    osat Ω ∗ oblG_elem i ∗ oblS_idle i q
    ⊢ ∃ a, ⌜Ω !! i = Some (obl_init a)⌝.
  Proof.
    iIntros "(Ho & #He & Hi)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExists a. done.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & ACT & _)".
      iPoseProof (oblS_idle_active_false with "[Hi ACT]") as "%F"; [iFrame | done].
      iPoseProof (oblS_active_auth_active with "ACT") as "#D". done.
    - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & ACT & _)".
      iPoseProof (oblS_idle_active_false with "[Hi ACT]") as "%F"; [iFrame | done].
      iPoseProof (oblS_active_auth_active with "ACT") as "#D". done.
  Qed.

  Lemma osat_obl_is_live Ω i q :
    osat Ω ∗ oblG_elem i ∗ oblS_active i ∗ oblS_live i q
    ⊢ ∃ a, ⌜Ω !! i = Some (obl_live a)⌝.
  Proof.
    iIntros "(Ho & #He & #Ha & Hl)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & IDLE & _)".
      iPoseProof (oblS_idle_active_false with "[IDLE Ha]") as "%F"; [iFrame; done | done].
    - iExists a. done.
    - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & _ & DONE)".
      iPoseProof (oblS_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (oblS_done_auth_done with "DONE") as "#D". done.
  Qed.

  Lemma osat_obl_is_done Ω i P R :
    osat Ω ∗ oblG_goal i P R ∗ oblS_done i
    ⊢ ∃ P', ⌜Ω !! i = Some (obl_done P') ∧ P' ≡ P⌝.
  Proof.
    iIntros "(Ho & #He & #Hd)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [rewrite /oblG_elem; iFrame; eauto |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (oblS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (oblS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iPoseProof (oblG_goal_lookup with "[Hoa]") as "(%&%&%&%&%&_)"; [iFrame; done |].
      destruct Q. iDestruct "LU" as "[% _]". iPureIntro. subst.
      rewrite LU2 in H. inv H. rewrite LU. exists P0. done.
  Qed.

  Lemma obl_alloc Ω a P R :
    osat Ω
    ⊢ |==> ∃ i, ⌜Ω !! i = None⌝ ∗ osat (<[i:=obl_init a]>Ω) ∗
                oblG_goal i P R ∗ oblS_idle i (1/2) ∗ oblS_live i (1/2) ∗ oblS_credit i a.
  Proof.
    rewrite /osat -!lock.
    iIntros "Ho". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iMod (@own_unit _ _ _ osatGpreS_state state_name) as "HU".
    iMod ((@own_updateP _ _ _ osatGpreS_state _ state_name) with "HU") as "H".
    { apply (alloc_updateP_cofinite' ∅ ((credit_bound a ⋅ credit a : bcred (H:=WFOrderedCM.orderedCM)), ●MN 0, ●MN 0) (dom Ω)).
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      apply credit_bound_credit_valid_eq.
    }
    iSimpl. iDestruct "H" as (a' (i & NIN & Ha' & _)) "H". rewrite insert_empty in Ha'. subst a'.
    iAssert (oblS_bound i a ∗ oblS_credit i a ∗ oblS_idle i (1/2) ∗ oblS_idle i (1/2) ∗ oblS_live i (1/2) ∗ oblS_live i (1/2))%I
      with "[H]" as "(Sb & Sc & Si1 & Si2 & Sl1 & Sl2)".
    { rewrite /oblS_bound /oblS_credit /oblS_idle /oblS_live -!own_op !singleton_op -!pair_op. iSimpl.
      iApply own_mono; [|done].
      apply singleton_included, option_included. right. do 2 eexists. do 2 split; [eauto|].
      left. rewrite !left_id !right_id. rewrite -!mono_nat_auth_dfrac_op dfrac_op_own Qp.half_half.
      done.
    }
    iMod (own_update with "Hoa") as "Hoa".
    { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); [| done | done].
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iDestruct "Hoa" as "[Hoa #Hg]".
    iModIntro. iExists i. iFrame. rewrite -!lock. iSplitR.
    { iPureIntro. subst. apply not_elem_of_dom_1. set_solver. }
    iSplit; [|done].
    { iClear "Hg". iExists (<[i:=(obl_init a, (P, R))]>Obls). iSplit.
      { iPureIntro. subst. by rewrite fmap_insert. }
      iSplitL "Hoa".
      { iEval (rewrite !fmap_insert). iFrame. }
      { iApply big_sepM_insert.
        { subst. apply not_elem_of_dom_1. set_solver. }
        iFrame. done.
      }
    }
  Qed.

  Lemma osat_step_one_obl_live_live Ω i a c :
    (Ω !! i = Some (obl_live a)) →
    (/0 /< c) →
    osat Ω ∗ oblS_credit i c
    ⊢ |==> ∃ o, osat (<[i:=o]>Ω) ∗ ∀ s, ⌜obl_state_step s (obl_live a) o⌝.
  Proof.
    intros LU Hc. iIntros "(Ho & CR)".
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (obl_live a, Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    iDestruct "LU" as "(%a' & %LE & BND & ACTa & LIVE)".
    iPoseProof (oblS_credit_spend with "[BND CR]") as ">(%&%&BND)"; [by iFrame |].
    assert (LT : a2 /< a).
    { apply WFOrderedCM.lt_exists_right. exists c. split; [auto | etransitivity; eauto]. }
    iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live a2, Q))  with "[Hom ACTa LIVE BND]") as "Hom".
    { apply lookup_delete. }
    { iFrame. iExists a2. iFrame. done. }
    iModIntro. iFrame. iExists (obl_live a2). iSplit; [|done].
    assert (snd <$> Obls = (snd <$> <[i:=(obl_live a2, Q)]> (delete i Obls))).
    { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete.
      rewrite lookup_fmap. rewrite LU2. done.
    }
    rewrite -lock. iExists _. iFrame. iSplit; [|by rewrite -!H0].
    { iPureIntro. rewrite fmap_insert fmap_delete.
      rewrite -HO. simpl. symmetry. apply insert_delete_insert.
    }
  Qed.

  Lemma osat_step_one_obl_live_done Ω i P R :
    osat Ω ∗ oblS_active i ∗ oblS_live i (1/2) ∗ oblG_goal i P R ∗ ▷ R
    ⊢ |==> osat (<[i:=obl_done P]>Ω) ∗ oblS_done i.
  Proof.
    iIntros "(Ho & #Ha & Hl & #Hg & R)".
    iPoseProof (osat_obl_is_live with "[Ho Hl]") as "[% %Hlive]".
    { iFrame. rewrite /oblG_elem. iSplit; [|done]. by iExists P, R. }
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done| subst].
    iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]".
    assert (o = obl_live a).
    { rewrite lookup_fmap in Hlive. rewrite IN in Hlive. inv Hlive. done. }
    subst o.
    iDestruct "Hc" as "(%&_&_&Haa&Hl2)".
    iCombine "Hl Hl2" as "Hl". iPoseProof (oblS_live_div_2 with "Hl") as "Hl".
    iMod (oblS_live_to_done with "[$]") as "Hda".
    iPoseProof (oblS_done_auth_done with "[$]") as "#DONE".
    iModIntro. iSplitL; [|done]. iExists (<[i := (obl_done P, (P, R'))]>Obls). iSplit.
    { iPureIntro. by rewrite fmap_insert. }
    iSplitL "Hoa".
    { rewrite fmap_insert insert_id; [iFrame|]. rewrite lookup_fmap IN. done. }
    iApply (big_sepM_delete _ _ i); [apply lookup_insert |].
    iFrame. iSplitL "R".
    { iSplit; [done|]. iNext. by iRewrite "HPQ". }
    rewrite delete_insert_delete. iFrame.
  Qed.

  Lemma osat_done_open Ω i P R :
    osat Ω ∗ oblS_done i ∗ oblG_goal i P R
    ⊢ (▷ R) ∗ (▷ R -∗ osat Ω).
  Proof.
    iIntros "(Ho & #Hd & #Hg)".
    iPoseProof (osat_obl_is_done with "[Ho]") as "%Hdone"; [iFrame; eauto|].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done|].
    iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]".
    subst. assert (∃ P', o = obl_done P' ∧ P' ≡ P).
    { rewrite lookup_fmap IN in Hdone. destruct Hdone as (?&?&?). inv H. exists x. done. }
    destruct H as (P'&?&?). subst.
    iDestruct "Hc" as "(HP&HQ&Haa&Hda)". iSplitL "HQ".
    { iNext. by iRewrite "HPQ" in "HQ". }
    { iIntros "HR". iExists Obls. iSplit; [iPureIntro; done |].
      iFrame. iApply (big_sepM_delete _ _ i); [eauto |].
      iFrame. iNext. by iRewrite "HPQ".
    }
  Qed.

  Lemma osat_done_open_pers Ω i P R :
    Persistent R →
    osat Ω ∗ oblS_done i ∗ oblG_goal i P R
    ⊢ osat Ω ∗ ▷ R.
  Proof.
    iIntros (PP) "H". iPoseProof (osat_done_open with "H") as "[#HP Ho]".
    iSplitL; [|done]. iApply "Ho". done.
  Qed.

End osat.

(* Allocation of an initial obligation protocol. *)
Lemma osat_alloc `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGpreS Π Σ} : ⊢ |==> ∃ _ : osatGS Π Σ, osat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γS) "HS";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OsatG SI _ _ _ _ WF _ _ _ γG γS).
  rewrite /osat -lock.
  iExists ∅. rewrite !fmap_empty big_opM_empty. by iFrame.
Qed.
