From iris.algebra Require Import gmap_view gmap gset mono_nat excl_auth mra.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris Require Export obligation wfocm wf_structs.
From liris Require Import bcred.

Definition osat_obl_class_def `(WFA : WFOCM.pack A) `(WFB : @well_founded B RB) (ps : Type) : obl_class ps (prod A B) :=
  Build_obl_class ps (prod A B) _ (prod_lt_well_founded WFOCM.lt_wf WFB).

(* All following definitions in this file are internal to [fancy_updates] with the
   exception of what's in the [osatGS] module. The module [osatGS] is thus exported in
   [fancy_updates], where [osat] is only imported. *)
Module osatGS.
  Class osatGpreS `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_goal : inG Σ (gmap_viewR obl_id (prodR (agreeR $ (prop_ofO ps)) (agreeR $ (laterO (iPropO Σ)))));
        osatGpreS_state : inG Σ (gmapUR obl_id (prodUR (prodUR bcredUR mono_natUR) mono_natUR));
      }.

  Class osatGS `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS ps Σ;
        goal_name : gname;
        state_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) : gFunctors :=
    #[GFunctor (gmap_viewTRF obl_id (prodTRF (agreeTRF $ (prop_ofO ps)) (agreeTRF $ (laterTF idTF))));
      GFunctor (gmapTRF obl_id (prodTRF (prodTRF bcredUR mono_natUR) mono_natUR))
      ].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOCM.pack A} {ps : Type} {Σ} : subG (osatΣ ps) Σ → (osatGpreS ps Σ).
  Proof. solve_inG. Qed.

End osatGS.
Import osatGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG osatGpreS_goal osatGpreS_state.

Definition goal_unfold `{SI : indexT} {Σ} (R : iProp Σ) : later (iProp Σ) :=
  Next R.
Definition oblG_goal `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) (P : prop_of ps) (R : iProp Σ) : iProp Σ :=
  own goal_name
    (gmap_view_frag i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)).
Global Typeclasses Opaque oblG_goal.
Global Instance: Params (@goal_unfold) 2 := {}.
Global Instance: Params (@oblG_goal) 7 := {}.

Definition oblG_elem `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) : iProp Σ :=
  ∃ P R, oblG_goal i P R.
Global Typeclasses Opaque oblG_elem.
Global Instance: Params (@oblG_elem) 7 := {}.

Definition oblS_idle `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ●MN{#q} 0, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_idle.
Global Instance: Params (@oblS_idle) 7 := {}.

Definition oblS_active_auth `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ●MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active_auth.
Global Instance: Params (@oblS_active_auth) 7 := {}.

Definition oblS_active `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ◯MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active.
Global Instance: Params (@oblS_active) 7 := {}.

Definition oblS_live `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ε, ●MN{#q} 0) ]} : gmap _ _).
Global Typeclasses Opaque oblS_live.
Global Instance: Params (@oblS_live) 7 := {}.

Definition oblS_done_auth `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ε, ●MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done_auth.
Global Instance: Params (@oblS_done_auth) 7 := {}.

Definition oblS_done `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOCM.ocm), ε, ◯MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done.
Global Instance: Params (@oblS_done) 7 := {}.

Definition oblS_credit `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit a : (@bcredUR _ _ _ _ WFOCM.ocm), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_credit.
Global Instance: Params (@oblS_credit) 7 := {}.

Definition oblS_bound `{SI : indexT} `{WF : WFOCM.pack A} `{!osatGS ps Σ} (i : obl_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit_bound a : (@bcredUR _ _ _ _ WFOCM.ocm), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_bound.
Global Instance: Params (@oblS_bound) 7 := {}.

Definition osat `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps Σ} {B : Type} {RB : B → B → Prop} {WFB : well_founded RB}
  (Ω : obl_states' (osat_obl_class_def WFA WFB ps)) : iProp Σ :=
  locked
    (∃ (Obls : gmap positive (obl_state * (prop_of ps * iProp Σ))%type),
        (⌜Ω = fst <$> Obls⌝) ∗
        (own goal_name
           (gmap_view_auth (DfracOwn 1)
              ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> (snd <$> Obls)))) ∗
        ([∗ map] i ↦ oQ ∈ Obls,
           match oQ with
           | (obl_init (a, _), _) =>
               (∃ a', ⌜WFOCM.leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_idle i (1/2/2) ∗ oblS_live i (1/2/2))
           | (obl_live (a, _), _) =>
               (∃ a', ⌜WFOCM.leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_active_auth i ∗ oblS_live i (1/2/2))
           | (obl_done P1, (P2, R)) =>
               (⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblS_active_auth i ∗ oblS_done_auth i)
           end)
    )%I.

Section osat.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps Σ} `{WFB : @well_founded B RB}.

  Local Instance occ : obl_class ps (prod A B) := osat_obl_class_def WFA WFB ps.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive i P : Contractive (@oblG_goal SI _ WFA ps Σ _ i P).
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

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

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

  Lemma oblS_idle_dfrac_op i q1 q2 q :
    q = (q1 + q2)%Qp →
    oblS_idle i q1 ∗ oblS_idle i q2 ⊣⊢ oblS_idle i q.
  Proof.
    intros; subst.
    rewrite /oblS_idle -own_op. iSplit; iIntros "H"; iApply own_mono. 2, 4 : iFrame.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own. done.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own. done.
  Qed.

  Lemma oblS_idle_div_2 i q :
    oblS_idle i (q/2) ∗ oblS_idle i (q/2) ⊣⊢ oblS_idle i q.
  Proof.
    rewrite oblS_idle_dfrac_op; first done. by rewrite Qp.div_2.
  Qed.

  Lemma oblS_idle_valid i q :
    oblS_idle i q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblS_idle. iIntros "H". iPoseProof (own_valid with "H") as "%V". iPureIntro.
    rewrite singleton_valid pair_valid in V. destruct V as [V _].
    rewrite pair_valid in V. destruct V as [_ V]. apply mono_nat_auth_dfrac_valid in V.
    by apply dfrac_valid in V.
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

  Lemma oblS_live_dfrac_op i q1 q2 q :
    q = (q1 + q2)%Qp →
    oblS_live i q1 ∗ oblS_live i q2 ⊣⊢ oblS_live i q.
  Proof.
    intros; subst.
    rewrite /oblS_live -own_op. iSplit; iIntros "H"; iApply own_mono. 2, 4 : iFrame.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own. done.
    - rewrite singleton_op -!pair_op !left_id. apply singleton_included, option_included.
      right. do 2 eexists. do 2 split; [reflexivity|].
      left. rewrite -mono_nat_auth_dfrac_op dfrac_op_own. done.
  Qed.

  Lemma oblS_live_div_2 i q :
    oblS_live i (q/2) ∗ oblS_live i (q/2) ⊣⊢ oblS_live i q.
  Proof.
    rewrite oblS_live_dfrac_op; first done. by rewrite Qp.div_2.
  Qed.

  Lemma oblS_live_valid i q :
    oblS_live i q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblS_live. iIntros "H". iPoseProof (own_valid with "H") as "%V". iPureIntro.
    rewrite singleton_valid pair_valid in V. destruct V as [_ V].
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma oblS_credit_eq i a0 a1 :
    a0 /= a1 →
    oblS_credit i a0 = oblS_credit i a1.
  Proof.
    intros EQ. rewrite /oblS_credit. by erewrite credit_eq.
  Qed.

  Lemma oblS_credit_eq_list L a0 a1 :
    a0 /= a1 →
    ([∗ list] i ∈ L, oblS_credit i a0)%I ≡ ([∗ list] i ∈ L, oblS_credit i a1)%I.
  Proof.
    intros. apply big_opL_proper. intros. erewrite oblS_credit_eq; eauto.
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

  Lemma oblS_credit_split_list L a0 a1 :
    ([∗ list] i ∈ L, oblS_credit i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, oblS_credit i a0) ∗ ([∗ list] i ∈ L, oblS_credit i a1).
  Proof.
    rewrite -big_sepL_sep. iSplit; iIntros "H".
    - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblS_credit_split.
    - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblS_credit_split.
  Qed.

  Lemma oblS_credit_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    oblS_credit i a2 ⊢ |==> oblS_credit i a0 ∗ oblS_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply oblS_credit_split. iApply oblS_credit_mon; done.
  Qed.

  Lemma oblS_credit_mon_split_list L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ list] i ∈ L, oblS_credit i a2) ⊢ |==> ([∗ list] i ∈ L, oblS_credit i a0) ∗ ([∗ list] i ∈ L, oblS_credit i a1).
  Proof.
    iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblS_credit_mon_split.
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
    iStopProof. pattern a. revert a. apply (well_founded_induction WFOCM.lt_wf).
    intros a IND. iIntros "[#Hb #HI]".
    iApply "HI". iIntros "Hc".
    iMod (oblS_credit_spend with "[Hb Hc]") as "(%a' & %LE & #Hb')"; [iFrame; done |].
    iClear "Hb". iApply (IND a'); [| iModIntro; iSplit; done].
    apply WFOCM.lt_exists_left. exists c. split; [auto | by rewrite OCM.add_comm_le ].
  Qed.

  Lemma oblG_goal_lookup (Obls : gmap positive (obl_state * (prop_of ps * iProp Σ))) i P R :
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

  (* osat lemmas. *)

  Implicit Types Ω : obl_states' occ.

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
    - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & ACT & _)".
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
    - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & IDLE & _)".
      iPoseProof (oblS_idle_active_false with "[IDLE Ha]") as "%F"; [iFrame; done | done].
    - iExists a. done.
    - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & _ & DONE)".
      iPoseProof (oblS_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (oblS_done_auth_done with "DONE") as "#D". done.
  Qed.

  Lemma osat_obl_is_done Ω i (P : prop_of ps) R :
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
    - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (oblS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (oblS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iPoseProof (oblG_goal_lookup with "[Hoa]") as "(%&%&%&%&%&_)"; [iFrame; done |].
      destruct Q. iDestruct "LU" as "[% _]". iPureIntro. subst.
      rewrite LU2 in H. inv H. rewrite LU. exists P0. done.
  Qed.

  Lemma osat_obl_is_done_weak Ω i :
    osat Ω ∗ oblG_elem i ∗ oblS_done i
    ⊢ ∃ P, ⌜Ω !! i = Some (obl_done P)⌝.
  Proof.
    rewrite /oblG_elem. iIntros "(Ho & #He & #Hd)". iDestruct "He" as "(%&%&#He)".
    iPoseProof (osat_obl_is_done with "[$]") as "(%&%)". destruct H. by iExists P'.
  Qed.

  Lemma osat_obl_is_done_weak_set Ω D :
    osat Ω ∗ ([∗ set] i ∈ D, oblS_done i ∗ oblG_elem i)
    ⊢ [∗ set] i ∈ D, ⌜ ∃ P, Ω !! i = Some (obl_done P) ⌝.
  Proof.
    revert Ω. pattern D. revert D. apply set_ind.
    { solve_proper. }
    { iIntros (Ω) "[HO Hs]". rewrite big_opS_empty. done. }
    iIntros (i D NIN IH Ω) "[HO Hs]". rewrite !big_sepS_union; [|set_solver|set_solver].
    rewrite !big_sepS_singleton. iDestruct "Hs" as "[[Hi1 Hi2] Hs]".
    iPoseProof (osat_obl_is_done_weak with "[HO Hi1 Hi2]") as "[% %]"; first iFrame. iSplitR.
    - iPureIntro. exists P. done.
    - iApply IH. iFrame.
  Qed.

  Lemma osat_alloc_obl Ω a b P R :
    osat Ω
    ⊢ |==> ∃ i, ⌜Ω !! i = None⌝ ∗ osat (<[i:=obl_init (a, b)]>Ω) ∗
                oblG_goal i P R ∗ oblS_idle i (1/2 + 1/2/2)%Qp ∗ oblS_live i (1/2 + 1/2/2)%Qp ∗ oblS_credit i a ∗ oblS_bound i a.
  Proof.
    rewrite /osat -!lock.
    iIntros "Ho". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iMod (@own_unit _ _ _ osatGpreS_state state_name) as "HU".
    iMod ((@own_updateP _ _ _ osatGpreS_state _ state_name) with "HU") as "H".
    { apply (alloc_updateP_cofinite' ∅ ((credit_bound a ⋅ credit a : bcred (H:=WFOCM.ocm)), ●MN 0, ●MN 0) (dom Ω)).
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      apply credit_bound_credit_valid_eq.
    }
    iSimpl. iDestruct "H" as (a' (i & NIN & Ha' & _)) "H". rewrite insert_empty in Ha'. subst a'.
    iAssert (oblS_bound i a ∗ oblS_credit i a ∗ oblS_idle i (1/2 + 1/2/2)%Qp ∗ oblS_idle i (1/2/2)%Qp ∗ oblS_live i (1/2 + 1/2/2)%Qp ∗ oblS_live i (1/2/2)%Qp)%I
      with "[H]" as "(Sb & Sc & Si1 & Si2 & Sl1 & Sl2)".
    { rewrite /oblS_bound /oblS_credit /oblS_idle /oblS_live -!own_op !singleton_op -!pair_op. iSimpl.
      iApply own_mono; [|done].
      apply singleton_included, option_included. right. do 2 eexists. do 2 split; [eauto|].
      left. rewrite !left_id !right_id. rewrite -!mono_nat_auth_dfrac_op dfrac_op_own.
      rewrite -!Qp.add_assoc !Qp.div_2. done.
    }
    iPoseProof "Sb" as "#Sb". iMod (own_update with "Hoa") as "Hoa".
    { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); [| done | done].
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iDestruct "Hoa" as "[Hoa #Hg]".
    iModIntro. iExists i. iFrame. iFrame "Sb". rewrite -!lock. iSplitR.
    { iPureIntro. subst. apply not_elem_of_dom_1. set_solver. }
    iSplit; [|done].
    { iClear "Hg". iExists (<[i:=(obl_init (a, b), (P, R))]>Obls). iSplit.
      { iPureIntro. subst. by rewrite fmap_insert. }
      iSplitL "Hoa".
      { iEval (rewrite !fmap_insert). iFrame. }
      { iApply big_sepM_insert.
        { subst. apply not_elem_of_dom_1. set_solver. }
        iFrame. eauto.
      }
    }
  Qed.

  Lemma osat_step_one_obl_init_live Ω i a b :
    Ω !! i = Some (obl_init (a, b)) →
    osat Ω ∗ oblG_elem i ∗ oblS_idle i (1/2 + 1/2/2)%Qp
    ⊢ |==> osat (<[i:=obl_live (a, b)]>Ω) ∗ oblS_active i.
  Proof.
    iIntros (LU) "(Ho&He&Hi)". rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (obl_init (a, b), Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). simpl in *. subst t. eauto. }
    destruct LU2 as (Q&LU2). iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    iDestruct "LU" as "(%a' & %LE & BND & IDLE & LIVE)".
    iMod (oblS_idle_to_active with "[Hi IDLE]") as "Ha".
    { iApply oblS_idle_dfrac_op; [|iFrame]. by rewrite Qp.add_comm -Qp.add_assoc !Qp.div_2. }
    iPoseProof (oblS_active_auth_active with "Ha") as "#Haa".
    iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live (a, b), Q))  with "[Hom Ha LIVE BND]") as "Hom".
    { apply lookup_delete. }
    { iFrame. iExists a'. iFrame. done. }
    iModIntro. iFrame. iSplit; [|done]. iSplit.
    - iPureIntro. rewrite insert_delete_insert fmap_insert. simpl. by rewrite <- HO.
    - assert (snd <$> Obls = (snd <$> <[i:=(obl_live (a, b), Q)]> (delete i Obls))).
      { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete. rewrite lookup_fmap. by rewrite LU2. }
      by rewrite H.
  Qed.

  Lemma osat_step_one_obl_live_live Ω i a b b' c :
    (Ω !! i = Some (obl_live (a, b))) →
    (/0 /< c) →
    osat Ω ∗ oblS_credit i c
    ⊢ |==> ∃ a', osat (<[i:=obl_live (a', b')]>Ω) ∗ ∀ s, ⌜obl_state_step s (obl_live (a, b)) (obl_live (a', b'))⌝.
  Proof.
    intros LU Hc. iIntros "(Ho & CR)".
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (obl_live (a, b), Q)).
    { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). simpl in *. subst t. eauto. }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    iDestruct "LU" as "(%a' & %LE & BND & ACTa & LIVE)".
    iPoseProof (oblS_credit_spend with "[BND CR]") as ">(%&%&BND)"; [by iFrame |].
    assert (LT : a2 /< a).
    { apply WFOCM.lt_exists_right. exists c. split; [auto | etransitivity; eauto]. }
    iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live (a2, b'), Q))  with "[Hom ACTa LIVE BND]") as "Hom".
    { apply lookup_delete. }
    { iFrame. iExists a2. iFrame. done. }
    iModIntro. iFrame. iExists a2. iSplit.
    - assert (snd <$> Obls = (snd <$> <[i:=(obl_live (a2, b'), Q)]> (delete i Obls))).
      { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete.
        rewrite lookup_fmap. rewrite LU2. done.
      }
      rewrite -lock. iExists _. iFrame. iSplit; [|by rewrite -!H0].
      { iPureIntro. rewrite fmap_insert fmap_delete.
        rewrite -HO. simpl. symmetry. apply insert_delete_insert.
      }
    - iIntros. iPureIntro. simpl. by econstructor 1.
  Qed.

  Lemma osat_step_one_obl_live_done Ω i P R :
    osat Ω ∗ oblS_active i ∗ oblS_live i (1/2 + 1/2/2) ∗ oblG_goal i P R ∗ ▷ R
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
    destruct a. iDestruct "Hc" as "(%&_&_&Haa&Hl2)".
    iCombine "Hl Hl2" as "Hl". iPoseProof (oblS_live_dfrac_op _ _ _ 1 with "Hl") as "Hl".
    { by rewrite -Qp.add_assoc !Qp.div_2. }
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

  Lemma osat_progress Ω (L : list obl_id) (F : obl_id → B → Prop) (R : obl_id → B → Prop) :
    osat Ω ∗ ([∗ map] i ↦ o ∈ Ω, match o with
                                 | obl_live (a, b) =>
                                     (if decide (i ∈ L)
                                      then (∃ c, ⌜ /0 /< c ⌝ ∧ oblS_credit i c ∧ ⌜ ∃ b', F i b' ⌝)
                                      else (⌜ ∃ b', RB b' b ∧ R i b' ⌝))
                                 | _ => True
                                 end)
    ⊢ |==> ∃ Ω', osat Ω' ∗ (⌜ obl_states_progress Ω Ω' ⌝) ∗
                 (⌜ map_Forall (λ i o, match o with
                                       | obl_live (a, b) => (if decide (i ∈ L) then F i b else R i b) | _ => True end) Ω' ⌝).
  Proof.
    rewrite /osat -!lock. iIntros "[(%Obls & %HO & Hoa & Hom) HM]".
    iEval (rewrite HO) in "HM". iPoseProof (big_sepM_fmap fst _ Obls with "HM") as "HM".
    iCombine "Hom HM" as "HM". iPoseProof (big_sepM_sep with "HM") as "HM".
    iAssert (|==> [∗ map] k↦x ∈ Obls,
               (let (y, y0) := (x : obl_state * (prop_of ps * iProp Σ)) in
                match y with
                | obl_init (a, _) =>
                    (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblS_bound k a' ∗ oblS_idle k (1/2/2) ∗ oblS_live k (1/2/2))
                | obl_live (a, b) =>
                    (if decide (k ∈ L)
                     then (∃ a0, ⌜ a0 /< a ⌝ ∗ ∃ a' : A, ⌜a' /≤ a0⌝ ∗ oblS_bound k a' ∗ oblS_active_auth k ∗ oblS_live k (1/2/2) ∧ ⌜ ∃ b', F k b' ⌝)
                     else ((∃ a' : A, ⌜a' /≤ a⌝ ∗ oblS_bound k a' ∗ oblS_active_auth k ∗ oblS_live k (1/2/2)) ∗ ⌜ ∃ b', RB b' b ∧ R k b' ⌝))
                | obl_done P1 => (let (P2, R) := y0 in ⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblS_active_auth k ∗ oblS_done_auth k)
                end))%I with "[HM]" as ">HM".
    { iApply big_sepM_bupd. iApply (big_sepM_impl with "HM"). iIntros "!>" (?? ?) "[H1 H2]".
      destruct x as (o&p&P). simpl. destruct o; [done | | done].
      destruct a as (a&b). iDestruct "H1" as "(%&%&Hb&Haa&Hl)". destruct (decide (k ∈ L)).
      - iDestruct "H2" as "(%&%&Hc&HF)".
        iMod (oblS_credit_spend with "[Hb Hc]") as "(%&%&Hb)"; first iFrame.
        iModIntro. iFrame. iExists a2. iSplit; [|done]. iPureIntro.
        apply WFOCM.lt_exists_right. exists c. split; [auto|]. by etransitivity.
      - iDestruct "H2" as %[b' Hb']. iModIntro. iFrame. iPureIntro. split; first done. eauto.
    }
    iAssert (|==> ∃ Obls', ([∗ map] k ↦ x ∈ (Obls' : gmap positive (obl_state * (prop_of ps * iProp Σ))),
                              let (y, y0) := (x : obl_state * (prop_of ps * iProp Σ)) in
                              match y with
                              | obl_init (a, _) =>
                                  (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblS_bound k a' ∗ oblS_idle k (1/2/2) ∗ oblS_live k (1/2/2))
                              | obl_live (a, _) =>
                                  (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblS_bound k a' ∗ oblS_active_auth k ∗ oblS_live k (1/2/2))
                              | obl_done P1 => (let (P2, R) := y0 in ⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblS_active_auth k ∗ oblS_done_auth k)
                              end) ∗
                           (⌜ snd <$> Obls = snd <$> Obls' ⌝) ∗
                           (⌜ (fst <$> Obls) ↪ₚ (fst <$> Obls')⌝) ∗
                           (⌜ map_Forall (λ i o, match o with | obl_live (a, b) => (if decide (i ∈ L) then F i b else R i b) | _ => True end) (fst <$> Obls') ⌝)
            )%I with "[HM]" as ">HM".
    { clear Ω HO. iStopProof. pattern Obls. revert Obls. apply map_ind.
      { iIntros "_". iExists ∅. rewrite big_sepM_empty. iPureIntro. split; first auto. split; first done.
        rewrite !fmap_empty. split; [|done]. intros. apply map_Forall2_empty.
      }
      intros i (o&P&Q) Obls Hlu IH. iIntros "H". iDestruct (big_sepM_insert _ _ _ _ Hlu with "H") as "[H HM]".
      iDestruct (IH with "HM") as ">(%&HM&%Hd&%Hp&%Hf)". clear IH.
      assert (Hdom : dom Obls = dom Obls').
      { rewrite <- (dom_fmap_L snd Obls), <- (dom_fmap_L snd Obls'). by rewrite Hd. }
      assert (Hlu2 : Obls' !! i = None).
      { apply not_elem_of_dom. apply not_elem_of_dom in Hlu. set_solver. }
      destruct o.
      - iModIntro. iExists (<[i:=(obl_init a, (P, Q))]>Obls'). iSplitL.
        + iApply big_sepM_insert; first done. iFrame.
        + iPureIntro. repeat split.
          * rewrite !fmap_insert. rewrite Hd. done.
          * rewrite !fmap_insert. apply map_Forall2_insert.
            { by rewrite lookup_fmap Hlu. }
            { by rewrite lookup_fmap Hlu2. }
            simpl. split; auto.
          * rewrite fmap_insert. apply map_Forall_insert.
            { by rewrite lookup_fmap Hlu2. }
            split; auto. done.
      - destruct a as [a b]. case_decide.
        { iDestruct "H" as "(%&%&%&%&Hb&Hi&Hl&%)". destruct H2.
          iMod (oblS_bound_mon _ _ _ H1 with "Hb") as "Hb".
          iModIntro. iExists (<[i:=(obl_live (a0, x), (P, Q))]>Obls'). iSplitL.
          - iApply big_sepM_insert; first done. by iFrame.
          - iPureIntro. repeat split.
            + rewrite !fmap_insert. by rewrite Hd.
            + rewrite !fmap_insert. simpl. apply map_Forall2_insert.
              { by rewrite lookup_fmap Hlu. }
              { by rewrite lookup_fmap Hlu2. }
              simpl; split; auto. by econstructor 1.
            + rewrite fmap_insert. apply map_Forall_insert.
              { by rewrite lookup_fmap Hlu2. }
              split; auto. simpl. case_decide; auto. set_solver.
        }
        { iDestruct "H" as "((%&%&Hb&Ha&Hl)&%)". destruct H1 as [b1 Hb1].
          iModIntro. iExists (<[i:=(obl_live (a, b1), (P, Q))]>Obls'). iSplitL.
          - iApply big_sepM_insert; first done. by iFrame.
          - iPureIntro. repeat split.
            + rewrite !fmap_insert. by rewrite Hd.
            + rewrite !fmap_insert. simpl. apply map_Forall2_insert.
              { by rewrite lookup_fmap Hlu. }
              { by rewrite lookup_fmap Hlu2. }
              simpl; split; auto. destruct Hb1. econstructor 2; auto.
            + rewrite fmap_insert. apply map_Forall_insert.
              { by rewrite lookup_fmap Hlu2. }
              split; auto. simpl. destruct Hb1. case_decide; done.
        }
      - iModIntro. iExists (<[i:=(obl_done P0, (P, Q))]>Obls'). iSplitL.
        + iApply big_sepM_insert; first done. iFrame.
        + iPureIntro. repeat split.
          * rewrite !fmap_insert. rewrite Hd. done.
          * rewrite !fmap_insert. apply map_Forall2_insert.
            { by rewrite lookup_fmap Hlu. }
            { by rewrite lookup_fmap Hlu2. }
            simpl. split; auto.
          * rewrite fmap_insert. apply map_Forall_insert.
            { by rewrite lookup_fmap Hlu2. }
            split; auto. done.
    }
    iDestruct "HM" as "(%&HM&%&%&%)". iModIntro. iExists (fst <$> Obls'). rewrite -lock. iSplitL.
    - iExists Obls'. iSplit; first done. rewrite <-H. iFrame.
    - iPureIntro. split; simpl; auto. intros. subst Ω. done.
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
Lemma osat_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGpreS ps Σ} `{WFB : @well_founded B RB} :
  ⊢ |==> ∃ _ : osatGS ps Σ, osat (WFB:=WFB) ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γS) "HS";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OsatG SI _ WFA _ _ _ γG γS).
  rewrite /osat -lock.
  iExists ∅. rewrite !fmap_empty big_opM_empty. by iFrame.
Qed.
