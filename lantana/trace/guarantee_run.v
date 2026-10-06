From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_struct.
From transfinite.stepindex Require Import ordinals.

(** * The run: certification, and reading the structures off a run *)

(** ** Certification

    At a position, a run opens every registered item and produces a later-guarded record of
    each content. The contents stay in their invariants. *)
Section certification.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Local Lemma until_cert_assigned k (P R : iProp Σ) G1 G2 h n σ Θ κs g v Ω W fu o :
    Ω !! k = Some (obl_assigned fu o) →
    ▷ (P ⊨ₜ G1) -∗
    ▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R)) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (tguar G1 n ∨ tguar G2 n).
  Proof.
    iIntros (Hk) "#HG (Var& HI& MI)". iNext. iDestruct "Var" as "[[_ HP]|[Of _]]".
    - iLeft. iApply (temporal_elim P G1 with "HG [$HI $MI $HP]").
    - iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Of". iDestruct "Of" as "[#Oe #Of]".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Of]") as %H. rewrite Hk in H. done.
  Qed.

  Local Lemma until_cert_discharged k (P : iProp Σ) G2 h n σ Θ κs g v Ω W :
    Ω !! k = Some obl_discharged →
    ▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ until_disch k G2)) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n').
  Proof.
    iIntros (Hk) "(Var& HI& MI)". iNext. iDestruct "MI" as "(MHI& S& _)".
    iDestruct "Var" as "[[Oa _]|[_ R]]".
    - iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&H). rewrite Hk in H. done.
    - iDestruct "R" as "(%n'& %i'& %Ω'& #EF& #TF)".
      iDestruct (event_obl_model_history_interp_lookup with "[$MHI $EF]") as %(_& _& _& Hn& _).
      iExists n', i', Ω'. iFrame "EF TF". done.
  Qed.

  (** The certificate of one registered item. *)
  Lemma cert_of_handle n e h σ Θ κs g v Ω W :
    treg_handle e -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ cert n e.
  Proof.
    iIntros "#Hd HI MI". destruct e; simpl.
    - by iFrame.
    - iDestruct "Hd" as "(%P& %G& #SP& #Hinv& #HG)".
      iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
      iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
      iMod ("Hclose" with "HP") as "_". iModIntro. iFrame "HI MI". iExists _. iFrame "SP C".
    - iDestruct "Hd" as "(%P& %G1& %G2& #SP& #SQ& #OI& #HG)".
      iAssert (⌜∃ o, Ω !! k = Some o⌝)%I as %[o Hk].
      { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "OI". iDestruct "OI" as "[#Oe _]".
        iDestruct (osat_elem_lookup with "[$S $Oe]") as "[%H|[_ %H]]"; iPureIntro.
        - destruct H as (?&?&?). eauto.
        - eauto. }
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first done.
      destruct o.
      + iPoseProof (until_cert_assigned k P _ G1 G2 with "HG [$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iLeft.
      + iPoseProof (until_cert_discharged with "[$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iRight.
  Qed.

  Lemma certify_entries n l h σ Θ κs g v Ω W :
    treg_entries treg_handle l -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ [∗ list] pe ∈ l, cert n pe.2.
  Proof.
    iIntros "#Hl HI MI". iInduction l as [|pe l] "IH".
    - iModIntro. iFrame. done.
    - rewrite /treg_entries !big_sepL_cons. iDestruct "Hl" as "[[_ #Hd] #Hl']".
      iMod (cert_of_handle with "Hd HI MI") as "(HI& MI& #C)".
      iMod ("IH" with "Hl' HI MI") as "($& $& #Cs)". iModIntro. iFrame "C Cs".
  Qed.

  (** The check at [n] appends the marker; the marked registry's lower bound and the
      certificates of its entries form the bundle for [n]. *)
  Lemma treg_mark n l h σ Θ κs :
    reg_auth l -∗ treg_entries treg_handle l -∗ history_interp h n σ Θ κs ==∗
    history_interp h n σ Θ κs ∗ reg_auth (l ++ [(n, RMark)]) ∗
    treg_entries treg_handle (l ++ [(n, RMark)]) ∗ reg_lb (l ++ [(n, RMark)]).
  Proof.
    iIntros "Ha #Hl HI".
    iDestruct (treg_entries_bound with "Hl HI") as %Hb.
    iMod (reg_auth_append l n RMark with "Ha") as "[Ha #Hj]"; first done.
    iDestruct (history_interp_hG_event_now with "HI") as "#Hnow".
    iDestruct (reg_auth_lb with "Ha") as "#Hlb".
    iModIntro. iFrame "HI Ha Hlb".
    rewrite /treg_entries big_sepL_app big_sepL_singleton. iFrame "Hl". iSplit; [by iExists _|done].
  Qed.

  Lemma bundle_intro n l :
    last l = Some (n, RMark) →
    reg_lb l -∗ ([∗ list] pe ∈ l, cert n pe.2) -∗ bundle l n.
  Proof.
    iIntros (Hlast) "#Hlb #Cs". iEval (rewrite /cert) in "Cs". rewrite /bundle /bundle_pre.
    iFrame "Hlb". iSplit; first done. iFrame "Cs".
  Qed.

  (** The check as a whole: the bundle for [n], and the registry state back. *)
  Lemma treg_check n h σ Θ κs g v Ω W :
    treg_state -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    treg_state ∗ history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ ∃ l, bundle l n.
  Proof.
    iIntros "(%l& Ha& #Hl) HI MI".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
    iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
    iModIntro. iFrame "HI MI B". iExists _. iFrame "Ha Hl'".
  Qed.

End certification.

(** ** Reading the registered structures off a run

    For any system with the one-step property. Each loop takes the certificate of its
    structure from the bundle of each position. *)
Section loops.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Local Notation sysT := (nat → state Λ → thread_pool Λ → list (observation Λ) → iProp Σ).

  Lemma behavior_S n (τf : nat → trace_state Λ) : behavior (n, τf) → behavior (S n, τf).
  Proof. intros BEH. inversion BEH. by subst. Qed.

  Local Lemma model_interp_event_obl k o g v Ω W n D :
    Ω !! k = Some o → model_interp g v Ω W n D ⊢ event_obl v (n, Ω) k o.
  Proof. iIntros (Hk) "(MHI& _)". by iApply model_history_interp_event_obl_now. Qed.

  (** The certificate of a registered always at a position [n] after its registration
      position [r]: from the bundle, or, at [r] itself, the allocation record. *)
  Lemma bundle_always_cert l n j r N γ G :
    r ≤ n →
    bundle l n -∗ reg_idx j r (RAlways N γ) -∗ saved_ti γ (tps_ti G) -∗
    (⌜r = n⌝ -∗ ▷ tguar G n) -∗ ▷ tguar G n.
  Proof.
    iIntros (Hrn) "#B #Hj #Hγ AC". rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
    iDestruct (reg_idx_lb_pos with "Hlb Hj") as %[Hin|Hle]; first done.
    - iDestruct (big_sepL_lookup with "Cs") as "Cj"; first done. simpl.
      iDestruct "Cj" as (f) "[#Hf #Cj]". iDestruct (saved_ti_agree_fun with "Hf Hγ") as "#Heq".
      iNext. rewrite /tguar. iApply (tguar_ti_eq with "Heq Cj").
    - iApply "AC". iPureIntro. lia.
  Qed.

  (** The same for an until. *)
  Lemma bundle_until_cert l n j r N k γP γQ G1 G2 :
    r ≤ n →
    bundle l n -∗ reg_idx j r (RUntil N k γP γQ) -∗
    saved_ti γP (tps_ti G1) -∗ saved_ti γQ (tps_ti G2) -∗
    (⌜r = n⌝ -∗ ▷ (tguar G1 n ∨ tguar G2 n)) -∗
    ▷ (tguar G1 n ∨ tguar G2 n) ∨
    ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n').
  Proof.
    iIntros (Hrn) "#B #Hj #HγP #HγQ AC". rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
    iDestruct (reg_idx_lb_pos with "Hlb Hj") as %[Hin|Hle]; first done.
    - iDestruct (big_sepL_lookup with "Cs") as "Cj"; first done. iEval (simpl) in "Cj".
      iDestruct "Cj" as (fP fQ) "(#HfP& #HfQ& [Cj|Cj])".
      + iLeft. iDestruct (saved_ti_agree_fun with "HfP HγP") as "#HeqP".
        iDestruct (saved_ti_agree_fun with "HfQ HγQ") as "#HeqQ".
        iNext. rewrite /tguar. iDestruct "Cj" as "[Cj|Cj]".
        * iLeft. iApply (tguar_ti_eq with "HeqP Cj").
        * iRight. iApply (tguar_ti_eq with "HeqQ Cj").
      + iRight. iDestruct (saved_ti_agree_fun with "HfQ HγQ") as "#HeqQ".
        iNext. iDestruct "Cj" as (n' i' Ω'') "(%& #EF& Cj)". iExists n', i', Ω''. iFrame "EF".
        iSplit; first done. rewrite /tguar. iApply (tguar_ti_eq with "HeqQ Cj").
    - iLeft. iApply "AC". iPureIntro. lia.
  Qed.

  (** One iteration of a loop, in the shape of the step-indexed readings: the check gives
      the bundle and the certificate [C], whose later the shape's later strips; the step gives
      the system at [S n], the facts about the step and [c] later credits. *)
  Lemma sys_step_iter (Sys : sysT) (c : nat) h n σ Θ κs g v Ω W τf γ (C Φ : iProp Σ) :
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
    (∀ l, bundle l n -∗ ▷ C) -∗
    ▷ (∀ l σ' Θ' κs' g' v' Ω' W' γ',
       ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω' W' ∧
        hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ obls_drop (fair_sched_fun γ) (fair_sched_fun γ') Ω Ω'⌝ -∗
       bundle l n -∗ C -∗ £n c -∗
       history_interp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗ model_interp g' v' Ω' W' (S n) (dom Θ') ∗
       Sys (S n) σ' Θ' κs' -∗
       |={⊤}=> Φ) -∗
    |={⊤,∅}=> ▷ |={∅,⊤}=> |={⊤,∅}=> ALC (|={∅,⊤}=> Φ).
  Proof.
    iIntros "#ST %H Sys HC K". rewrite /sys_step /sys_step_pre.
    iMod ("ST" $! c with "[//] Sys") as (l) "[#B Step]".
    iDestruct ("HC" with "B") as "C".
    iModIntro. iNext. iMod "Step". iModIntro. iMod "Step". iModIntro.
    iApply (ALC_wand with "[K C] Step").
    iIntros ">(%σ'& %Θ'& %κs'& %g'& %v'& %Ω'& %W'& %γ'& %Hf& LC& HI& MI& Sys)".
    iApply ("K" with "[//] B C LC [$HI $MI $Sys]").
  Qed.

  (** *** The always loop *)
  Lemma always_run (Sys : sysT) N γ G j r :
    sys_step Sys -∗ reg_idx j r (RAlways N γ) -∗ saved_ti γ (tps_ti G) -∗
    ∀ h n σ Θ κs g v Ω W τf γ',
      ⌜r < n ∧ behavior (n, τf) ∧ beh_fscnt (n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω W ∧ hist_trace h τf⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      ti_always (tps_ti G) (ti_pure True) (n, τf).
  Proof.
    iIntros "#ST #Hj #Hγ" (h n σ Θ κs g v Ω W τf γ') "%H Sys".
    iLöb as "IH" forall (h n σ Θ κs g v Ω W τf γ' H).
    destruct H as (Hrn& BEH& FS& LB& HIST).
    rewrite ti_always_unfold /ti_always_pre.
    iApply (sys_step_iter Sys 0 _ _ _ _ _ _ _ _ _ _ _ (tguar G n) with "ST [%] Sys [] []").
    { split_and!; done. }
    { iIntros (l) "#B". iApply (bundle_always_cert with "B Hj Hγ []"); first lia.
      iIntros (?). lia. }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ'') "%Hstep #B #C _ Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iModIntro. iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C ST [%] B Sys"). split_and!; done.
    - unfold trace_next. simpl. iApply ("IH" with "[%] Sys"). split_and!; [lia|done..].
  Qed.

  (** The registered structures guarantee the always and the until of their stored
      readings. *)
  Lemma temporal_always_guar N P G : ⊢ alwaysI_guar N P G ⊨ₜ tps_always G.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& #A)". rewrite alwaysI_guar_unfold.
    iDestruct "A" as (j r γ st) "(#Hj& #HE& #Hγ& #Hinv& #HG& #AC)".
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    iDestruct (bundle_always_cert with "B Hj Hγ []") as "#C"; first done.
    { iIntros (->). done. }
    rewrite /= ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_". iModIntro.
    iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C ST [%] B Sys"). split_and!; done.
    - iApply (always_run with "ST Hj Hγ [%] Sys"). simpl.
      split_and!; [lia|by apply behavior_S|exact FS|done|done].
  Qed.

  Lemma temporal_always_as N P V : ⊢ alwaysI_as N P V ⊨ₜ tps_always (tps_sem V).
  Proof. apply temporal_always_guar. Qed.
  Lemma temporal_always N P : ⊢ alwaysI N P ⊨ₜ tps_always (tps_sem P).
  Proof. apply temporal_always_as. Qed.

  (** *** The until loop

      Once the obligation is discharged, the record of the right formula at the current
      position is at hand: step, and decide with it. *)
  Lemma until_run_discharged (Sys : sysT) (fP : tiProp Λ Σ) G2 a h n σ Θ κs g v Ω W τf γ :
    sys_step Sys -∗ tguar G2 n -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
    ti_until Ord.lt a fP (tps_ti G2) (n, τf).
  Proof.
    iIntros "#ST #TQ %H Sys". destruct H as (BEH& FS& LB& HIST).
    rewrite ti_until_unfold /ti_until_pre.
    iApply (sys_step_iter Sys 0 _ _ _ _ _ _ _ _ _ _ _ True%I with "ST [%] Sys [] []").
    { split_and!; done. }
    { by iIntros (l) "_". }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ') "%Hstep #B _ _ Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iModIntro. iLeft. iApply (tguar_elim with "TQ ST [%] B Sys"). split_and!; done.
  Qed.

  (** While the obligation is assigned, with the measure of its state at the check: the
      bundle decides which content holds at [n]; the obligation at [S n], read with a credit
      of the step, decides the continuation. *)
  Lemma until_run (Sys : sysT) N k γP γQ j r (P : iProp Σ) G1 G2 :
    sys_step Sys -∗ reg_idx j r (RUntil N k γP γQ) -∗
    saved_ti γP (tps_ti G1) -∗ saved_ti γQ (tps_ti G2) -∗
    oblP_inv N k P (until_disch k G2) -∗
    ∀ h n σ Θ κs g v Ω W τf γ fu o,
      ⌜r < n ∧ behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Ω !! k = Some (obl_assigned fu o)⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      ti_until Ord.lt (Ord.S (fair_sched_fun γ o fu)) (tps_ti G1) (tps_ti G2) (n, τf).
  Proof.
    iIntros "#ST #Hj #HγP #HγQ #OI". iIntros (h n σ Θ κs g v Ω W τf γ fu o) "%H Sys".
    iLöb as "IH" forall (h n σ Θ κs g v Ω W τf γ fu o H).
    destruct H as (Hrn& BEH& FS& LB& HIST& Hk).
    iAssert (event_obl v (n, Ω) k (obl_assigned fu o))%I as "#EA".
    { iDestruct "Sys" as "(_& MI& _)". by iApply (model_interp_event_obl with "MI"). }
    rewrite ti_until_unfold /ti_until_pre.
    iApply (sys_step_iter Sys 1 _ _ _ _ _ _ _ _ _ _ _
              ((tguar G1 n ∨ tguar G2 n) ∨
               (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n'))%I
              with "ST [%] Sys [] []").
    { split_and!; done. }
    { iIntros (l) "#B". iDestruct (bundle_until_cert with "B Hj HγP HγQ []") as "[C|C]"; first lia.
      - iIntros (?). lia.
      - iNext. by iLeft.
      - iNext. by iRight. }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ') "%Hstep #B #C LC Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& EF& TQ')]".
    - (* [P] holds at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[Of R]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply DROP; eauto. }
        unfold trace_next. simpl.
        iApply ("IH" with "[%] Sys"). split_and!; [lia|done..].
      + (* discharged during the step, at [n] (before the step) or at [S n] (after) *)
        iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' v) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' v with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare v i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "ST TQ' [%] Sys"). split_and!; [by apply behavior_S|done..].
    - (* [Q] holds at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ ST [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' v) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' v with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare v i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
  Qed.

  Lemma temporal_until_guar N k q P Q G1 G2 : ⊢ untilI_guar N k q P Q G1 G2 ⊨ₜ tps_until G1 G2.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& U)". rewrite untilI_guar_unfold /untilI_guar_pers.
    iDestruct "U" as "[Oa #U]".
    iDestruct "U" as (j r γP γQ st v Ω1 fu1 o1) "(#Hj& #HE& #HγP& #HγQ& #OI& _& _& #EA1& #AC)".
    iAssert (⌜∃ fu o, Ω !! k = Some (obl_assigned fu o)⌝)%I as %(fu& o& Hk).
    { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&?). eauto. }
    iPoseProof (model_interp_event_obl with "MI") as "#EA"; first exact Hk.
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    (* the certificate of this until for [n]: from the bundle, or its allocation records *)
    iDestruct (bundle_until_cert with "B Hj HγP HγQ []") as "#C"; first done.
    { iIntros (->). iNext. by iLeft. }
    rewrite /= /ti_exist. iExists (Ord.S (Ord.S (fair_sched_ub fu))).
    rewrite ti_until_unfold /ti_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    rewrite (ALC_credits _ _ (Ord.from_nat 1) (|={∅,⊤}=> _)%I). iApply ALC_intro. iIntros "LC".
    iMod "close" as "_".
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& #EF& #TQ')]".
    - (* [P] at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[Of R]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iAssert (⌜(fu' w≤ fu)⌝)%I as %Hfu.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EA]") as %(_& _& _& _& [_ Hle]).
          iPureIntro. specialize (Hle _ _ _ Hk Hk'). destruct Hle as [[? _]|?]; [done|by apply WFOCM.lt_le]. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply Ord.le_lt_lt; first apply fair_sched_fun_ub.
          eapply Ord.le_lt_lt; [by apply fair_sched_ub_le_proper|apply Ord.S_lt]. }
        unfold trace_next. simpl.
        iApply (until_run with "ST Hj HγP HγQ OI [%] Sys").
        split_and!; [lia|by apply behavior_S|done|done|done|done].
      + iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' i) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "ST TQ' [%] Sys").
          split_and!; [by apply behavior_S|done|done|done].
    - (* [Q] at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ ST [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' i) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
  Qed.

  Lemma temporal_until N k q P Q : ⊢ untilI N k q P Q ⊨ₜ tps_until (tps_sem P) (tps_sem Q).
  Proof. rewrite untilI_guar_canonical. apply temporal_until_guar. Qed.

  (** With valid guarantees of the contents. *)
  Lemma temporal_always_as_valid N P V G : (⊢ V ⊨ₜ G) → ⊢ alwaysI_as N P V ⊨ₜ tps_always G.
  Proof.
    intros HG. iApply (temporal_weaken _ (tps_always (tps_sem V))).
    { apply tps_always_mono. by apply tps_sem_le. }
    iApply temporal_always_as.
  Qed.
  Lemma temporal_always_valid N P G : (⊢ P ⊨ₜ G) → ⊢ alwaysI N P ⊨ₜ tps_always G.
  Proof. apply temporal_always_as_valid. Qed.
  Lemma temporal_until_valid N k q P Q G1 G2 :
    (⊢ P ⊨ₜ G1) → (⊢ Q ⊨ₜ G2) → ⊢ untilI N k q P Q ⊨ₜ tps_until G1 G2.
  Proof.
    intros HG1 HG2. iApply (temporal_weaken _ (tps_until (tps_sem P) (tps_sem Q))).
    { apply tps_until_mono; by apply tps_sem_le. }
    iApply temporal_until.
  Qed.

End loops.
