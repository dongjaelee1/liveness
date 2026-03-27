(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export weakestpre.
From liris.algebra Require Import ordinal_wfocm.

TODO

Class ExecCond `{SI : indexT} `{!lirisGS Λ Σ} (ς : thread_id → expr Λ → iProp Σ) i :=
  exec_cond : ∀ K e1 e2 σ Θ κ,
  LanguageCtx K → Θ !! i = Some (K e1) → prim_step i e1 σ (dom Θ) [] e2 σ ∅ →
  ∀ e', ((ς i e' ∗ state_interp σ Θ κ) ⊢ |==> (ς i (K e2) ∗ state_interp σ (<[i:=K e2]>Θ) κ)).

Section lifting.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  (* For lwp_step, enable progress and fork. *)
  Lemma lwp_step_step s i E e1 ν :
    (∀ K h n σ1 κ κs Θ,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) → history_interp h n σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_obls i G 1 -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                               ([∗ set] j ∈ dom efs, thP_obls j ∅ 1) -∗
                               ALC (|={∅,E}=>
                                      history_interp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)]) (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                      (ν e2 efs))))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    iIntros "H". iIntros (??????? ??) "SI".
    iMod ("H" with "[//] [//] SI") as "($& %& GOs& GFs& %& #REs& H)".
    iIntros "!> % % % %Step".
    iApply (mprog_step). iModIntro. iFrame "GOs GFs REs". iIntros "(GOs& Ws)".
    iApply (mphys_step _ (S n) _ _ (dom efs)). 1: eauto.
    { rewrite dom_insert_lookup_L; auto. }
    { eapply fork_thread_ids; eauto. }
    iIntros "!> !> Efs".
    iMod ("H" with "[//] GOs Ws Efs") as "H". iModIntro.
    iMod "H". iMod "H" as "[HI H]". by iFrame.
  Qed.

  Lemma lwp_lift_step s i E e1 Φ :
    (∀ K h n σ1 κ κs Θ,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) → history_interp h n σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_obls i G 1 -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                               ([∗ set] j ∈ dom efs, thP_obls j ∅ 1) -∗
                               ALC (|={∅,E}=>
                                      history_interp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)]) (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                      (lWP e2 @ s; i; E {{ Φ }}) ∗
                                      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". rewrite lwp_unfold_fix lwp_fix_unfold /lwp_pre. destruct (to_val e1) eqn:He.
    { iIntros (?????? ??) "SI". iMod ("H" $! K _ _ _ [] with "[//] [//] SI") as "[[% %] _]". done. }
    iModIntro. iApply lwp_step_step. iIntros (??????? ??) "I".
    iMod ("H" $! K with "[//] [//] I") as "(%& H)". destruct H1 as [_ H1].
    iModIntro. iSplitR; first done. iDestruct "H" as "(%& $& $& %& $& H)".
    iIntros (????). iMod ("H" with "[//]") as "H". iIntros "!> TG RWs Efs".
    iMod ("H" with "TG RWs Efs") as "H". iMod "H" as "[$ [H Efs]]". iModIntro. iFrame.
    iApply (big_sepM_impl with "Efs"). iIntros "!> %%% H". by iModIntro.
  Qed.

  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma lwp_lc_later_ord s i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s i E e Φ :
    £n n -∗ (▷^n lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

  Lemma lwp_lift_stuck i E Φ e :
    to_val e = None →
    (∀ K h n σ κ Θ, ⌜LanguageCtx K⌝ → ⌜Θ !! i = Some (K e)⌝ →
                    history_interp h n σ Θ κ ={E,∅}=∗ ⌜ stuck i e σ (dom Θ) ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    rewrite lwp_unfold /lwp_pre /lwp_step =>->.
    iIntros "H !>" (K h n σ Θ κ κs ??) "Hσ". iMod ("H" $! K with "[//] [//] Hσ") as "[% %Hirr]".
    iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  TODO
  (** Derived lifting lemmas. *)
  Lemma lwp_lift_pure_step_no_fork s i E E' e1 Φ ς e' :
    (∀ σ1 Θ, if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    ExecCond ς i →
    (|={E,E'}=>
       ς i e' ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
       ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
       (∀ σ Θ κ e2 efs, (⌜prim_step i e1 σ Θ κ e2 σ efs⌝) ={∅}=∗
          ς i (K e2) -∗
          thP_obls i G 1 -∗
          ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
          ALC (|={E',E}=> lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep EC HK0) "H".
    iApply lwp_lift_step. iIntros (K h n σ1 κ κs Θ HK HΘ) "Hσ".
    iMod ("H" $! K with "[//]") as "(Hc& (%& Tb& Gfs& %& #Rs& H))". iPoseProof (HCC with "Hc1 Hσ") as "%HC".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (e2 σ2 efs ?).
    destruct (Hstep κ σ1 (dom Θ) e2 σ2 efs HC) as (-> & <- & ->); auto.
    rewrite !map_union_empty. rewrite app_nil_l.
    iPoseProof (history_interp_step _ _ _ σ2 _ (<[i:=K e2]> Θ) with "Hσ") as "[SI ACC]".
    iMod (exec_cond _ _ _ _ _ _ HK HΘ H with "[$Hc2 $SI]") as "[Hc2 SI]".
    iMod ("ACC" with "SI") as "$".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "Hc1 Hc2 Tb Wcs [//]") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
  Qed.

  Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} i E Φ e :
    (∀ σ τ, stuck i e σ τ) →
    True ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply lwp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case (Hstuck inhabitant ∅).
    - iIntros (?????? ??) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_step {s i E1 E2 Φ} e1 :
    (∀ K h n σ1 κ κs Θ,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) → history_interp h n σ1 Θ (κ ++ κs) ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_obls i G 1 -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                               ([∗ set] j ∈ dom efs, thP_obls j ∅ 1) -∗
                               ALC (|={E2,E1}=>
                                      history_interp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)]) (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                      (from_option (λ v, lwpupd i E1 e2 (Φ v)) False (to_val e2)) ∗
                                      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply (lwp_lift_step s i E1 e1).
    iIntros (K h n σ1 κ κs Θ HK HΘ) "Hσ1". iMod ("H" $! K with "[//] [//] Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%& Tb& Gfs& %& #Rs& H)".
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (????). iMod ("H" with "[//]") as "H".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "Tb Wcs Efs") as "H".
    iMod "Hclose" as "_". iMod "H" as "($&Hq&$)".
    iModIntro. destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value_lwpupd; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s i E E' Φ C ς1 ς2} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecCond C ς1 i →
    ExecCond ς2 i →
    (|={E,E'}=>
       ς1 ∗ ς2 ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
       ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
         (ς1 -∗ ς2 -∗
          thP_obls i G 1 -∗
          ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
          ALC (|={E',E}=> lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC HCS) "H". iApply (lwp_lift_pure_step_no_fork s i E E'); eauto.
    { naive_solver. }
    iMod "H" as "($& $& %& $& $& %& $& H)". iModIntro.
    iIntros "Hc1 Hc2 Tb Wcs". iMod ("H" with "Hc1 Hc2 Tb Wcs") as ">H".
    iIntros "!> % % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_pure_step `{!Inhabited (state Λ)} (n : nat) (o : Ord.t) s i E E' e1 e2 φ Φ C ς1 ς2 :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς1 i →
    ExecCond ς2 i →
    (Nat.iter n (λ P, |={E,E'}=>
                   ς1 ∗ ς2 ∗
                   ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
                   ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                   (ς1 -∗ ς2 -∗
                    thP_obls i G 1 -∗
                    ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                    ALC (£ o ={E',E}=∗ |={E}=>m P)))
       (lWP e2 @ s; i; E {{ Φ }}))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC HCS) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { auto. }
    iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - iDestruct "Hlwp" as ">($& $& %& $& $& %& $& H)".
      iModIntro. iIntros "Hc1 Hc2 Gb Wcs". iDestruct ("H" with "Hc1 Hc2 Gb Wcs") as "H".
      iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
      iPoseProof (tlc_split with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iMod ("H" with "LC") as "H".
      iModIntro. iMod "H". iApply "IH". auto.
  Qed.

  Lemma lwp_pure_step_alt `{!Inhabited (state Λ)} (n : nat) G R (o : Ord.t) s i E E' e1 e2 φ Φ C ς1 ς2 :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς1 i →
    ExecCond ς2 i →
    ([∗ set] r ∈ R, oblP_id r) ∗
    (Nat.iter n (λ P, |={E,E'}=> ς1 ∗ ς2 ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
                                (ς1 -∗ ς2 -∗ thP_obls i G 1 -∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗ ALC (£ o ={E',E}=∗ |={E}=>m P))) (lWP e2 @ s; i; E {{ Φ }}))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec HΦ HCC HCS) "(#Rs& LWP)".
    iApply (lwp_pure_step n o _ _ E E'). 1: auto.
    iStopProof. clear Hexec. pattern n. induction n.
    { simpl. iIntros "(#Rs& LWP)". auto. }
    simpl. iIntros "(#Rs& LWP)".
    iMod "LWP" as "($& $& $& $& LWP)". iFrame "Rs".
    iIntros "!> Hc1 Hc2 TG Wcs". iMod ("LWP" with "Hc1 Hc2 TG Wcs") as "LWP". iIntros "LC".
    iApply IHn. iFrame "Rs". iMod ("LWP" with "LC") as "LWP". iModIntro. iFrame "LWP".
  Qed.

  Lemma lwp_pure_step_simple `{!Inhabited (state Λ)} n G R (o : Ord.t) s i E e1 e2 φ Φ C ς1 ς2 :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς1 i →
    ExecCond ς2 i →
    (ς1 ∗ ς2 ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 n) ∗ ([∗ set] r ∈ R, oblP_id r) ∗
     (ς1 -∗ ς2 -∗ thP_obls i G 1 -∗ ([∗ set] r ∈ R, witP_cred r n ∨ oblP_fulfilled r) -∗
      £ (o × n)%ord -∗ |={E}=>m lWP e2 @ s; i ; E {{ Φ }}))
    ⊢ |={E}=>m lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec HΦ HCC HCS) "(Hc1& Hc2& TG& Gfs& #Rs& Hlwp)".
    iApply (lwp_pure_step n o _ _ E E). 1: auto.
    iStopProof. clear Hexec. pattern n. induction n.
    { iIntros "(#Rs& Hc1& Hc2& TG& Gfs& IH)". simpl.
      iMod tlc_zero as "Hz". iPoseProof (tlc_equiv Ord.O (o × 0)%ord with "Hz") as "Hz".
      { by rewrite Jacobsthal.mult_O_r. }
      iMod (obl_check_witnesses with "Rs") as "Ws".
      iApply ("IH" with "Hc1 Hc2 TG [Ws] Hz").
      rewrite Ord.from_nat_O. done. }
    iIntros "(#Rs& Hc1& Hc2& TG& Gfs& IH)". simpl.
    iAssert (([∗ set] g ∈ G, oblP_fuel g 0 n) ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1))%I with "[Gfs]" as "[Gfs Gf]".
    { iApply (oblP_fuel_add_set). rewrite (oblP_fuel_eq_set _ _ _ (n ⊕ 1)%M (S n)%M). 1: auto.
      rewrite measure_nat_S measure_add. by rewrite Hessenberg.add_comm. }
    iModIntro. iModIntro. iFrame "Hc1 Hc2 TG Gf Rs". iIntros "Hc1 Hc2 TG RWs".
    iIntros "!> LC !>". iApply IHn. iFrame "Rs Hc1 Hc2 TG Gfs".
    iIntros "Hc1 Hc2 TG Ws LC2". iApply ("IH" with "Hc1 Hc2 TG [Ws RWs] [LC LC2]").
    { iCombine "Ws RWs" as "Ws". rewrite -big_sepS_sep. iApply (big_sepS_impl with "Ws").
      iIntros "!> %% [[Wc1 | #Gd1] [Wc2 | #Gd2]]"; auto.
      iLeft. rewrite (witP_cred_eq _ (n ⊕ Ord.one)%ord (S n)).
      - iApply witP_cred_split. iFrame.
      - rewrite -Ord.from_nat_1 -Hessenberg.add_from_nat comm. done. }
    { rewrite (tlc_equiv (o × S n)%ord ((o × n) ⊕ o)%ord).
      - rewrite tlc_split. iFrame.
      - rewrite Ord.from_nat_S Jacobsthal.mult_S comm. done. }
  Qed.

End lifting.

Global Opaque sfmupd lwpupd.
