From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Module Flag.

  Definition set_flag : val :=
    λ: "x", "x" <- #1.

  Definition wait_flag : val := 
    rec: "wait" "x" :=
      let: "n" := !"x" in
      if: "n" = #1
      then #()
      else "wait" "x".

End Flag.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (iModIntro; lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (iModIntro; lwp_pure; post_lwp_lc n).

  Let N := nroot.@ "message_passing".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".
  Let Nl := N.@ "label".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  Definition flag_inv_tf (l : loc) (k : oid) : tf Σ :=
    ⟨witP_layer k 0⟩ ∗
    tf_always Na (((tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1)) ∨ (⟨oblP_fulfilled k⟩ ∗ (l ↦ #1)))).

  Definition flag_inv (l : loc) (k : oid) : iProp Σ :=
    (witP_layer k 0) ∗
    ⟦tf_always Na (((tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1)) ∨ (⟨oblP_fulfilled k⟩ ∗ (l ↦ #1))))⟧ₗ.

  (** The main proofs. *)
  Global Instance flag_inv_persistent l k : Persistent (flag_inv l k).
  Proof. rewrite /flag_inv. tf_red. apply _. Qed.

  Lemma flag_inv_tf_red l k : ⟦flag_inv_tf l k⟧ₗ = flag_inv l k.
  Proof. rewrite /flag_inv /flag_inv_tf. tf_red. auto. Qed.

  Lemma set_flag_spec :
    ⊢ ∃ μ, ∀ lc i j l G g K k,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ∃ ℓ, ogP_fuel g ℓ μ) ∗
         ogP_obls j g 0 K ∗ ⌜ k ∈ K ⌝ ∗
         (* The other half of the until ownership for the pointsto. *)
         ⟦tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1)⟧ₗ ∗
         flag_inv l k }}}
      Flag.set_flag #l @ i
    l{{{ RET #(); £ lc ∗ thP_groups i G ∗ ogP_obls j g 0 (K ∖ {[k]}) }}}.
  Proof.

  TODO

    iExists 10. iIntros (i l Φ) "!> HP HΦ".
    iDestruct "HP" as "(%&%&%& %Nek& #Hmp& Hup& Hul& TG& Gg& Gf)".
    rewrite /mp /mp_tf. do 2 tf_red. iDestruct "Hmp" as "((#Ok& #Wlk)& #Hmp)".
    rewrite /writer /=.
    iPoseProof (ogP_fuels_init {[g]} 10 with "[Gf]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, 10. iSplitR; first eauto. iIntros "TG GF _ LC".
    iPoseProof (ogP_fuels_add 8 1 with "GF") as "[GF GF1]". 1: lia.
    lwp_bind (Store _ _).
    iModIntro.
    iInv "Hmp" as "mp". iDestruct "mp" as "[mp | mp]"; cycle 1.
    { iDestruct "mp" as "[>mp _]". iEval (rewrite tf_until_logic) in "Hup". iDestruct "Hup" as "[Oak _]".
      iPoseProof (oblP_assigned_fulfilled_false with "Oak mp") as "%". done. }
    replace 10 with (9 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iCombine "Hup mp" as "mp".
    iMod (tf_until_fulfill with "mp") as "mp".
    { apply N_subseteq_1. }
    replace 9 with (8 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "mp" as "[Ptrl ACCmp]".
    iApply lwp_sfmupd. iEval (rewrite tf_atomic_logic) in "Ptrl".
    iApply (lwp_store _ ∅ 0 with "[$Ptrl $TG $GF1]"). 1: done.
    iIntros "((_& TG& _)& Ptrl)".
    iMod ("ACCmp" $! _) as "ACCmp".
    iApply sfmupd_fupd_acc. iMod ("ACCmp" with "Ptrl") as "ACCmp".
    iModIntro. 
    iPoseProof ("ACCmp" with "[] Gg") as "ACCmp".
    { iPureIntro. set_solver. }
    replace 8 with (7 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("ACCmp" $! _) as "ACCmp". iIntros "!> !>". iMod "ACCmp" as "(Ptrl& Gg& #Ofk)".
    iIntros "!> !>". iSplitL "Ptrl".
    { iNext. iRight. iFrame. eauto. }
    replace ({[k; kl]} ∖ {[k]} : gset _) with ({[kl]} : gset _) by set_solver.
    do 2 lwp_pure_one.
    iApply lwpupd_label. iIntros "PL".
    iApply sfmupd_fupd_acc.
    iMod (tf_until_fulfill with "Hul") as "Hul". 1: set_solver.
    iModIntro.
    iEval (replace 7 with (6 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "Hul" as "[_ Hul]". iMod ("Hul" $! _) as "Hul".
    iMod ("Hul" with "[PL]") as "Hul".
    { iNext. tf_red. iExists _. tf_red. iEval (rewrite tf_atomic_logic). iFrame. done. }
    iPoseProof ("Hul" with "[] Gg") as "Hul".
    { iPureIntro. set_solver. }
    iEval (replace 6 with (5 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("Hul" $! _) as "Hul". iModIntro. iMod "Hul" as "(PL& Gg& #OFkl)".
    tf_red. iDestruct "PL" as "(%& PL)". tf_red. iDestruct "PL" as "(PL& %)". subst a.
    iModIntro. iFrame "PL".
    replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
    iMod (group_delete with "TG Gg") as "TG".
    replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ogid) by set_solver.
    iModIntro. lwp_pure. simpl.
    iFrame "TG". iExists 1, ∅, 0. iSplitR; first eauto. iIntros "TG _ _ _".
    iModIntro.
    lwp_finish.
    iApply "HΦ". rewrite /lift_term. iMod (thread_terminate with "TG") as "$". done.
  Qed.

  Lemma mp_reader_spec :
    ⊢ ∃ m, ∀ i l,
    l{{{ ∃ g k kl, mp k l ∗
                   ⟦tf_eventually Nl kl false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝)⟧ₗ ∗
                   thP_groups i {[g]} ∗
                   ogP_obls i g 1 {[kl]} ∗
                   ogP_fuel g 1 m}}}
                   (* ogP_fuel g 1 ((1 × ▽) ⊕ 1)%M}}} *)
      reader #l @ i
    l{{{ v, RET v; lift_term i fork_post v }}}.
  Proof.
    iExists ((1 × ▽) ⊕ 1)%M. iIntros (i l Φ) "!> HP HΦ".
    iDestruct "HP" as "(%&%&%& #Hmp& Hul& TG& Gg& Fg)".
    rewrite /reader /=.
    rewrite /mp /mp_tf. do 2 tf_red. iDestruct "Hmp" as "((#Ok& #Wlk)& #Hmp)".
    iPoseProof (ogP_fuel_add with "Fg") as "[WFg Fg]".
    (* Liveness induction *)
    iPoseProof (wit_fuels_init with "Wlk") as "(%& Wf0)".
    iMod (wit_fuels_add _ _ _ _ g 1 1 with "Wf0 WFg") as "Wf".
    { apply ordArith.lt_from_nat. lia. }
    iClear "Wf0". iInduction α as [α IH] using WFOCM.ind.
    iMod (ogP_fuel_extend _ 0 1 (10)%M with "Fg") as "Fg".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (ogP_fuels_init {[g]} with "[Fg]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    lwp_rec. simpl.
    iFrame "TG GF". iExists ∅, 100. iSplitR; first eauto. iIntros "TG GF _ LC".
    lwp_bind (Load _).
    iModIntro.
    iInv "Hmp" as "mp". iDestruct "mp" as "[mp | mp]".
    - (* Induction case. *)
      replace 100 with (99 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
      iApply (lwp_lc_later with "LC1"). iNext.
      iEval (rewrite tf_until_logic) in "mp". iDestruct "mp" as "(Oak& #OIk)".
      iMod (oblP_inv_acc_assigned with "OIk") as "H".
      1: apply N_subseteq_1.
      iDestruct ("H" with "Oak") as "[H HACC]". iDestruct "H" as ">(Oak& Oak'& Ptrl)".
      iEval (rewrite tf_atomic_logic) in "Ptrl".
      iPoseProof (ogP_fuels_add 8 1 with "GF") as "[GF GF1]". 1: lia.
      iApply (lwp_load _ ({[k]} : gset _) 0 with "[$TG $Ptrl $GF1]").
      { iApply big_sepS_singleton. auto. }
      iIntros "[(_& TG& Rs) Ptrl]".
      iEval (rewrite big_sepS_singleton) in "Rs". iDestruct "Rs" as "[Wck | #Ofk]"; cycle 1.
      { iPoseProof (oblP_assigned_fulfilled_false with "Oak Ofk") as "%". done. }
      iMod ("HACC" with "[Oak' Ptrl]") as "_".
      { iModIntro. iApply oblP_variant_unfold. iLeft. iFrame. }
      iModIntro. iModIntro. iSplitL "Oak".
      { iNext. rewrite tf_until_logic. iLeft. iFrame. eauto. }
      do 4 lwp_pure_one.
      iModIntro.
      iMod (wit_fuels_decr with "Wf Wck") as "(%& %LTα& Wf'& Fkl')".
      rewrite big_sepM_singleton.
      iApply ("IH" $! α0 LTα with "Hul TG Gg HΦ Fkl' Wf'").
    - (* k is fulfilled. *)
      iDestruct "mp" as ">(#Ofk& Ptrl)".
      iEval (rewrite tf_atomic_logic) in "Ptrl".
      iPoseProof (ogP_fuels_add 8 1 with "GF") as "[GF GF1]". 1: lia.
      iApply (lwp_load _ ∅ 0 with "[$TG $Ptrl $GF1]"). 1: done.
      iIntros "[(_& TG& _) Ptrl]".
      iModIntro. iSplitL "Ptrl".
      { iNext. iRight. iFrame. eauto. }
      do 4 lwp_pure_one.
      iApply lwpupd_label. iIntros "PL".
      iApply sfmupd_fupd_acc.
      iMod (tf_until_fulfill with "Hul") as "Hul". 1: set_solver.
      iModIntro.
      iEval (replace 100 with (99 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iDestruct "Hul" as "[_ Hul]". iMod ("Hul" $! _) as "Hul".
      iMod ("Hul" with "[PL]") as "Hul".
      { iNext. tf_red. iExists _. tf_red. iEval (rewrite tf_atomic_logic). iFrame. done. }
      iPoseProof ("Hul" with "[] Gg") as "Hul".
      { iPureIntro. set_solver. }
      iEval (replace 99 with (98 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iMod ("Hul" $! _) as "Hul". iModIntro. iMod "Hul" as "(PL& Gg& #OFkl)".
      tf_red. iDestruct "PL" as "(%& PL)". tf_red. iDestruct "PL" as "(PL& %)". subst a.
      iModIntro. iFrame "PL".
      replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
      iMod (group_delete with "TG Gg") as "TG".
      replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ogid) by set_solver.
      iModIntro. lwp_pure. simpl.
      iFrame "TG". iExists 1, ∅, 0. iSplitR; first eauto. iIntros "TG _ _ _".
      iModIntro.
      lwp_finish.
      iApply "HΦ". rewrite /lift_term. iMod (thread_terminate with "TG") as "$". done.
  Qed.

  Lemma mp_pre Θ i j (l : loc) Φ Ψs :
    i ≠ j →
    Θ = {[i := writer #l; j := reader #l ]} →
    Φ = (λ m1 m2, (∃ g1 g2 k kl1 kl2,
                      ⌜ k ≠ kl1 ⌝ ∗ mp_tf k l ∗
                      tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1) ∗
                      tf_eventually Nl kl1 false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
                      tf_eventually Nl kl2 false 1 (∃ v, (j ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
                      ⟨thP_groups i {[g1]} ∗ ogP_obls i g1 0 {[k; kl1]} ∗
                       thP_groups j {[g2]} ∗ ogP_obls j g2 1 ({[kl2]}) ∗
                       ogP_fuel g1 0 m1 ∗ ogP_fuel g2 1 m2⟩)%F) →
    Ψs = ({[i := fork_post; j := fork_post]}) →
    ((l ↦ #0) -∗
     ([∗ set] i ∈ dom Θ, thP_groups i ∅) -∗
     |={⊤}=>m ∃ m1 m2, (⟦Φ m1 m2⟧ₗ ∗
                       (⟦Φ m1 m2⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (Hij HT HP HQ) "Ptrl TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    iPoseProof (big_sepS_union with "TGs") as "[TG1 TG2]".
    { set_solver. }
    rewrite !big_sepS_singleton.
    iPoseProof (mp_writer_spec) as (m1) "mp_writer_spec".
    iPoseProof (mp_reader_spec) as (m2) "mp_reader_spec".
    iMod (group_alloc _ _ _ 0 m1 with "TG1") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ _ false 0 0 m1 with "Gg1") as "(%k& %Hk& Gg1& #Ok& Ofk& #Wlk& Ak)". 1: done.
    iMod ("Ak" $! _ Np (l ↦ #0)%F (l ↦ #1)%F with "Ptrl") as "Uk".
    iPoseProof (tf_until_frac_split with "Uk") as "[Uk Uk']".
    { symmetry; apply Qp.div_2. }
    iMod (inv_alloc Na _ ⟦(tf_until Np k false (1 / 2) (l ↦ #0) (l ↦ #1) ∨ ⟨ oblP_fulfilled k ⟩ ∗ l ↦ #1)⟧ₗ with "[Uk']") as "#Ak".
    { iNext. tf_red. iLeft. iFrame. }
    iMod (tf_until_alloc _ _ _ _ false 0 0 m1 with "Gg1") as "(%kl1& %Hkl1& Gg1& #Okl1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nl (⌜True⌝)%F (∃ v : val, i ⤉ "exit",v ∗ ⌜v = #()⌝)%F with "[]") as "Ukl1".
    { tf_red. done. }
    iMod (group_alloc _ _ _ 1 m2 with "TG2") as "(%g2& %Ning2& TG2& Gg2& Gf2)".    
    iMod (tf_until_alloc _ _ _ _ false 1 1 1 with "Gg2") as "(%kl2& %Hkl2& Gg2& #Okl2& Ofkl2& #Wlkl2& Akl2)". 1: done.
    iMod ("Akl2" $! _ Nl (⌜True⌝)%F (∃ v : val, j ⤉ "exit",v ∗ ⌜v = #()⌝)%F with "[]") as "Ukl2".
    { tf_red. done. }
    iModIntro. iExists m1, m2. iSplitL "Uk Ukl1 Ukl2 TG1 Gg1 TG2 Gg2 Gf1 Gf2 Ofk Ofkl1 Ofkl2".
    { subst Φ.
      tf_red. iExists g1. tf_red. iExists g2.
      tf_red. iExists k. tf_red. iExists kl1. tf_red. iExists kl2.
      do 1 tf_red. iSplit.
      { iPureIntro. intros <-. set_solver. }
      iFrame "Ok Wlk Ak".
      replace ({[kl1]} ∪ ({[k]} ∪ ∅)) with ({[k; kl1]} : gset _) by set_solver. rewrite !union_empty_r_L. iFrame. }
    iClear "Ok Wlk Ak Okl1 Wlkl1 Okl2 Wlkl2". clear dependent g1 g2 k kl1 kl2.
    iIntros "HP". subst Φ.
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g2& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%k& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl2& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%Hkne& #mp& Uk& Ukl1& Ukl2& TG1& Gg1& TG2& Gg2& Gf1& Gf2)".
    iPoseProof ("mp_writer_spec" $! i l (λ v, lift_term i fork_post v) with "[Uk Ukl1 TG1 Gg1 Gf1]") as "WP1".
    { iExists g1, k, kl1. iFrame. iSplitR; eauto. }
    iPoseProof ("mp_reader_spec" $! j l (λ v, lift_term j fork_post v) with "[Ukl2 TG2 Gg2 Gf2]") as "WP2".
    { iExists g2, k, kl2. iFrame. eauto. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { rewrite lookup_insert_ne; auto. }
    { rewrite lookup_insert_ne; auto. }
    iSplitL "WP1".
    { iApply "WP1". iModIntro. eauto. }
    rewrite big_sepM2_singleton. iApply "WP2". iModIntro. eauto.
  Qed.

End proof.
