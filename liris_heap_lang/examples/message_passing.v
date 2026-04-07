From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(* From liris.heap_lang.lib Require Import par. *)

Definition writer : val :=
  λ: "l", "l" <- #1;;
          Label "exit" #().

Definition reader : val := 
  rec: "reader" "l" :=
    let: "n" := !"l" in
    if: "n" = #1
    then Label "exit" #()
    else "reader" "l".

Section mp_proof.
  Context `{!heapGS Σ}.
  Let N := nroot.@ "message_passing".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".
  Let Nl := N.@ "label".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  Definition mp_tf (k : oid) (l : loc) : tf Σ :=
    ⟨oblP_layer k 0 ∗ oblP_id k ∗ witP_layer k 0⟩ ∗
    tf_always Na (((tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1)) ∨ (⟨oblP_fulfilled k⟩ ∗ (l ↦ #1)))).

  Definition mp (k : oid) (l : loc) : iProp Σ :=
    ⟦mp_tf k l⟧ₗ.

  (** The main proofs. *)
  Global Instance mp_persistent k l : Persistent (mp k l).
  Proof. rewrite /mp /mp_tf. tf_red. apply _. Qed.

  Lemma mp_writer_spec i l :
    l{{{ ∃ k kl, ⌜k ≠ kl⌝ ∗
                 mp k l ∗
                 (* Start with the other half of the until ownership for the pointsto. *)
                 ⟦tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1)⟧ₗ ∗
                 ⟦tf_eventually Nl kl false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝)⟧ₗ ∗
                 thP_obls i ({[k; kl]}) 1 ∗
                 oblP_fuel k 0 10 ∗ oblP_fuel kl 0 10 }}}
      writer #l @ i
    l{{{ v, RET v; lift_term i fork_post v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as "(%&%& %Nek& #Hmp& Hup& Hul& TG& Ofk& Ofkl)".
    rewrite /mp /mp_tf. do 2 tf_red. iDestruct "Hmp" as "((#Olk& #Ok& #Wlk)& #Hmp)".
    rewrite /writer /=.
    iMod (oblP_fuel_lt_set ({[k; kl]}) 0 0 9 10 with "[Ofk Ofkl]") as "[Of Of1]".
    { rewrite !measure_nat. apply OrdArith.lt_from_nat. lia. }
    { destruct (decide (({[k]} : gset _) ## {[kl]})); cycle 1.
      { destruct (decide (k = kl)).
        - subst. rewrite union_idemp_L. iApply big_sepS_singleton. eauto.
        - exfalso. set_solver. }
      iApply big_sepS_union; first auto. rewrite !big_sepS_singleton. iFrame. }
    (* Pure steps *)
    lwp_lam. iFrame "TG". iExists ⊤, ∅, 10. iSplitR; first done.
    iSplitL "Of1".
    { by iFrame. }
    iIntros "!> TG _ !> LC !>".
    lwp_finish_upd.
    rewrite (oblP_fuel_eq_set _ 0 0 9 (8 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (oblP_fuel_add_set with "Of") as "[Of Of1]".
    lwp_bind (Store _ _).
    iModIntro.
    iInv "Hmp" as "mp". iDestruct "mp" as "[mp | mp]"; cycle 1.
    { iDestruct "mp" as "[>mp _]". iEval (rewrite tf_until_logic) in "Hup". iDestruct "Hup" as "[Oak _]".
      iPoseProof (oblP_assigned_fulfilled_false with "Oak mp") as "%". done. }
    replace 10 with (9 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iCombine "Hup mp" as "mp".
    iMod (tf_until_to_true with "mp") as "mp".
    { apply N_subseteq_1. }
    replace 9 with (8 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "mp" as "[Ptrl ACCmp]".
    iApply lwp_sfmupd. iEval (rewrite tf_atomic_logic) in "Ptrl".
    iApply (lwp_store _ ∅ 0 with "[$Ptrl $TG $Of1]").
    { done. }
    iIntros "((_& TG& _)& Ptrl)".
    iMod ("ACCmp" with "Ptrl") as "mp".
    (** TODO: make this a modality instance. *)
    iApply sfmupd_fupd_acc. iMod "mp". iMod (tf_until_fulfill with "mp") as "mp".
    { apply N_subseteq_1. }
    iPoseProof ("mp" with "[] TG") as "mp".
    { iPureIntro. set_solver. }
    (** TODO: add rules for sfmupd and lc. *)
    replace 8 with (7 + 1) by lia. iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_fupd_elim_later with "LC1"). iNext.
    iMod ("mp" $! _) as "mp". iModIntro. iMod "mp" as "(Ptrl& TG& #Ofk)".
    iApply fupd_mask_intro. 1: set_solver. iIntros ">_". iIntros "!> !>". iSplitL "Ptrl".
    { iNext. iRight. iFrame. eauto. }
    iModIntro.
    lwp_pure.
    replace ({[k; kl]} ∖ {[k]} : gset _) with ({[kl]} : gset _).
    2:{ set_solver. }
    simpl. iPoseProof (big_sepS_union with "Of") as "[_ Of]".
    { set_solver. }
    rewrite big_sepS_singleton.
    rewrite (oblP_fuel_eq _ 0 0 8 (7 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (oblP_fuel_add with "Of") as "[Of Of1]".
    simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Of1".
    { iApply big_sepS_singleton. iFrame. }
    iIntros "TG _ !> _ !>".
    iModIntro.
    rewrite (oblP_fuel_eq _ 0 0 7 (6 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (oblP_fuel_add with "Of") as "[Of Of1]".
    lwp_pure.
    simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Of1".
    { iApply big_sepS_singleton. iFrame. }
    iIntros "TG _ !> _ !>".
    iApply lwpupd_label. iIntros "PL".
    iApply sfmupd_fupd_acc.
    iMod (tf_until_to_true with "Hul") as "Hul". 1: set_solver.
    iEval (replace 7 with (6 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_fupd_elim_later with "LC1"). iNext.
    iDestruct "Hul" as "[_ Hul]". iMod ("Hul" $! _) as "Hul".
    iApply sfmupd_fupd_acc.
    iMod ("Hul" with "[PL]") as "Hul".
    { iNext. tf_red. iExists _. tf_red. iEval (rewrite tf_atomic_logic). iFrame. done. }
    iModIntro. iApply sfmupd_fupd_acc.
    iMod (tf_until_fulfill with "Hul") as "Hul". 1: set_solver.
    iPoseProof ("Hul" with "[] TG") as "Hul".
    { iPureIntro. set_solver. }
    iEval (replace 6 with (5 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
    iApply (lc_fupd_elim_later with "LC1"). iNext.
    iMod ("Hul" $! _) as "Hul". iModIntro. iMod "Hul" as "(PL& TG& #OFkl)".
    tf_red. iDestruct "PL" as "(%& PL)". tf_red. iDestruct "PL" as "(PL& %)". subst a.
    iModIntro. iApply fupd_mask_intro. 1: set_solver. iIntros ">_". iModIntro. iFrame "PL".
    replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
    iModIntro. lwp_pure.
    simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitR; first done.
    iIntros "TG _ !> _ !> !>".
    lwp_finish.
    iApply "HΦ". rewrite /lift_term. iMod (obl_terminate with "TG") as "$". done.
  Qed.

  Lemma mp_reader_spec i l :
    l{{{ ∃ k kl, mp k l ∗
                 ⟦tf_eventually Nl kl false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝)⟧ₗ ∗
                 thP_obls i ({[kl]}) 1 ∗
                 oblP_fuel kl 1 (10 ⊕ (10 × ▽))%M}}}
      reader #l @ i
    l{{{ v, RET v; lift_term i fork_post v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as "(%&%& #Hmp& Hul& TG& Fkl)".
    rewrite /reader /=.
    rewrite /mp /mp_tf. do 2 tf_red. iDestruct "Hmp" as "((#Olk& #Ok& #Wlk)& #Hmp)".
    iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl WFkl]".
    (* Liveness induction *)
    iPoseProof (wit_fuels_init with "Wlk") as "(%& Wf0)".
    (* FIXME: coercions not working *)
    iMod (wit_fuels_add_map _ _ _ _ ({[kl:=(ord.from_nat 1, ms_nat 10)]}) with "Wf0 [WFkl]") as "Wf".
    { rewrite big_sepM_singleton. iFrame. iPureIntro. apply ordArith.lt_from_nat. lia. }
    rewrite map_union_empty.
    iClear "Wf0". iInduction α as [α IH] using WFOCM.ind.
    rewrite (oblP_fuel_eq _ 1 0 10 (9 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
    lwp_rec. simpl. iFrame "TG". iExists ⊤, ∅, 100. iSplitR; first done. iModIntro. iSplitL "Fkl1".
    { rewrite big_sepS_singleton. iFrame. }
    iIntros "TG _ !> LC !>".
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
      rewrite (oblP_fuel_eq _ _ 0 9 (8 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      iApply (lwp_load _ ({[k]} : gset _) 0 with "[$TG $Ptrl Fkl1]").
      { rewrite !big_sepS_singleton. iFrame. auto. }
      iIntros "[(_& TG& Rs) Ptrl]".
      rewrite big_sepS_singleton. iDestruct "Rs" as "[Wck | #Ofk]"; cycle 1.
      { iPoseProof (oblP_assigned_fulfilled_false with "Oak Ofk") as "%". done. }
      iMod ("HACC" with "[Oak' Ptrl]") as "_".
      { iModIntro. iApply oblP_variant_unfold. iLeft. iFrame. }
      iModIntro. iModIntro. iSplitL "Oak".
      { iNext. rewrite tf_until_logic. iLeft. iFrame. eauto. }
      iModIntro.
      rewrite (oblP_fuel_eq _ _ 0 8 (7 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_let. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 7 (6 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_lam. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 6 (5 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_op. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 5 (4 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_if. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      iMod (wit_fuels_decr with "Wf Wck") as "(%& %LTα& Wf'& Fkl')".
      rewrite big_sepM_singleton. rewrite (oblP_fuel_eq _ 1 0 10 (9 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iApply ("IH" $! α0 LTα with "Hul TG HΦ Fkl' Wf'").
    - (* k is fulfilled. *)
      iDestruct "mp" as ">(#Ofk& Ptrl)".
      iEval (rewrite tf_atomic_logic) in "Ptrl".
      rewrite (oblP_fuel_eq _ _ 0 9 (8 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      iApply (lwp_load _ ∅ 0 with "[$TG $Ptrl Fkl1]").
      { rewrite !big_sepS_singleton. iFrame. auto. }
      iIntros "[(_& TG& _) Ptrl]".
      iModIntro. iSplitL "Ptrl".
      { iNext. iRight. iFrame. eauto. }
      iModIntro.
      rewrite (oblP_fuel_eq _ _ 0 8 (7 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_let. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 7 (6 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_lam. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 6 (5 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_op. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !> !>".
      rewrite (oblP_fuel_eq _ _ 0 5 (4 ⊕ 1)%M); cycle 1.
      { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (oblP_fuel_add with "Fkl") as "[Fkl Fkl1]".
      lwp_if. simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitL "Fkl1".
      { rewrite big_sepS_singleton. iFrame. }
      iIntros "TG _ !> _ !>".
      iApply lwpupd_label. iIntros "PL".
      iApply sfmupd_fupd_acc.
      iMod (tf_until_to_true with "Hul") as "Hul". 1: set_solver.
      iEval (replace 100 with (99 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
      iApply (lc_fupd_elim_later with "LC1"). iNext.
      iDestruct "Hul" as "[_ Hul]". iMod ("Hul" $! _) as "Hul".
      iApply sfmupd_fupd_acc.
      iMod ("Hul" with "[PL]") as "Hul".
      { iNext. tf_red. iExists _. tf_red. iEval (rewrite tf_atomic_logic). iFrame. done. }
      iModIntro. iApply sfmupd_fupd_acc.
      iMod (tf_until_fulfill with "Hul") as "Hul". 1: set_solver.
      iPoseProof ("Hul" with "[] TG") as "Hul".
      { iPureIntro. set_solver. }
      iEval (replace 99 with (98 + 1) by lia) in "LC". iPoseProof (tlc_split_nat with "LC") as "[LC LC1]".
      iApply (lc_fupd_elim_later with "LC1"). iNext.
      iMod ("Hul" $! _) as "Hul". iModIntro. iMod "Hul" as "(PL& TG& #OFkl)".
      tf_red. iDestruct "PL" as "(%& PL)". tf_red. iDestruct "PL" as "(PL& %)". subst a.
      iModIntro. iApply fupd_mask_intro. 1: set_solver. iIntros ">_". iModIntro. iFrame "PL".
      replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
      iModIntro. lwp_pure.
      simpl. iFrame "TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro. iSplitR; first done.
      iIntros "TG _ !> _ !> !>".
      lwp_finish.
      iApply "HΦ". rewrite /lift_term. iMod (obl_terminate with "TG") as "$". done.
  Qed.

  Lemma mp_pre Θ i j (l : loc) Φ Ψs :
    i ≠ j →
    Θ = {[i := writer #l; j := reader #l ]} →
    Φ = (∃ k kl1 kl2, ⌜ k ≠ kl1 ⌝ ∗ mp_tf k l ∗
                      tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1) ∗
                      tf_eventually Nl kl1 false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
                      tf_eventually Nl kl2 false 1 (∃ v, (j ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
                      ⟨thP_obls i ({[k; kl1]}) 1 ∗ thP_obls j ({[kl2]}) 1 ∗
                       oblP_fuel k 0 10 ∗ oblP_fuel kl1 0 10 ∗ oblP_fuel kl2 1 (10 ⊕ (10 × ▽))%M⟩)%F →
    Ψs = ({[i := fork_post; j := fork_post]}) →
    ((l ↦ #0) -∗
     ([∗ set] i ∈ dom Θ, thP_obls i ∅ 1) -∗
     |={⊤}=>m (⟦Φ⟧ₗ ∗
              (⟦Φ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (Hij HT HP HQ) "Ptrl TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    iPoseProof (big_sepS_union with "TGs") as "[TG1 TG2]".
    { set_solver. }
    rewrite !big_sepS_singleton.
    iMod (tf_until_alloc _ _ _ _ false 0 10 with "TG1") as "(%k& %Hk& TG1& #Olk& #Ok& Ofk& #Wlk& Ak)".
    iMod ("Ak" $! _ Np (l ↦ #0)%F (l ↦ #1)%F with "Ptrl") as "Uk".
    iPoseProof (tf_until_frac_split with "Uk") as "[Uk Uk']".
    { symmetry; apply Qp.div_2. }
    iMod (inv_alloc Na _ ⟦(tf_until Np k false (1 / 2) (l ↦ #0) (l ↦ #1) ∨ ⟨ oblP_fulfilled k ⟩ ∗ l ↦ #1)⟧ₗ with "[Uk']") as "#Ak".
    { iNext. tf_red. iLeft. iFrame. }
    iMod (tf_until_alloc _ _ _ _ false 0 10 with "TG1") as "(%kl1& %Hkl1& TG1& #Olkl1& #Okl1& Ofkl1& #Wlkl1& Akl1)".
    iMod ("Akl1" $! _ Nl (⌜True⌝)%F (∃ v : val, i ⤉ "exit",v ∗ ⌜v = #()⌝)%F with "[]") as "Ukl1".
    { tf_red. done. }
    iMod (tf_until_alloc _ _ _ _ false 1 (10 ⊕ 10 × ▽)%M with "TG2") as "(%kl2& %Hkl2& TG2& #Olkl2& #Okl2& Ofkl2& #Wlkl2& Akl2)".
    iMod ("Akl2" $! _ Nl (⌜True⌝)%F (∃ v : val, j ⤉ "exit",v ∗ ⌜v = #()⌝)%F with "[]") as "Ukl2".
    { tf_red. done. }
    iModIntro. iSplitL "Uk Ukl1 Ukl2 TG1 TG2 Ofk Ofkl1 Ofkl2".
    { subst Φ. tf_red. iExists k. tf_red. iExists kl1. tf_red. iExists kl2. do 1 tf_red. iSplit.
      { iPureIntro. intros <-. set_solver. }
      iFrame "Olk Ok Wlk Ak".
      replace ({[kl1]} ∪ ({[k]} ∪ ∅)) with ({[k; kl1]} : gset _) by set_solver. rewrite union_empty_r_L. iFrame. }
    iClear "Olk Ok Wlk Ak Olkl1 Okl1 Wlkl1 Olkl2 Okl2 Wlkl2". clear dependent k kl1 kl2.
    iIntros "HP". subst Φ.
    iEval (tf_red) in "HP". iDestruct "HP" as "(%k& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl2& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%Hkne& #mp& Uk& Ukl1& Ukl2& TG1& TG2& Ofk& Ofkl1& Ofkl2)".
    iPoseProof (mp_writer_spec i l (λ v, lift_term i fork_post v) with "[Uk Ukl1 TG1 Ofk Ofkl1]") as "WP1".
    { iExists k, kl1. iFrame. iSplitR; eauto. }
    iPoseProof (mp_reader_spec j l (λ v, lift_term j fork_post v) with "[Ukl2 TG2 Ofkl2]") as "WP2".
    { iExists k, kl2. iFrame. eauto. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { rewrite lookup_insert_ne; auto. }
    { rewrite lookup_insert_ne; auto. }
    iSplitL "WP1".
    { iApply "WP1". iModIntro. eauto. }
    rewrite big_sepM2_singleton. iApply "WP2". iModIntro. eauto.
  Qed.

End mp_proof.
