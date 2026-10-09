From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From lantana.heap_lang Require Import triple.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag.

Module Nondet.

  (** [nest x n] sets the flag [x]. If [n > 0], it first allocates a flag [y], forks
      [nest y (n - 1)], and waits on [y]. *)
  Definition nest : val :=
    rec: "fn" "x" "n" :=
      if: "n" ≤ #0%Z
      then Flag.set "x"
      else
        let: "y" := Flag.init #() in
        Fork ("fn" "y" ("n" - #1%Z));;
        Flag.wait "y";;
        Flag.set "x".

  (** [nondet] chooses [n] nondeterministically, allocates a flag [x], forks [nest x n], and
      waits on [x]. *)
  Definition nondet : val :=
    λ: <>,
      let: "n" := ChooseNat in
      let: "x" := Flag.init #() in
      Fork (nest "x" "n");;
      Flag.wait "x".

End Nondet.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  (** Each nested [wait] needs fuel one layer above its flag, so [nest x n] needs fuel at
      layer [n]. *)
  Lemma Nondet_nest_spec :
    ⊢ ∃ μ, ∀ lc i (x : loc) (n : Z) G g K k ℓg C,
    l{{{ thread_expr i C (Nondet.nest #x #n) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g (Z.to_nat n)%ordi μ) ∗
         crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗
         flag_tk x k ∗
         is_flag x k (Z.to_nat n) }}}
      Nondet.nest #x #n @ i
    l{{{ RET #(); thread_expr i C #() ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    unfold Nondet.nest.
    (* Löb induction on the whole specification, [∃ μ] included. The recursive call runs in a
       forked thread, whose new carrier gets the budget that the induction hypothesis names. *)
    iLöb as "NEST".
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (100 ⊕ μ_fi ⊕ μ_fs ⊕ μ_fw)%M.
    iIntros (lc i x n G g K k ℓg C) "!> % (TE& TG& GF& Gg& %Ink& Ftk& #is_flag) HΦ".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_set]".
    iPoseProof (crP_fuel_add_set with "F_set") as "[F_init F_set]".
    iPoseProof (crP_fuel_add_set with "F_set") as "[F_set F_wait]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc (100 ⊕ lc)%ord.
    iPoseProof (tlc_split with "LC") as "[LC Q_LC]".
    lwp_pures.
    destruct (decide (n ≤ 0)%Z).
    - rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      lwp_bind (Flag.set _).
      iModIntro.
      iMod (crP_fuel_layer_mon_set _ 0 with "F_set") as "F_set".
      { apply ord.O_bot. }
      iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_set $Gg $Ftk $is_flag]"). 1: eauto.
      iIntros "(TE& _& TG& Gg& #Od)". iApply ("HΦ" with "[$]").
    - rewrite bool_decide_eq_false_2; last done.
      lwp_pures.
      lwp_bind (Flag.init _).
      iMod (carrier_alloc _ _ _ (Z.to_nat (n - 1)%Z) (μ_fi ⊕ 95)%M with "TG")
        as "(%& %NinG& TG& Cg0& GF0)".
      iPoseProof (crP_fuel_add with "GF0") as "[F_init0 GF0]".
      iMod (crP_fuel_layer_mon_set _ 0 with "F_init") as "F_init".
      { apply ordArith.le_from_nat. lia. }
      iMod (crP_fuel_layer_mon _ 0 with "F_init0") as "F_init0".
      { apply ordArith.le_from_nat. lia. }
      iModIntro.
      iApply ("Flag_init_spec" $! 0 _ _ _ _ _ 1 with "[$TE $TG F_init F_init0 $Cg0]").
      { iApply big_sepS_union. 1: set_solver. rewrite big_sepS_singleton. iFrame. }
      iIntros "%ptry %k0 (TE& _& TG& _& Cg0& Of0& Ftk0& #is_flag0)".
      rewrite union_empty_r_L.
      iPoseProof (crP_fuels_add_carrier with "GF0 GF") as "GF".
      lwp_pures.
      lwp_bind (Fork _).
      iModIntro.
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iDestruct "NEST" as (μ_s) "NEST".
      iApply (lwp_fork _ (10 ⊕ μ_s)%M _ _ _ ∅ 0 with "[] [$TE $TG $GF1 $Cg0 Of0 Ftk0]"). 1: reflexivity.
      2:{ iSplitR; first done. iSplitL "Of0".
          - rewrite big_sepS_singleton. iFrame.
          - iApply "Ftk0". }
      { iIntros (j ? ?) "!> (TE& TG& GFj& Cgj& Ftk0) HΦ".
        iPoseProof (crP_fuel_add_set with "GFj") as "[GF GFj]".
        iPoseProof (crP_fuels_init with "GF") as "GF".
        lwp_pure_one.
        iModIntro.
        iPoseProof ("NEST" $! 0 with "[$TE $TG $GFj $Cgj $Ftk0 $is_flag0]") as "H".
        { iPureIntro. set_solver. }
        iApply lwp_sfmupd. iApply "H". iIntros "(TE& _& TG& Cg& #Od)".
        replace ({[k0]} ∖ {[k0]}) with (∅ : gset oid) by set_solver.
        iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
        replace ({[g2]} ∖ {[g2]}) with (∅ : gset ocid) by set_solver.
        iMod (thread_terminate with "TG") as "#Td".
        iModIntro. rewrite /lift_term. iApply "HΦ". eauto. }
      iIntros "(TE& (_& TG& _)& Cg0)".
      replace ({[k0]} ∖ {[k0]}) with (∅ : oids) by set_solver.
      iMod (carrier_delete with "TG Cg0") as "TG". 1: set_solver.
      iPoseProof (crP_fuels_remove_carrier g0 with "GF") as "GF".
      replace (({[g0]} ∪ G) ∖ {[g0]}) with G by set_solver.
      lwp_pures.
      lwp_bind (Flag.wait _).
      iModIntro.
      iMod (crP_fuel_layer_mon_set _ ((Z.to_nat (n - 1)) ⊕ 1)%ordi with "F_wait") as "F_wait".
      { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n - 1) + 1)%nat with (Z.to_nat n) by lia. done. }
      iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $F_wait $is_flag0]").
      iIntros "(TE& _& TG& #Od0)".
      lwp_pures.
      lwp_bind (Flag.set _).
      iModIntro.
      iMod (crP_fuel_layer_mon_set _ 0 with "F_set") as "F_set".
      { apply ord.O_bot. }
      iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_set $Gg $Ftk $is_flag]"). 1: eauto.
      iIntros "(TE& _& TG& Gg& #Od)". iApply ("HΦ" with "[$]").
  Qed.

  (** [nondet] terminates, but [nest]'s layer depends on the chosen [n], so the precondition
      needs fuel at layer [ω]. *)
  Lemma Nondet_nondet_spec :
    ⊢ ∃ μ, ∀ i G C,
    l{{{ thread_expr i C (Nondet.nondet #()) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g (ω)%ordi μ) }}}
      Nondet.nondet #() @ i
    l{{{ v, RET v; thread_expr i C (of_val v) ∗ thP_carriers i G ∗ ⌜v = #1⌝ }}}.
  Proof.
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iPoseProof (Nondet_nest_spec) as (μ_nn) "Nondet_nest_spec".
    iExists (100 ⊕ μ_fi ⊕ μ_fw ⊕ μ_nn)%M. iIntros (i G C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF)".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (crP_fuel_add_set with "GF_m") as "[GF_fi GF_m]".
    iPoseProof (crP_fuel_add_set with "GF_m") as "[GF_fw GF_nn]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    rewrite /Nondet.nondet /=.
    lwp_pure_lc 100.
    lwp_bind (ChooseNat).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_choosenat _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iIntros (n) "(TE& _& TG& _)".
    lwp_pures.
    lwp_bind (Flag.init _).
    iMod (carrier_alloc _ _ _ (Z.to_nat (n)%Z) (μ_fi ⊕ 96)%M with "TG")
      as "(%& %NinG& TG& Cg0& GF0)".
    iPoseProof (crP_fuel_add with "GF0") as "[F_init0 GF0]".
    iMod (crP_fuel_layer_mon_set _ 0 with "GF_fi") as "F_init".
    { apply ord.lt_le, ord.omega_upperbound. }
    iMod (crP_fuel_layer_mon _ 0 with "F_init0") as "F_init0".
    { apply ordArith.le_from_nat. lia. }
    iModIntro.
    iApply ("Flag_init_spec" $! 0 _ _ _ _ _ 1 with "[$TE $TG F_init F_init0 $Cg0]").
    { iApply big_sepS_union. 1: set_solver. rewrite big_sepS_singleton. iFrame. }
    iIntros "%ptrx %k (TE& _& TG& _& Cg0& Of0& Ftk& #is_flag)".
    rewrite union_empty_r_L.
    iPoseProof (crP_fuels_add_carrier with "GF0 GF") as "GF".
    lwp_pures.
    lwp_bind (Fork _).
    iModIntro.
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_fork _ (μ_nn)%M _ _ _ ∅ 0 with "[] [$TE $TG $GF1 $Cg0 Of0 Ftk]"). 1: reflexivity.
    2:{ iSplitR; first done. iSplitL "Of0".
        - rewrite big_sepS_singleton. iFrame.
        - iApply "Ftk". }
    { iIntros (j ? ?) "!> (TE& TGj& GFj& Cgj& Ftk) HΦ".
      iApply lwp_sfmupd.
      iApply ("Nondet_nest_spec" $! 0 with "[$TE $TGj $GFj $Cgj $Ftk $is_flag]").
      { iPureIntro. set_solver. }
      iIntros "(TE& _& TG& Cg& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g2]} ∖ {[g2]}) with (∅ : gset ocid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. iApply "HΦ". eauto. }
    iIntros "(TE& (_& TG& _)& Cg0)".
    replace ({[k]} ∖ {[k]}) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Cg0") as "TG". 1: set_solver.
    iPoseProof (crP_fuels_remove_carrier g with "GF") as "GF".
    replace (({[g]} ∪ G) ∖ {[g]}) with G by set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (crP_fuel_layer_mon_set _ ((Z.to_nat (n)) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n) + 1)%nat with (Z.to_nat (n + 1)) by lia.
      apply ord.lt_le, ord.omega_upperbound. }
    iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    iApply ("HΦ" with "[$TE $TG]"). done.
  Qed.

  (** * The specifications in the paper's format

      Each is a corollary of the texan specification above. *)

  (** SPEC-NEST *)
  Corollary Nondet_nest_fbspec :
    ⊢ □ ∃ μ, ∀ lc i (x : loc) (n : Z) G g K k ℓg C,
    fb{{ fuels G (Z.to_nat n)%ordi μ ∗ crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗ flag_tk x k ∗
      is_flag x k (Z.to_nat n) }}^G
      Nondet.nest #x #n @ i; C; ⊤
    fb{{ v, ⌜v = #()⌝ ∗ £ lc ∗ crP_obls g ℓg (K ∖ {[k]}) ∗ oblP_discharged k }}^G.
  Proof.
    iPoseProof Nondet_nest_spec as (μ) "#H". iIntros "!>". iExists μ.
    iIntros (lc i x n G g K k ℓg C). rewrite /fbtriple /fbtriple_gen. iIntros (Φ) "Pre HΦ".
    iApply ("H" $! lc i x n G g K k ℓg C with "Pre"). iIntros "(TE& LC& TG& Post)".
    iApply "HΦ". by iFrame.
  Qed.

  (** SPEC-NONDET *)
  Corollary Nondet_nondet_fbspec :
    ⊢ □ ∃ μ, ∀ i G C,
    fb{{ fuels G (ω)%ordi μ }}^G Nondet.nondet #() @ i; C; ⊤ fb{{ v, ⌜v = #1⌝ }}^G.
  Proof.
    iPoseProof Nondet_nondet_spec as (μ) "#H". iIntros "!>". iExists μ.
    iIntros (i G C). rewrite /fbtriple /fbtriple_gen. iIntros (Φ) "Pre HΦ".
    iApply ("H" $! i G C with "Pre"). iIntros (v) "Post". by iApply "HΦ".
  Qed.

End proof.
