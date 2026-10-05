From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag.
From lantana.heap_lang.examples Require Import step_tactics.

(** * Nested waits on flags, to a nondeterministically chosen depth *)

Module Nondet.

  Definition nest : val :=
    rec: "fn" "x" "n" :=
      if: "n" ≤ #0%Z
      then Flag.set "x"
      else
        let: "y" := Flag.init #() in
        Fork ("fn" "y" ("n" - #1%Z));;
        Flag.wait "y";;
        Flag.set "x".

  Definition nondet : val :=
    λ: <>,
      let: "n" := ChooseNat in
      let: "x" := Flag.init #() in
      Fork (nest "x" "n");;
      Flag.wait "x".

End Nondet.

Section proof.
  Context `{!heapGS Σ}.

  (** The main proofs. *)

  (** Because the blocking function [wait] increases the layer by 1, the layer grows with the
      nested [wait] calls. The obligation [k] of the flag [x] is a child of the running thread. *)
  Lemma Nondet_nest_spec :
    ⊢ ∃ μ, ∀ lc i (x : loc) (n : Z) G k C,
    l{{{ thread_expr i C (Nondet.nest #x #n) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g (Z.to_nat n)%ordi μ) ∗
         ⌜k ∈ G⌝ ∗ oblP_kids k ∅ ∗
         flag_tk x k ∗
         is_flag x k (Z.to_nat n) }}}
      Nondet.nest #x #n @ i
    l{{{ RET #(); thread_expr i C #() ∗ £ lc ∗ thP_kids i (G ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    unfold Nondet.nest.
    (* Löb induction (or induction on [n]); the [∃ μ] is fine since the layer [n] drops. *)
    iLöb as "NEST".
    iPoseProof (Flag_init_thread_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_thread_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (100 ⊕ μ_fi ⊕ μ_fs ⊕ μ_fw)%M.
    iIntros (lc i x n G k C) "!> % (TE& TG& GF& %Ink& Kk& Ftk& #is_flag) HΦ".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF F_set]".
    iPoseProof (oblP_fuel_add_set with "F_set") as "[F_init F_set]".
    iPoseProof (oblP_fuel_add_set with "F_set") as "[F_set F_wait]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc (100 ⊕ lc)%ord.
    iPoseProof (tlc_split with "LC") as "[LC Q_LC]".
    lwp_pures.
    destruct (decide (n ≤ 0)%Z).
    - rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      lwp_bind (Flag.set _).
      iModIntro.
      iMod (oblP_fuel_layer_mon_set _ 0 with "F_set") as "F_set".
      { apply ord.O_bot. }
      iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_set $Kk $Ftk $is_flag]"). 1: eauto.
      iIntros "(TE& _& TG& #Od)". iApply ("HΦ" with "[$]").
    - rewrite bool_decide_eq_false_2; last done.
      lwp_pures.
      lwp_bind (Flag.init _).
      iMod (oblP_fuel_layer_mon_set _ 0 with "F_init") as "F_init".
      { apply ordArith.le_from_nat. lia. }
      iModIntro.
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iDestruct "NEST" as (μ_s) "NEST".
      (* The obligation of the flag [y] pays the steps until the fork, the move to the forked
         thread, and the steps of the forked thread. *)
      iApply ("Flag_init_spec" $! 0 _ _ (Z.to_nat (n - 1)%Z) (95 ⊕ (1 ⊕ (10 ⊕ μ_s)))%M
               with "[$TE $TG $F_init]").
      iIntros "%ptry %k0 (TE& _& %Hk0& TG& Kk0& Of0& Ftk0& #is_flag0)".
      iPoseProof (oblP_fuel_add with "Of0") as "[Of0 Fr]".
      iPoseProof (oblP_fuel_add with "Fr") as "[Mv GFj]".
      iPoseProof (oblP_fuels_add_obl with "Of0 GF") as "GF".
      lwp_pures.
      lwp_bind (Fork _).
      iModIntro.
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_fork {[k0]} (oblP_kids k0 ∅ ∗ oblP_fuel k0 (Z.to_nat (n - 1)%Z) (10 ⊕ μ_s)%M ∗
                               flag_tk ptry k0)%I ({[k0]} ∪ G) ∅ 0
               with "[] [TE TG GF1 Mv Kk0 GFj Ftk0]"); first set_solver.
      2:{ iFrame "TE TG GF1 Kk0 GFj Ftk0". iSplitR; first by rewrite big_sepS_empty.
          rewrite big_sepS_singleton. iExists _. iFrame "Mv". }
      { iIntros (j ?) "!> (TE& TG& Kk0& GFj& Ftk0) HΦ".
        iPoseProof (oblP_fuel_add with "GFj") as "[GF GFj]".
        iAssert (oblP_fuels {[k0]} 10) with "[GF]" as "GF".
        { rewrite big_sepS_singleton. iExists _. iFrame. }
        lwp_pure_one.
        iModIntro.
        iPoseProof ("NEST" $! 0 with "[$TE $TG $Kk0 $Ftk0 $is_flag0 GFj]") as "H".
        { iSplitL "GFj"; first by rewrite big_sepS_singleton. iPureIntro. set_solver. }
        iApply lwp_sfmupd. iApply "H". iIntros "(TE& _& TG& #Od)".
        replace ({[k0]} ∖ {[k0]}) with (∅ : gset oid) by set_solver.
        iMod (thread_terminate with "TG") as "#Td".
        iModIntro. rewrite /lift_term. iApply "HΦ". eauto. }
      iIntros "(TE& _& TG& _)".
      iPoseProof (oblP_fuels_remove_obl k0 with "GF") as "GF".
      replace (({[k0]} ∪ G) ∖ {[k0]}) with G by set_solver.
      lwp_pures.
      lwp_bind (Flag.wait _).
      iModIntro.
      iMod (oblP_fuel_layer_mon_set _ ((Z.to_nat (n - 1)) ⊕ 1)%ordi with "F_wait") as "F_wait".
      { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n - 1) + 1)%nat with (Z.to_nat n) by lia. done. }
      iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $F_wait $is_flag0]").
      iIntros "(TE& _& TG& #Od0)".
      lwp_pures.
      lwp_bind (Flag.set _).
      iModIntro.
      iMod (oblP_fuel_layer_mon_set _ 0 with "F_set") as "F_set".
      { apply ord.O_bot. }
      iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_set $Kk $Ftk $is_flag]"). 1: eauto.
      iIntros "(TE& _& TG& #Od)". iApply ("HΦ" with "[$]").
  Qed.

  (** [nondet] always terminates; since the layer of [nest] depends on the nondeterministically
      chosen [n], the precondition needs layer [ω]. *)
  Lemma Nondet_nondet_spec :
    ⊢ ∃ μ, ∀ i G C,
    l{{{ thread_expr i C (Nondet.nondet #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g (ω)%ordi μ) }}}
      Nondet.nondet #() @ i
    l{{{ v, RET v; thread_expr i C (of_val v) ∗ ⌜v = #1⌝ }}}.
  Proof.
    iPoseProof (Flag_init_thread_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iPoseProof (Nondet_nest_spec) as (μ_nn) "Nondet_nest_spec".
    iExists (100 ⊕ μ_fi ⊕ μ_fw ⊕ μ_nn)%M. iIntros (i G C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF)".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_fi GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_fw GF_nn]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    rewrite /Nondet.nondet /=.
    lwp_pure_lc 100.
    lwp_bind (ChooseNat).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_choosenat _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iIntros (n) "(TE& _& TG& _)".
    lwp_pures.
    lwp_bind (Flag.init _).
    iMod (oblP_fuel_layer_mon_set _ 0 with "GF_fi") as "F_init".
    { apply ord.lt_le, ord.omega_upperbound. }
    iModIntro.
    (* The obligation of the flag [x] pays the steps until the fork, the move to the forked
       thread, and the forked thread. *)
    iApply ("Flag_init_spec" $! 0 _ _ (Z.to_nat (n)%Z) (96 ⊕ (1 ⊕ μ_nn))%M with "[$TE $TG $F_init]").
    iIntros "%ptrx %k (TE& _& %Hk& TG& Kk& Of0& Ftk& #is_flag)".
    iPoseProof (oblP_fuel_add with "Of0") as "[Of0 Fr]".
    iPoseProof (oblP_fuel_add with "Fr") as "[Mv GFj]".
    iPoseProof (oblP_fuels_add_obl with "Of0 GF") as "GF".
    lwp_pures.
    lwp_bind (Fork _).
    iModIntro.
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_fork {[k]} (oblP_kids k ∅ ∗ oblP_fuel k (Z.to_nat (n)%Z) μ_nn ∗ flag_tk ptrx k)%I ({[k]} ∪ G) ∅ 0
             with "[] [TE TG GF1 Mv Kk GFj Ftk]"); first set_solver.
    2:{ iFrame "TE TG GF1 Kk GFj Ftk". iSplitR; first by rewrite big_sepS_empty.
        rewrite big_sepS_singleton. iExists _. iFrame "Mv". }
    { iIntros (j ?) "!> (TE& TG& Kk& GFj& Ftk) HΦ".
      iApply lwp_sfmupd.
      iApply ("Nondet_nest_spec" $! 0 with "[$TE $TG $Kk $Ftk $is_flag GFj]").
      { iSplitL "GFj"; first by rewrite big_sepS_singleton. iPureIntro. set_solver. }
      iIntros "(TE& _& TG& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. iApply "HΦ". eauto. }
    iIntros "(TE& _& TG& _)".
    iPoseProof (oblP_fuels_remove_obl k with "GF") as "GF".
    replace (({[k]} ∪ G) ∖ {[k]}) with G by set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (oblP_fuel_layer_mon_set _ ((Z.to_nat (n)) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n) + 1)%nat with (Z.to_nat (n + 1)) by lia.
      apply ord.lt_le, ord.omega_upperbound. }
    iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    iApply ("HΦ" with "[$TE]"). done.
  Qed.

End proof.
