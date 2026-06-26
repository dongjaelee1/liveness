From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From liris.heap_lang.examples Require Export flag.

Module Nondet.

  Definition nest : val :=
    rec: "fn" "x" "n" :=
      if: "n" ≤ #0%Z
      (* if true, set the flag and return *)
      then Flag.set "x"
      else
        (* fork and recursively pass the flag y to a thread *)
        let: "y" := ref #0 in
        Fork ("fn" "y" ("n" - #1%Z));;
        (* and wait on y *)
        Flag.wait "y";;
        (* finally set x and return *)
        Flag.set "x".

  Definition nondet : val :=
    λ: <>,
      (* alloc a flag x, nondeterministically choose a nat, and fork a nest thread and wait *)
      let: "x" := ref #0 in
      let: "n" := ChooseNat in
      Fork (nest "x" "n");;
      Flag.wait "x".

End Nondet.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nl := nroot.@ "label".

  (** The main proofs. *)

  (** Because the blocking function wait increases the layer by 1, the layer grows with the nested wait calls. *)
  Lemma Nondet_nest_spec :
    ⊢ ∃ μ, ∀ lc i (x : loc) (n : Z) G g K k ℓg,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g (Z.to_nat n)%ordi μ) ∗
         crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗
         flag_tk x k ∗
         is_flag x k (Z.to_nat n) }}}
      Nondet.nest #x #n @ i
    l{{{ RET #(); £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    unfold Nondet.nest.
    (** Löb to bootstrap the spec; can do induction on n too *)
    (* Existential μ is okay, because the layer n will drop *)
    iLöb as "NEST".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (100 ⊕ μ_fs ⊕ μ_fw)%M.
    iIntros (lc i x n G g K k ℓg) "!> % (TG& GF& Gg& %Ink& Ftk& #is_flag) HΦ".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_set]".
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
      iApply ("Flag_set_spec" $! 0 with "[$TG $F_set $Gg $Ftk $is_flag]"). 1: eauto.
      iIntros "(_& TG& Gg& #Od)". iApply ("HΦ" with "[$]").
    - rewrite bool_decide_eq_false_2; last done.
      lwp_pures.
      lwp_bind (AllocN _ _).
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
      iModIntro. iIntros (ptry) "((_& TG& _)& Ptry& _)".
      lwp_pures.
      lwp_bind (Fork _).
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iModIntro. iApply lwp_fork. iModIntro. iFrame "TG GF1". iExists ∅. iSplitR; first done.
      iIntros (j) "TG _ TGj !> !>".
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iDestruct "NEST" as (μ_s) "NEST".
      iMod (carrier_alloc _ _ _ (Z.to_nat (n - 1)%Z) (10 ⊕ μ_s)%M with "TGj") as "(%& _& TGj& Cgj& GFj)".
      iMod (is_flag_init _ ptry _ _ (Z.to_nat (n - 1)%Z) _ 0 with "Ptry Cgj") as "(%k0& _& Cgj& _& Ftk0& #is_flag0)". 1: done.
      rewrite !union_empty_r_L.
      iModIntro. iSplitR "TGj GFj Cgj Ftk0".
      + iModIntro. lwp_pures.
        lwp_bind (Flag.wait _).
        iModIntro.
        iMod (crP_fuel_layer_mon_set _ ((Z.to_nat (n - 1)) ⊕ 1)%ordi with "F_wait") as "F_wait".
        { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n - 1) + 1)%nat with (Z.to_nat n) by lia. done. }
        iApply ("Flag_wait_spec" $! 0 with "[$TG $F_wait $is_flag0]").
        iIntros "(_& TG& #Od0)".
        lwp_pures.
        lwp_bind (Flag.set _).
        iModIntro.
        iMod (crP_fuel_layer_mon_set _ 0 with "F_set") as "F_set".
        { apply ord.O_bot. }
        iApply ("Flag_set_spec" $! 0 with "[$TG $F_set $Gg $Ftk $is_flag]"). 1: eauto.
        iIntros "(_& TG& Gg& #Od)". iApply ("HΦ" with "[$]").
      + iModIntro.
        iRename "TGj" into "TG".
        iPoseProof (crP_fuel_add with "GFj") as "[GF GFj]".
        iPoseProof (crP_fuels_init with "[GF]") as "GF".
        { iApply big_sepS_singleton. iFrame. }
        lwp_pure_one.
        iModIntro.
        iPoseProof ("NEST" $! 0 with "[$TG GFj $Cgj $Ftk0 $is_flag0]") as "H".
        { iSplit.
          - iApply big_sepS_singleton. iFrame.
          - iPureIntro. set_solver. }
        iApply lwp_sfmupd. iApply "H". iIntros "(_& TG& Cg& #Od)".
        replace ({[k0]} ∖ {[k0]}) with (∅ : gset oid) by set_solver.
        iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
        replace ({[g0]} ∖ {[g0]}) with (∅ : gset ocid) by set_solver.
        iMod (thread_terminate with "TG") as "#Td".
        iModIntro. rewrite /lift_term. by iFrame "Td".
  Qed.

  (** nondet always terminates, but because nest's layer depends on nondeterministically chosen n, we need ω for precondition. *)
  Lemma Nondet_nondet_spec :
    ⊢ ∃ μ, ∀ i G,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g (ω)%ordi μ) }}}
      Nondet.nondet #() @ i
    l{{{ v, RET v; ⌜v = #1⌝ }}}.
  Proof.
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iPoseProof (Nondet_nest_spec) as (μ_nn) "Nondet_nest_spec".
    iExists (100 ⊕ μ_fw ⊕ μ_nn)%M. iIntros (i G Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF)".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (crP_fuel_add_set with "GF_m") as "[GF_fw GF_nn]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    rewrite /Nondet.nondet /=.
    lwp_pure_lc 100.
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptrx) "((_& TG& _)& Ptrx& _)".
    lwp_pures.
    lwp_bind (ChooseNat).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_choosenat _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iIntros (n) "(_& TG& _)".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro. iApply lwp_fork. iModIntro. iFrame "TG GF1". iExists ∅. iSplitR; first done.
    iIntros (j) "TG _ TGj !> !>".
    iMod (carrier_alloc _ _ _ (Z.to_nat (n)%Z) (μ_nn)%M with "TGj") as "(%& _& TGj& Cgj& GFj)".
    iMod (is_flag_init _ ptrx _ _ (Z.to_nat (n)%Z) _ 0 with "Ptrx Cgj") as "(%k& _& Cgj& _& Ftk& #is_flag)". 1: done.
    rewrite !union_empty_r_L.
    iModIntro. iSplitR "TGj GFj Cgj Ftk".
    - iModIntro. lwp_pures.
      lwp_bind (Flag.wait _).
      iModIntro.
      iMod (crP_fuel_layer_mon_set _ ((Z.to_nat (n)) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
      { rewrite -hessenberg.add_from_nat. replace (Z.to_nat (n) + 1)%nat with (Z.to_nat (n + 1)) by lia.
        apply ord.lt_le, ord.omega_upperbound. }
      iApply ("Flag_wait_spec" $! 0 with "[$TG $GF_fw $is_flag]").
      iIntros "(_& TG& #Od0)".
      iApply ("HΦ" with "[]"). done.
    - iModIntro.
      iApply lwp_sfmupd.
      iApply ("Nondet_nest_spec" $! 0 with "[$TGj GFj $Cgj $Ftk $is_flag]").
      { iSplit.
        - iApply big_sepS_singleton. iFrame.
        - iPureIntro. set_solver. }
      iIntros "(_& TG& Cg& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g]} ∖ {[g]}) with (∅ : gset ocid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. by iFrame "Td".
  Qed.

End proof.
