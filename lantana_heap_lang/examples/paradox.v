From iris.bi Require Import lib.fractional.
From iris.algebra Require Import gmap mono_nat.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import rocq_tactics.
(* Re-imported so that Lantana's [£] shadows upstream Iris' ['£' n]. *)
From lantana.base_logic Require Import later_credits.

(** * The no-credit rule is unsound

    [lantanaGS_no_lc] assumes a rule for pure steps that pays no fuel. With it, two looping
    threads prove "eventually False" ([loop_paradox]), and a fair run of the loops refutes the
    rule ([no_lc_absurd]). *)

(** The assumed rule: a pure step that pays no fuel (and gives no later credits), yet yields
    a witness credit for each obligation of [R] that is not discharged. *)
Class lantanaGS_no_lc `(HGS : lantanaGS Λ Σ) `{!TemporalInterp Λ Σ} := {
    lwp_pure_step_no_lc :
    ∀ n s i E E' e1 e2 φ Φ,
      PureExec φ n e1 e2 →
      φ →
      Nat.iter n
        (λ P,
           |={E,E'}=> ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                          (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                           (|={E',E}=> |={E}=>m P)))
        ((|={E}=>m (lWP e2 @ s; i; E {{ v, Φ v }})))
      ⊢ lWP e1 @ s; i; E {{ Φ }};
  }.

Lemma lwp_pure_step_no_lc_alt `{!heapGS Σ} `{@lantanaGS_no_lc _ _ Σ _ _} (n : nat) R s i E E' e1 e2 φ Φ :
  PureExec φ n e1 e2 →
  φ →
  ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
  (Nat.iter n (λ P, |={E,E'}=> (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               (|={E',E}=> |={E}=>m P)))
     ((|={E}=>m (lWP e2 @ s; i; E {{ Φ }}))))
  ⊢ (lWP e1 @ s; i; E {{ Φ }}).
Proof.
  iIntros (Hexec HΦ) "(#Rs& LWP)".
  iApply (lwp_pure_step_no_lc n _ _ E E'). 1: auto.
  iStopProof. clear Hexec. pattern n. induction n.
  { simpl. iIntros "(#Rs& LWP)". auto. }
  simpl. iIntros "(#Rs& LWP)".
  iMod "LWP". iFrame "Rs".
  iIntros "!> Wcs". iMod ("LWP" with "Wcs") as "LWP".
  iApply IHn. iFrame "Rs". iModIntro. iFrame "LWP".
Qed.

Lemma tac_lwp_pure_no_lc `{!heapGS Σ} `{@lantanaGS_no_lc _ _ Σ _ _}
  Δ (s : stuckness) i E (K : list (ectxi_language.ectx_item _)) e1 e2 φ n (Φ : val → iProp Σ) :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (∃ E' R,
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
        (Nat.iter n (λ (P : iProp Σ), |={E,E'}=>
                       (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗ (|={E',E}=> |={E}=>m P)))
           ((|={E}=>m (lWP (fill K e2) @ s; i; E {{ Φ }})))))%I →
  envs_entails Δ (lWP (fill K e1) @ s; i; E {{ Φ }})%I.
Proof.
  rewrite envs_entails_unseal=> ?? ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  iIntros "(%&%& #Rs& Iter)". iApply lwp_pure_step_no_lc_alt. 1: auto.
  iFrame "Rs Iter".
Qed.

Tactic Notation "lwp_pure_no_lc" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
      let e := eval simpl in e in
        reshape_expr e ltac:(fun K e' =>
                               unify e' efoc;
                               eapply (tac_lwp_pure_no_lc _ _ _ _ K e');
                               [tc_solve                       (* PureExec *)
                               |try solve_vals_compare_safe    (* its pure condition *)
                               |idtac (* new goal *)
                            ])
        || fail "lwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "lwp_pure: not a 'lwp'"
  end.
Tactic Notation "lwp_pure_no_lc" :=
  lwp_pure_no_lc _.

Tactic Notation "lwp_rec_no_lc" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  lwp_pure_no_lc (App _ _);
  clear H.

Tactic Notation "lwp_lam_no_lc" := lwp_rec_no_lc.

Definition loop : val :=
  rec: "loop" <> :=
    "loop" #().

(** The CMRA we need. *)
Class mcntsG Σ :=
  MCounterG {
      #[local] mcnts_inG :: inG Σ (gmapUR positive mono_natUR);
      #[local] tlock_ticketG :: ghost_mapG Σ nat (oid);
    }.

Definition mcntsΣ : gFunctors :=
  #[GFunctor (gmapUR positive mono_natUR); (ghost_mapΣ nat (oid))].

Global Instance subG_mcntsΣ {Σ} : subG mcntsΣ Σ → mcntsG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !mcntsG Σ} `{@lantanaGS_no_lc _ _ Σ _ _}.

  Definition cnt_auth (γ : gname) (i : positive) n (q : Qp) : iProp Σ :=
    own γ ({[i := ●MN{#q} n]}).
  Definition cnt_lb (γ : gname) (i : positive) n : iProp Σ :=
    own γ ({[i := ◯MN n]}).
  Definition cnt_base (γ : gname) : iProp Σ :=
    own γ (∅ : gmapUR positive mono_natUR).

  Section cnt.

    Global Instance cnt_auth_timeless γ i n q : Timeless (cnt_auth γ i n q).
    Proof. rewrite /cnt_auth. apply _. Qed.
    Global Instance cnt_lb_timeless γ i n : Timeless (cnt_lb γ i n).
    Proof. rewrite /cnt_lb. apply _. Qed.

    Global Instance cnt_lb_persistent γ i n : Persistent (cnt_lb γ i n).
    Proof. rewrite /cnt_lb. apply _. Qed.

    Global Instance cnt_auth_fractional γ i n :
      Fractional (cnt_auth γ i n).
    Proof.
      rewrite /cnt_auth. intros p q.
      by rewrite -own_op singleton_op -mono_nat_auth_dfrac_op.
    Qed.
    Global Instance cnt_auth_as_fractional γ i n q :
      AsFractional (cnt_auth γ i n q) (cnt_auth γ i n) q.
    Proof. split; [auto|apply _]. Qed.

    Lemma alloc_cnt_base γ :
      ⊢ |==> cnt_base γ.
    Proof. rewrite /cnt_base. apply own_unit. Qed.

    Lemma alloc_cnt_auth γ n :
      cnt_base γ ⊢ |==> cnt_base γ ∗ ∃ i, cnt_auth γ i n 1.
    Proof.
      rewrite /cnt_base /cnt_auth. iIntros "B".
      iMod (own_updateP (λ m' : gmapUR positive mono_natUR, ∃ i, m' = <[i:=●MN n]> ∅ ∧ (∅ : gmap positive mono_natUR) !! i = None) with "B") as "(%&%& B)".
      { eapply @alloc_updateP'. 1: apply _. apply mono_nat_auth_valid. }
      destruct H0 as (?&?&?). subst. rewrite insert_singleton_op; last auto.
      iDestruct "B" as "[$ $]". auto.
    Qed.

    Lemma get_cnt_lb γ i q n1 n2 :
      n1 ≤ n2 →
      cnt_auth γ i n2 q ⊢ cnt_lb γ i n1.
    Proof.
      rewrite /cnt_auth /cnt_lb. iIntros (HLe) "H".
      assert ({[i := ●MN{#q} n2]} ≡ ({[i := ●MN{#q} n2 ⋅ ◯MN n2]} : gmap _ _)).
      { rewrite -mono_nat_auth_lb_op. done. }
      rewrite H0. iDestruct "H" as "[_ H]". rewrite (mono_nat_lb_op_le_l _ _ HLe).
      iDestruct "H" as "[$ _]".
    Qed.

    Lemma cnt_auth_op_valid γ i n1 n2 q1 q2 :
      cnt_auth γ i n1 q1 -∗ cnt_auth γ i n2 q2 -∗ ⌜ n1 = n2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
    Proof.
      rewrite /cnt_auth. iIntros "H1 H2". iCombine "H1 H2" as "H".
      iPoseProof (own_valid with "H") as "%".
      apply singleton_valid, mono_nat_auth_dfrac_op_valid in H0.
      destruct H0. done.
    Qed.

    Lemma cnt_auth_lb_valid γ i q n m :
      cnt_auth γ i n q -∗ cnt_lb γ i m -∗ ⌜ m ≤ n ∧ (q ≤ 1)%Qp ⌝.
    Proof.
      rewrite /cnt_auth /cnt_lb. iIntros "H1 H2". iCombine "H1 H2" as "H".
      iPoseProof (own_valid with "H") as "%".
      apply singleton_valid, mono_nat_both_dfrac_valid in H0.
      destruct H0. done.
    Qed.

    Lemma cnt_auth_update γ i n1 n2 :
      n1 ≤ n2 →
      cnt_auth γ i n1 1 ⊢ |==> cnt_auth γ i n2 1.
    Proof.
      rewrite /cnt_auth. iIntros (LE). apply own_update, singleton_update, mono_nat_update. auto.
    Qed.

  End cnt.

  Typeclasses Opaque cnt_auth.

  Let N := nroot .@ "paradox_inv".
  Let Nu := nroot .@ "paradox_until".
  Let N1 := nroot .@ "paradox_false".

  Definition px_inv r rm i j : iProp Σ :=
    ∃ n (os : gmap nat oid),
      (cnt_auth r j n (1/2)%Qp ∗
       ghost_map_auth_frac rm 1 os) ∗
      ([∗ map] a ↦ k ∈ os,
         ((£ (10)%ord ∨ cnt_lb r i a) ∗
          a ↪[rm]□ k ∗ cnt_lb r j a ∗ witP_layer k 0) ∗
         ((finallyI Nu k (1/2) (cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')) ∨
            (oblP_discharged k ∗ (cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')))).

  Definition px r rm i j : iProp Σ :=
    inv N (px_inv r rm i j).

  (** The main proofs. *)
  Global Instance px_persistent r i j k : Persistent (px r i j k).
  Proof. rewrite /px. apply _. Qed.

  (** Later credits come from [px_inv]. *)
  Lemma px_loop1_spec :
    ⊢ ∀ i z r rm ci cj C,
    l{{{ thread_expr i C (loop #()) ∗ thP_kids i ({[z]}) ∗
         untilI N1 z 1 True False ∗
         £ (10)%ord ∗
         px r rm ci cj ∗
         ∃ n, cnt_auth r ci n 1%Qp ∗ cnt_lb r cj n ∗
              ∃ ck, witP_layer ck 0 ∗ n ↪[rm]□ ck
      }}}
      loop #() @ i
    l{{{ RET #(); thread_expr i C #() ∗ lift_term i fork_post #() }}}.
  Proof using Type*.
    iIntros (i z r rm ci cj C).
    iIntros (Φ) "!> (TE& TG& TUz& LC& #Ipx& %& Cai& #Cljn& %& #Wckn& #Mn) HΦ".
    iEval (rewrite /px) in "Ipx".
    (** Löb induction *)
    iRevert (n ck) "Cljn Wckn Mn Cai". iLöb as "IH".
    iIntros (n ck) "#Cljn #Wckn #Mn Cai".
    (** Witness induction *)
    iPoseProof (wit_fuels_init with "Wckn") as "(%& Wfs)".
    iRevert "Wfs".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros "Wfs".
    iEval (rewrite /loop).
    (* The step returns to the same expression, so [TE] is unchanged. *)
    lwp_lam_no_lc. simpl. iExists ⊤, ({[ck]}). iSplitR.
    { rewrite big_sepS_singleton. auto. }
    iIntros "!> Wcs !> !>".
    iEval (rewrite -/loop).
    iEval (rewrite big_sepS_singleton) in "Wcs". iDestruct "Wcs" as "[Wc | #Gdckn]".
    - (** Witness induction *)
      iMod (wit_fuels_decr with "Wfs Wc") as "(%& %LTw& #Wfs'& _)".
      iPoseProof ("IHα" $! _ LTw with "TE TG TUz LC HΦ Cai Wfs'") as "LWP".
      eauto.
    - (** Counter is at least n; fetch next count and use Löb induction *)
      iApply sfmupd_fupd_l. iInv "Ipx" as "H".
      iPoseProof (tlc_split_nat 9 1 with "LC") as "[LC LCw]".
      (** TODO: interface lemmas for [tlc]; this uses the model's [lc_fupd_add_later]. *)
      iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LCw"). iNext.
      iDestruct "H" as "(%& %& (Ca& GMA)& HM)".
      iPoseProof (ghost_map_lookup with "GMA Mn") as "%LU".
      iPoseProof (big_sepM_delete _ _ _ _ LU with "HM") as "[Hm HM]".
      iDestruct "Hm" as "(Hm& [F | (_& (#Cljn1& %& #Mn1))])".
      { rewrite /finallyI !untilI_unfold. iDestruct "F" as "(Ga& _)".
        iPoseProof (oblP_assigned_discharged_false with "Ga Gdckn") as "%". done. }
      iPoseProof (big_sepM_delete _ _ _ _ LU with "[Hm $HM]") as "HM".
      { iFrame. iRight. eauto. }
      iPoseProof (ghost_map_lookup with "GMA Mn1") as "%LU1".
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "HM") as "[Hm HM]".
      iDestruct "Hm" as "(([LC1 | #Flb]& _& #Clbj1& #Wckn1)& Hm)"; cycle 1.
      { iPoseProof (cnt_auth_lb_valid with "Cai Flb") as "%". destruct H0. lia. }
      iMod (cnt_auth_update _ _ _ (n + 1) with "Cai") as "Cai".
      { lia. }
      iPoseProof (get_cnt_lb _ _ _ (n + 1) with "Cai") as "#Clbi1". 1: lia.
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "[Hm $HM]") as "HM".
      { iFrame. iFrame "Clbj1". eauto. }
      iModIntro. iSplitL "Ca GMA HM".
      { iFrame. }
      iIntros "!> !>". iApply ("IH" with "TE TG TUz LC1 HΦ Cljn1 Wckn1 Mn1 Cai").
  Qed.

  Lemma px_loop2_spec :
    ⊢ ∀ j n r rm ci cj ck C,
    l{{{ thread_expr j C (loop #()) ∗ thP_kids j {[ck]} ∗ oblP_kids ck ∅ ∗
              finallyI Nu ck (1/2) (cnt_lb r cj (n + 1) ∗ ∃ k', (n + 1) ↪[rm]□ k') ∗
              oblP_fuel ck 0 10 ∗
              px r rm ci cj ∗
              cnt_auth r cj n (1/2) ∗ n ↪[rm]□ ck }}}
      loop #() @ j
    l{{{ RET #(); thread_expr j C #() ∗ lift_term j fork_post #() }}}.
  Proof using Type*.
    iIntros (j n r rm ci cj ck C) "!> %Φ (TE& TG& Kck& Uck& Gf& #Ipx& Caj& #Mn) HΦ".
    iEval (rewrite /px) in "Ipx".
    (** Löb induction *)
    iRevert (n ck) "TG Kck Uck Gf Caj Mn". iLöb as "IH".
    iIntros (n ck) "TG Kck Uck Gf Caj #Mn".
    iEval (rewrite /loop).
    iPoseProof (oblP_fuels_init {[ck]} with "[Gf]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 100. iSplitR; first eauto. iIntros "TG GF _ LC TE".
    iEval (rewrite -/loop).
    iPoseProof (tlc_split_nat 90 10 with "LC") as "[LC LC']".
    (** TODO: better interface for sfmupd-fupd access patterns *)
    (* The next until is allocated and registered (a model update) before the invariant is
       opened. *)
    iMod (untilI_alloc _ _ _ 0 10 with "[] TG") as "(%ck1& %Nin1& TG& Kck1& Of1& #Wlk1& A)".
    { iApply parP_le_thread. }
    iMod ("A" $! _ Nu True%I (cnt_lb r cj (n + 2) ∗ ∃ k' : oid, (n + 2) ↪[rm]□ k')%I with "[//]") as "Unew".
    iApply (sfmupd_fupd_acc _ ∅).
    iMod (inv_acc with "Ipx") as "[H IpxACC]". 1: set_solver.
    iPoseProof (tlc_split_nat 89 1 with "LC") as "[LC LC1]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%& %& (Ca& GMA)& HM)".
    iAssert (⌜ os !! (n + 1)%nat = None ⌝)%I as "%Nin".
    { destruct (os !! (n + 1)) eqn:LU1; last auto.
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "HM") as "[Hm HM]".
      iDestruct "Hm" as "((_& _& #Clbj1& _)& _)". iPoseProof (cnt_auth_lb_valid with "Caj Clbj1") as "%".
      destruct H0. lia. }
    iPoseProof (ghost_map_lookup with "GMA Mn") as "%LU".
    iPoseProof (big_sepM_delete _ _ _ _ LU with "HM") as "[Hm HM]".
    iDestruct "Hm" as "(Hm& [Uck1 | (#F& _)])"; cycle 1.
    { rewrite /finallyI !untilI_unfold. iDestruct "Uck" as "(Ga& _)".
      iPoseProof (oblP_assigned_discharged_false with "Ga F") as "%". done. }
    iPoseProof (untilI_frac_add with "Uck Uck1") as "Uck".
    { rewrite Qp.div_2. reflexivity. }
    iPoseProof (cnt_auth_op_valid with "Caj Ca") as "%". destruct H0 as [? _]. subst n0.
    iCombine "Ca Caj" as "Caj".
    iMod (cnt_auth_update _ _ _ (n + 1) with "Caj") as "[Caj Caj2]". 1: lia.
    iPoseProof (get_cnt_lb _ _ _ (n + 1) (n + 1) with "Caj") as "#Cljn1". 1: lia.
    iMod (ghost_map_insert_persist (n + 1) ck1 with "GMA") as "[GMA #Mn1]". 1: auto.
    assert (NDisj : N ## Nu).
    { subst N Nu. apply ndot_ne_disjoint. done. }
    iMod (untilI_discharge with "Uck") as "H"; first set_solver.
    iPoseProof (tlc_split_nat 88 1 with "LC") as "[LC LC1]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(_& H)".
    iPoseProof ("H" $! (PThread j) ({[ck1]} ∪ {[ck]}) with "[] TG Kck []") as "H".
    { iPureIntro. set_solver. }
    { iFrame "Cljn1". iExists _. iExact "Mn1". }
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "mask" as "_".
    iMod "H" as "(_& TG& #Ofck)".
    iDestruct "Unew" as "[Unew Unew1]".
    iMod ("IpxACC" with "[Caj2 GMA Hm LC' Unew1 HM]") as "_".
    { iNext. iFrame "Caj2 GMA". iApply big_sepM_insert. 1: auto. iSplitL "LC' Unew1".
      { iFrame. iSplitR; first eauto. iLeft. replace (n + 1 + 1) with (n + 2) by lia. iFrame. }
      iApply (big_sepM_delete _ _ _ _ LU). iFrame. iRight. eauto. }
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    replace (({[ck1]} ∪ {[ck]}) ∖ {[ck]}) with ({[ck1]} : gset oid) by set_solver.
    iModIntro. iMod "mask" as "_". iIntros "!>".
    iApply ("IH" with "TE HΦ TG Kck1 [Unew] Of1 Caj Mn1").
    replace (n + 1 + 1) with (n + 2) by lia. iFrame.
  Qed.

  Lemma px_init E j :
    thP_kids j ∅
    -∗ |={E}=>m ∃ ck r rm ci cj n,
                thP_kids j {[ck]} ∗ oblP_kids ck ∅ ∗ oblP_fuel ck 0 10 ∗
                finallyI Nu ck (1/2) (cnt_lb r cj (n + 1) ∗ ∃ k', (n + 1) ↪[rm]□ k') ∗
                witP_layer ck 0 ∗
                px r rm ci cj ∗ cnt_auth r ci n 1%Qp ∗ cnt_auth r cj n (1/2) ∗
                cnt_lb r cj n ∗  n ↪[rm]□ ck.
  Proof.
    iIntros "TG".
    set (r := inhabitant : gname).
    iMod (alloc_cnt_base r) as "CB".
    iMod (alloc_cnt_auth _ 0 with "CB") as "(CB& %ci& CAi)".
    iPoseProof (get_cnt_lb with "CAi") as "#Cli". 1: reflexivity.
    iMod (alloc_cnt_auth _ 0 with "CB") as "(CB& %cj& CAj)".
    iPoseProof (get_cnt_lb with "CAj") as "#Clj". 1: reflexivity.
    iMod (ghost_map_alloc (∅ : gmap nat oid)) as "(%rm& GM& _)".
    iMod (untilI_alloc _ _ _ 0 10 with "[] TG") as "(%ck& _& TG& Kck& Gf& #Wl& ACC)".
    { iApply parP_le_thread. }
    rewrite union_empty_r_L.
    iMod ("ACC" $! _ Nu True%I (cnt_lb r cj (0 + 1) ∗ ∃ k', (0 + 1) ↪[rm]□ k')%I with "[//]") as "HF".
    iMod (ghost_map_insert_persist 0 ck with "GM") as "(GM& #GMe)". 1: done.
    iExists ck, r, rm, ci, cj, 0.
    iDestruct "HF" as "[HF HF0]". iDestruct "CAj" as "[CAj CAj0]".
    iFrame. iFrame "Wl Clj GMe".
    rewrite /px.
    iMod (inv_alloc N _ (px_inv r rm ci cj) with "[-]") as "#H". 2: iModIntro; iFrame "H".
    iNext. rewrite /px_inv. iExists 0, {[0 := ck]}.
    iFrame. iApply big_sepM_singleton. iSplitR "HF".
    - iFrame "GMe Clj Wl". iRight. eauto.
    - iLeft. iFrame.
  Qed.

  Lemma px_loop_pre Θ i j (Φ : iProp Σ) Ψs :
    i ≠ j →
    Θ = {[i := loop #(); j := loop #() ]} →
    Φ = ((∃ z ck r rm ci cj n,
             untilI N1 z 1 True False ∗
             finallyI Nu ck (1/2) (cnt_lb r cj (n + 1) ∗ ∃ k', (n + 1) ↪[rm]□ k') ∗
             (£ (10)%ord ∗
              px r rm ci cj ∗ cnt_auth r ci n 1%Qp ∗ cnt_auth r cj n (1/2) ∗
              cnt_lb r cj n ∗  n ↪[rm]□ ck ∗
              witP_layer ck 0 ∗
              thP_kids i {[z]} ∗
              thP_kids j {[ck]} ∗ oblP_kids ck ∅ ∗ oblP_fuel ck 0 10))%I) →
    Ψs = ({[i := fork_post; j := fork_post]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗ £ (10)%ord -∗
     ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
     |={⊤}=>m (Φ ∗
              (Φ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ i; ⊤ {{ lift_term i Ψ }}))).
  Proof using H.
    iIntros (Hij HT HP HQ) "TEs LC TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    iPoseProof (big_sepS_union with "TGs") as "[TG1 TG2]".
    { set_solver. }
    rewrite !big_sepS_singleton.
    iPoseProof (px_loop1_spec) as "px_loop1_spec".
    iPoseProof (px_loop2_spec) as "px_loop2_spec".
    iMod (untilI_alloc _ _ _ 1 0 with "[] TG1") as "(%z& _& TG1& _& _& _& ACC)".
    { iApply parP_le_thread. }
    iMod ("ACC" $! _ N1 True%I False%I with "[//]") as "HFz".
    rewrite !union_empty_r_L.
    iMod (px_init ⊤ with "TG2") as "(%&%&%&%&%&%& TG2& Kck& Gf& HFck& #Wl& #px& CAi& CAj& #Clj& #GMe)".
    iModIntro. iSplitR "TEs".
    { subst Φ.
      iExists z, ck, r, rm, ci, cj, n. iFrame. iFrame "px Clj GMe Wl". }
    iClear "Wl px Clj GMe". clear dependent z ck r rm ci cj n.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (z ck r rm ci cj n) "(HFz& HFck& LC& #px& CAi& CAj& #Clj& #GMe& #Wl& TG1& TG2& Kck& Gf)".
    iEval (rewrite HT big_sepM_insert; last by rewrite lookup_singleton_ne) in "TEs".
    iDestruct "TEs" as "[TEi TEs]".
    iEval (rewrite big_sepM_singleton) in "TEs". iRename "TEs" into "TEj".
    iPoseProof ("px_loop1_spec" $! i z r rm ci cj [] (λ v, lift_term i fork_post v)
                 with "[$TEi $TG1 $HFz $LC $px $CAi $Clj $Wl $GMe]") as "WP1".
    iPoseProof ("px_loop2_spec" $! j n r rm ci cj ck [] (λ v, lift_term j fork_post v)
                 with "[$TEj $TG2 $Kck $HFck $Gf $px $CAj $GMe]") as "WP2".
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { rewrite lookup_insert_ne; auto. }
    { rewrite lookup_insert_ne; auto. }
    iSplitL "WP1".
    { iApply "WP1". iIntros "[_ $]". }
    rewrite big_sepM2_singleton. iApply "WP2". iIntros "[_ $]".
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let j : thread_id := 2%positive.
  Let Θ0 : thread_pool heap_lang := {[i := loop #(); j := loop #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  Let R_main : trProp heap_lang :=
        (tr_eventually ⌜ False ⌝ ∧ tr_eventually ⌜ True ⌝)%R.

  Let Nu := nroot .@ "paradox_until".
  Let N1 := nroot .@ "paradox_false".

  Let Φ_P `{!heapGS Σ} `{!mcntsG Σ} : iProp Σ :=
        (∃ z ck r rm ci cj n,
            untilI N1 z 1 True False ∗
            finallyI Nu ck (1/2) (cnt_lb r cj (n + 1) ∗ ∃ k', (n + 1) ↪[rm]□ k') ∗
            (£ (10 : Ord.t)%ord ∗
             px r rm ci cj ∗ cnt_auth r ci n 1%Qp ∗ cnt_auth r cj n (1/2) ∗
             cnt_lb r cj n ∗  n ↪[rm]□ ck ∗
             witP_layer ck 0 ∗
             thP_kids i {[z]} ∗
             thP_kids j {[ck]} ∗ oblP_kids ck ∅ ∗ oblP_fuel ck 0 10))%I.

  (** The trace property guaranteed by the final resources, as inferred. *)
  Section G_main.
    Context `{!heapGS Σ} `{!mcntsG Σ}.
    Definition G_main : itProp heap_lang Σ := ltac:(itProp_of Φ_P).
  End G_main.

  Lemma Φ_P_temporal `{!heapGS Σ} `{!mcntsG Σ} : ⊢ Φ_P ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : itProp_external (G_main (Σ:=Σ)) τ → R_main τ.
  Proof.
    destruct τ as [n τf]. intros (Hf& (m& Hm& _& Hb)& _). split; first exact Hf.
    exists m. split_and!; [done|done|]. intros. done.
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ;
          mcntsΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post; j := fork_post]}.

  Theorem loop_paradox :
    (∀ Λ0 Σ0 (HGS : lantanaGS Λ0 Σ0) (TI : TemporalInterp Λ0 Σ0), @lantanaGS_no_lc _ Λ0 Σ0 HGS TI) →
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    R_main τ.
  Proof.
    intros LNLC τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main (R_main)).
    { apply G_main_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists (10 : Ord.t)%ord.
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { iDestruct "PI" as "[PI _]". by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (px_loop_pre (heapGS0:=HHeapGS) Θ0 i j (Φ_P (heapGS0:=HHeapGS)) with "[Tis] [$LC] [TGs]") as "H".
    { subst i j. lia. }
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as "(HP& H)".
    iModIntro. iExists Φ_P. iFrame "HP H". iApply Φ_P_temporal.
  Qed.

  (** ** The no-credit rule is unsound *)
  (** A fair run of the two loops: thread [i] steps at even times and [j] at odd times; every
      step takes [loop #()] to [loop #()]. *)
  Lemma loop_prim_step k σ tids :
    prim_step k (loop #()) σ tids [] (loop #()) σ ∅.
  Proof. apply ectx_language.base_prim_step. by econstructor. Qed.

  Let ρ0 : cfg heap_lang := (Θ0, Build_state σ0 ∅).
  Let sched (n : nat) : thread_id := if Nat.even n then i else j.
  Let loop_run : trace heap_lang := (0, λ n, (ρ0, sched n, [])).

  Lemma loop_run_behavior n : behavior (n, loop_run.2).
  Proof.
    revert n. cofix IH. intros n.
    eapply (behavior_step n _ ρ0 ρ0 (sched n) (sched (S n)) [] []); [done| |done|apply IH].
    assert (Hk : Θ0 !! sched n = Some (loop #())).
    { rewrite /Θ0 /sched. destruct (Nat.even n); by simplify_map_eq. }
    left. eapply (thread_step_atomic (loop #()) _ (loop #()) _ ∅ Θ0); [done|exact Hk|apply loop_prim_step|].
    rewrite /ρ0 right_id_L insert_id //.
  Qed.

  Lemma loop_run_fair : fair_scheduling loop_run.
  Proof.
    intros m _ k. simpl. rewrite /ρ0 /Θ0.
    destruct (decide (k = i ∨ k = j)) as [Hk|Hk].
    - right. split.
      + exists (loop #()). split; last done. destruct Hk as [->| ->]; by simplify_map_eq.
      + destruct Hk as [->| ->].
        * exists (2 * m). simpl. split; first lia. split; last done.
          rewrite /ts_emb /thread_turn /sched /=. replace (m + (m + 0)) with (2 * m) by lia.
          rewrite Nat.even_mul. done.
        * exists (1 + 2 * m). simpl. split; first lia. split; last done.
          rewrite /ts_emb /thread_turn /sched /=. replace (m + (m + 0)) with (2 * m) by lia.
          change (match 2 * m with 0 => false | S n' => Nat.even n' end) with (Nat.even (S (2 * m))).
          rewrite Nat.even_succ Nat.odd_mul. done.
    - left. left. assert (k ≠ i ∧ k ≠ j) as [Hi Hj] by tauto. by simplify_map_eq.
  Qed.

  (** Assuming the rule, [loop_paradox] gives "eventually False" on this run. *)
  Theorem no_lc_absurd :
    (∀ Λ0 Σ0 (HGS : lantanaGS Λ0 Σ0) (TI : TemporalInterp Λ0 Σ0), @lantanaGS_no_lc _ Λ0 Σ0 HGS TI) →
    False.
  Proof.
    intros LNLC.
    destruct (loop_paradox LNLC loop_run) as [Hf _].
    - apply loop_run_behavior.
    - apply loop_run_fair.
    - done.
    - done.
    - destruct Hf as (m& _& Hm& _). done.
  Qed.

End adequacy.
