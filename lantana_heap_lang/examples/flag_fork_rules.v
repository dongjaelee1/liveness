(** The proof of [main] (§2), using only the rules of [triple.v] and the flag specifications in
    the paper's format ([Flag_init_fbspec], [Flag_set_fbspec], [Flag_wait_fbspec]). It follows
    the paper's walkthrough step by step. [flag_fork.v] proves the same specification
    ([FlagFork_main_fbspec]) directly with [lwp]. *)
From iris.proofmode Require Import proofmode.
From lantana.heap_lang Require Import notation proofmode triple.
From lantana.heap_lang.examples Require Import flag flag_fork.
From iris.prelude Require Import options.
From iris.proofmode Require Import coq_tactics.

(** * Derived rules

    Each is derived from the rules of [triple.v]. They let a proof keep its resources in the
    context, with triples whose precondition is [True]. *)
Section derived.
  Context `{!heapGS Σ}.
  Implicit Types (P : iProp Σ) (Q : val → iProp Σ) (e : expr) (v : val).
  Implicit Types (G : gset ocid) (i : thread_id) (C : list ectx_item).

  (** Move the precondition into the context ([fbtriple_wand_pre]). *)
  Lemma fb_intro s i C E G G' P e Q :
    (P -∗ ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G') ⊢ ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros "H". iApply (fbtriple_conseq _ _ _ _ _ _ (True ∗ P)%I P e Q Q with "[] [] [H]").
    - by iIntros "$".
    - by iIntros (v) "$".
    - by iApply fbtriple_wand_pre.
  Qed.

  (** Supply a precondition from the context (consequence). *)
  Lemma fb_pre s i C E G G' (R : iProp Σ) e Q :
    R -∗ ⦃ R ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G' -∗ ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros "HR H". iApply (fbtriple_conseq with "[HR] [] H").
    - iIntros "_". iExact "HR".
    - by iIntros (v) "$".
  Qed.

  (** Eliminate an update (UPD-ELIM). *)
  Lemma fb_upd s i C E G G' (R : iProp Σ) e Q :
    (|={E}=> R) -∗ (R -∗ ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G') -∗
    ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros "HR H". iApply (fb_pre with "HR"). iApply fbtriple_upd_elim. by iApply fb_intro.
  Qed.

  (** A pure step in the evaluation context [K] ([fbtriple_pure_step]). *)
  Lemma fb_pure s i C E G G' K e1 e2 φ Q :
    PureExec φ 1 e1 e2 → φ →
    fuels G 0 1 -∗ ⦃ True ⦄^G fill K e2 @ s; i; C; E ⦃ v, Q v ⦄^G' -∗
    ⦃ True ⦄^G fill K e1 @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros (Hexec Hφ) "F H". iApply (fb_pre _ _ _ _ _ _ (fuels G 0 1 ∗ True)%I with "[F]").
    { by iFrame. }
    iApply (fbtriple_pure_step _ _ _ _ _ _ True%I (fill K e1) (fill K e2) φ _ Ord.O);
      [by apply pure_exec_fill|done|].
    iApply (fbtriple_conseq with "[] [] H"); [by iIntros "_"|by iIntros (v) "$"].
  Qed.

  (** Call a function at the evaluation context [K] (BIND). *)
  Lemma fb_call s i C E K G0 G1 G2 P e Q1 (R : val → iProp Σ) :
    ⦃ P ⦄^G0 e @ s; i; K ++ C; E ⦃ v, Q1 v ⦄^G1 -∗ P -∗
    (∀ v, Q1 v -∗ ⦃ True ⦄^G1 fill K (of_val v) @ s; i; C; E ⦃ w, R w ⦄^G2) -∗
    ⦃ True ⦄^G0 fill K e @ s; i; C; E ⦃ w, R w ⦄^G2.
  Proof.
    iIntros "H HP Hk". iApply (fb_pre with "HP").
    iApply (fbtriple_bind with "H"). iIntros (v). iApply fb_intro. iApply "Hk".
  Qed.

  (** CARRIER-ALLOC. *)
  Lemma fb_alloc s i C E G G' ℓ μ e Q :
    (∀ g, ⌜g ∉ G⌝ -∗ crP_obls g ℓ ∅ -∗ fuels {[g]} ℓ μ -∗
          ⦃ True ⦄^({[g]} ∪ G) e @ s; i; C; E ⦃ v, Q v ⦄^G') -∗
    ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros "H". iApply (fbtriple_carrier_alloc _ _ _ _ _ _ ℓ μ). iIntros (g Hg).
    iApply fb_intro. iIntros "(_& Cg& Fg)". by iApply ("H" with "[//] Cg Fg").
  Qed.

  (** CARRIER-DELETE. *)
  Lemma fb_delete s i C E G G' g ℓ e Q :
    g ∈ G →
    crP_obls g ℓ ∅ -∗ ⦃ True ⦄^(G ∖ {[g]}) e @ s; i; C; E ⦃ v, Q v ⦄^G' -∗
    ⦃ True ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    iIntros (Hg) "Cg H". iApply (fb_pre _ _ _ _ _ _ (True ∗ crP_obls g ℓ ∅)%I with "[Cg]").
    { by iFrame. }
    by iApply (fbtriple_carrier_delete _ _ _ _ _ _ g ℓ True%I _ _ Hg with "H").
  Qed.

  (** EXIT, for a thread that ends with no carriers. *)
  Lemma fb_exit s i C E v :
    ⊢ ⦃ True ⦄^∅ (of_val v) @ s; i; C; E ⦃ _, True ⦄^∅.
  Proof.
    iApply (fbtriple_conseq _ _ _ _ _ _ True%I True%I (of_val v) (λ w, ⌜w = v⌝)%I
              (λ _, True)%I with "[] [] []"); last iApply fbtriple_exit.
    - by iIntros "_".
    - by iIntros (w) "_".
  Qed.

  Lemma tac_fb_pure Δ s i C E G G' K e1 e2 φ Q :
    PureExec φ 1 e1 e2 → φ →
    envs_entails Δ (fuels G 0 1 ∗ ⦃ True ⦄^G fill K e2 @ s; i; C; E ⦃ v, Q v ⦄^G') →
    envs_entails Δ (⦃ True ⦄^G fill K e1 @ s; i; C; E ⦃ v, Q v ⦄^G').
  Proof.
    rewrite envs_entails_unseal => ?? ->. iIntros "[F H]". by iApply (fb_pure with "F H").
  Qed.
End derived.

(** [fb_pure H]: take the next pure step, burning the fuel [H] ([fuels G 0 1]). *)
Tactic Notation "fb_pure" constr(H) :=
  iStartProof;
  let Hrec := fresh in assert (Hrec := AsRecV_recv);
  lazymatch goal with
  | |- envs_entails _ (fbtriple _ _ _ _ _ _ _ ?e _) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      eapply (tac_fb_pure _ _ _ _ _ _ _ K e');
      [tc_solve|try done|iSplitL H; [iExact H|]])
    || fail "fb_pure: no pure redex in" e
  end;
  clear Hrec.

(** [fb_call efoc pat]: call the subexpression [efoc] (BIND), with the spec pattern [pat] for the
    call's triple and its precondition. *)
Tactic Notation "fb_call" open_constr(efoc) constr(pat) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (fbtriple _ _ _ _ _ _ _ ?e _) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      iApply (fb_call _ _ _ _ K with pat))
    || fail "fb_call: cannot find" efoc "in" e
  end.

(** * The proof of [main] *)
Section proof.
  Context `{!heapGS Σ}.

  Let Nr := nroot.@ "flag_fork_ret".

  Lemma FlagFork_main_fbspec_rules :
    ⊢ □ ∃ μ, ∀ i g kr,
    ⦃ fuels {[g]} (1)%ordi μ ∗ crP_obls g 1 {[kr]} ∗ ⟦finallyP Nr kr 1 (exits #42@i)⟧ₗ ⦄^{[g]}
      FlagFork.main #() @ i; []; ⊤
    ⦃ v, ⌜v = #42⌝ ⦄^∅.
  Proof.
    iIntros "!>".
    (** The setup destructs the three specifications for their budgets. *)
    iDestruct Flag_init_fbspec as (μ_init) "#Hinit".
    iDestruct Flag_set_fbspec as (μ_set) "#Hset".
    iDestruct Flag_wait_fbspec as (μ_wait) "#Hwait".
    (** [g_e]'s layer-1 budget: one unit for the layer-0 phase, [μ_wait] for [wait], and one
        unit for the steps after it. *)
    iExists (1 ⊕ (μ_wait ⊕ 1))%M. iIntros (i ge kr).
    iApply fb_intro. iIntros "(F& Ce& HF)".
    iDestruct (fuels_add with "F") as "[F0 F]".
    iDestruct (fuels_add with "F") as "[Fw Fend]".
    (** FUELS-LAYER: the unit becomes the layer-0 budget [1 ⊕ μ0]: one step for the call of
        [main], and [μ0] for [init] and the five steps up to [wait]. *)
    set (μ0 := (μ_init ⊕ (1 ⊕ (1 ⊕ (1 ⊕ (1 ⊕ 1)))))%M).
    iApply (fb_upd with "[F0]").
    { iMod (fuels_layer _ 0 1 (1 ⊕ μ0)%M with "F0") as "F0".
      { apply ordArith.lt_from_nat. lia. }
      iModIntro. iExact "F0". }
    iIntros "F0". iDestruct (fuels_add with "F0") as "[F00 F0]".
    rewrite /FlagFork.main.
    fb_pure "F00".
    (** CARRIER-ALLOC allocates [g_f] at layer 0 with budget [μ0], and FUELS-UNION merges the
        two carriers' layer-0 fuel. *)
    iApply (fb_alloc _ _ _ _ _ _ 0 μ0). iIntros (gf Hgf) "Cf Ff".
    iAssert (fuels ({[gf]} ∪ {[ge]}) 0 μ0) with "[F0 Ff]" as "F0".
    { iApply fuels_union. replace ({[gf]} ∖ {[ge]}) with ({[gf]} : gset ocid) by set_solver.
      iFrame. }
    iDestruct (fuels_add with "F0") as "[Fi F0]".
    (** SPEC-INIT, with [g = g_f] and [m = 1]. *)
    fb_call (Flag.init _) "[] [Fi Cf]".
    { iApply ("Hinit" $! 0 i ({[gf]} ∪ {[ge]}) gf ∅ 0 1). }
    { iFrame. }
    iIntros (v) "(%x& %kf& -> & _& _& Cf& Of& Ftk& #Hflag)".
    rewrite union_empty_r_L.
    (** The let-binding takes two pure steps. *)
    iDestruct (fuels_add with "F0") as "[F1 F0]". fb_pure "F1".
    iDestruct (fuels_add with "F0") as "[F1 F0]". fb_pure "F1".
    (** FORK*: [k_f] moves to the child, together with [isFlag] and [FlagObl]. The child runs
        SPEC-SET, then CARRIER-DELETE and EXIT. *)
    iDestruct (fuels_add with "F0") as "[F1 F0]".
    fb_call (Fork _) "[] [F1 Cf Of Ftk]".
    { iApply (fbtriple_fork1 _ _ _ _ _ gf 0 μ_set kf (flag_tk x kf ∗ is_flag x kf 0)%I _ Ord.O).
      iIntros (j g2). iApply fb_intro. iIntros "(Fs& Cs& Ftk& #Hflag')".
      fb_call (Flag.set _) "[] [Fs Cs Ftk]".
      { iApply ("Hset" $! 0 j x {[g2]} g2 {[kf]} kf 0 0). }
      { iFrame "Fs Cs Ftk Hflag'". iPureIntro. set_solver. }
      iIntros (v) "(_& _& Cs& _)". rewrite difference_diag_L.
      iApply (fb_delete with "Cs"); first set_solver. rewrite difference_diag_L.
      iApply fb_exit. }
    { iFrame "F1 Cf Of Ftk Hflag". }
    (** Back on the parent, [g_f] is empty, and CARRIER-DELETE drops it. *)
    iIntros (w) "(-> & Cf& _)".
    iApply (fb_delete with "Cf"); first set_solver.
    replace (({[gf]} ∪ {[ge]}) ∖ {[gf]}) with ({[ge]} : gset ocid) by set_solver.
    iDestruct (fuels_weaken _ {[ge]} with "F0") as "F0"; first set_solver.
    (** The sequence takes two pure steps. *)
    iDestruct (fuels_add with "F0") as "[F1 F0]". fb_pure "F1". fb_pure "F0".
    (** SPEC-WAIT, with fuel at layer [0 ⊕ 1], which is layer 1. *)
    iDestruct (fuels_layer_eq _ _ (0 ⊕ 1)%ordi _ (hessenberg.add_from_nat 0 1) with "Fw") as "Fw".
    fb_call (Flag.wait _) "[] [Fw]".
    { iApply ("Hwait" $! 0 i x {[ge]} kf 0). }
    { iFrame "Fw Hflag". }
    iIntros (w') "(-> & _& _)".
    (** The last unit of layer-1 fuel covers the two remaining steps (FUELS-LAYER). *)
    iApply (fb_upd with "[Fend]").
    { iMod (fuels_layer _ 0 1 (1 ⊕ 1)%M with "Fend") as "F".
      { apply ordArith.lt_from_nat. lia. }
      iModIntro. iExact "F". }
    iIntros "F". iDestruct (fuels_add with "F") as "[F1 F]".
    fb_pure "F1".
    (** FINALLY-EXIT*: the last step, the β-step to [#42], discharges the exit obligation [k_e]
        and retires [g_e]. *)
    iApply (fb_pre _ _ _ _ _ _
              (fuels {[ge]} 0 1 ∗ crP_obls ge 1 {[kr]} ∗ ⟦finallyP Nr kr 1 (exits #42@i)⟧ₗ)%I
              with "[$F $Ce $HF]").
    pose proof AsRecV_recv.
    iApply (fbtriple_finally_exit _ _ _ _ _ _ _ _ _ True); 
      [exact (pure_beta BAnon BAnon (Val #42) (RecV BAnon BAnon (Val #42)) #1)
      |done|solve_ndisj].
  Qed.
End proof.
