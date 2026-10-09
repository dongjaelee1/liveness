(** [main] (§2), the client of the flag module: its specification, proved with the rules of
    [triple.v] and the flag specifications in the paper's format ([Flag_init_fbspec],
    [Flag_set_fbspec], [Flag_wait_fbspec]), and its adequacy theorems. *)
From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From lantana.heap_lang Require Import triple.
From lantana.program_logic Require Import adequacy_iris.
From iris.prelude Require Import options.
From iris.proofmode Require Import coq_tactics.

From lantana.heap_lang.examples Require Export flag.

Module FlagFork.

  Definition main : val :=
    λ: <>,
      (* alloc a flag x and forks a set-thread and wait *)
      let: "x" := Flag.init #() in
      Fork (Flag.set "x");;
      Flag.wait "x";;
      #42.

End FlagFork.

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

  (** The closed specification of [main], in the paper's format: it ends with no carriers. The
      proof follows §2's walkthrough step by step. *)
  Lemma FlagFork_main_fbspec :
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

  (** The same specification in the form [main_pre] uses: the thread has terminated. *)
  Lemma FlagFork_main_spec :
    ⊢ ∃ μ, ∀ i g kr,
    l{{{ thread_expr i [] (FlagFork.main #()) ∗ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_fuel g (1)%ordi μ) ∗
         crP_obls g 1 {[kr]} ∗
         ⟦finallyP Nr kr 1 (exits #42@i)⟧ₗ }}}
      FlagFork.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof FlagFork_main_fbspec as (μ) "#H". iExists μ. iIntros (i g kr).
    iApply (fbtriple_top_texan with "H"). iIntros (v) "[Td ->]". rewrite /lift_term. by iFrame.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := FlagFork.main #() ]} →
    Φ = (λ μ, (∃ g kr, finallyP Nr kr 1 (exits #42@i) ∗
                       ⟨thP_carriers i {[g]} ∗ crP_obls g 1 {[kr]} ∗
                        crP_fuel g 1 μ⟩)%F) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (⟦Φ μ⟧ₗ ∗
                   (⟦Φ μ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (FlagFork_main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 1 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nr (⌜True⌝)%F (exits #42@i)%F with "[]") as "Ukl1".
    { tf_red. done. }
    iModIntro. iExists μ. iSplitL "Ukl1 TG1 Gg1 Gf1 Ofkl1".
    { subst Φ.
      tf_red. iExists g1. tf_red. iExists kl1. tf_red.
      rewrite !union_empty_r_L. iFrame. }
    iClear "Wlkl1". clear dependent g1 kl1.
    iIntros "HP". subst Φ.
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(HF& TG& Cg& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i g1 kl1 (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v) with "[TEs TG Cg GF HF]") as "WP".
    { iFrame. by iApply big_sepS_singleton. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iModIntro. eauto. iIntros (?) "(_& %& H)". rewrite /lift_term.
      iDestruct "H" as "[$ _]". eauto. }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := FlagFork.main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  Let Φ : tp :=
        (tp_finally (exits #42@i))%P.

  Let Φ' : tp :=
        (∃ (g : ocid) (kr : oid),
            tp_finally (exits #42@i) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    simpl. unfold_trProp. intros. destruct τ. destruct H as (?&?&?&?).
    firstorder.
  Qed.

  Let Nr := nroot.@ "flag_fork_ret".

  Let Φ_tf `{!heapGS Σ} : _ → tf Σ :=
        λ μ,
          (∃ g kl,
              finallyP Nr kl 1 (exits #42@i) ∗
              ⟨thP_carriers i {[g]} ∗ crP_obls g 1 {[kl]} ∗
               crP_fuel g 1 μ⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} m :
    tf_to_tp (Φ_tf m) = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #42⌝)%I]}.

  Theorem main_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    apply Φ_impl.
    eapply (lwp_adequacy Σ heap_lang (Build_state σ0 ∅) Θ0 i [] Φ').
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (main_pre Θ0 i with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_tf μ). iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

  (** Safety: in every fair behavior, the scheduled thread is never stuck, and once [main]
      has returned, its value is [#42]. *)
  Theorem main_safety_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    safety_iris i (λ _ v, v = #42) τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_safety_iris Σ heap_lang (Build_state σ0 ∅) Θ0 i [] i).
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iModIntro. iSplit.
    { iPureIntro. eexists. split; first apply lookup_singleton_eq.
      intros v. iIntros "%Hv". by iPureIntro. }
    iSplitL "HI TI PI".
    { by iFrame. }
    iSplitR; first done.
    iIntros "LC TGs".
    iMod (main_pre Θ0 i with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iApply ("H" with "HP").
  Qed.

  (** Liveness and safety together, over the same fair behaviors: [main] returns [#42], and no
      scheduled thread is ever stuck. *)
  Corollary main_liveness_safety :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ ∧ (safety_iris i (λ _ v, v = #42) τ).
  Proof.
    intros τ Beh FS Init1 Init2. split.
    - by apply main_adequacy.
    - by apply main_safety_adequacy.
  Qed.

End adequacy.

(* Print Assumptions main_adequacy. *)
