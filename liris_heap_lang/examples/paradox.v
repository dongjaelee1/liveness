From iris.bi Require Import lib.fractional.
From iris.algebra Require Import gmap mono_nat.
From iris.proofmode Require Import proofmode.
(* From transfinite.base_logic Require Import lib.ghost_map. *)
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export weakestpre.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.

(** "pure" steps that are reducible with the thread_exec predicate, without submitting fuels. *)
Class heapGS_no_lc `(HGS : heapGS Σ) := {
    lwp_pure_step_no_lc :
    ∀ n R s i q E E' e1 e2 φ Φ,
      PureExec φ thread_cond n e1 e2 →
      φ →
      ([∗ map] r↦v ∈ R, gl r v) ∗
      Nat.iter n
        (λ P,
           |={E,E'}=> thread_exec i q ∗
                     (thread_exec i q -∗
                      ([∗ map] r↦v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
                      (|={E',E}=> P)))
        (lWP e2 @ s; i; E {{ v, Φ v }})
      ⊢ lWP e1 @ s; i; E {{ Φ }};    
  }.

Lemma tac_lwp_pure_no_lc `{!heapGS Σ} `{@heapGS_no_lc Σ _}
  Δ (s : stuckness) i E (K : list (ectxi_language.ectx_item _)) e1 e2 φ n (Φ : val → iProp Σ) :
  PureExec φ thread_cond n e1 e2 →
  φ →
  envs_entails Δ (∃ q E' R,
        ([∗ map] r↦v ∈ R, gl r v) ∗
        (Nat.iter n (λ P, |={E,E'}=>
                       thread_exec i q ∗
                       (thread_exec i q -∗ ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗ (|={E',E}=> P)))
           (lWP (fill K e2) @ s; i; E {{ Φ }})))%I →
  envs_entails Δ (lWP (fill K e1) @ s; i; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  iIntros "(%&%&%& #Rs& Iter)". iApply lwp_pure_step_no_lc. 1: auto.
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
                               |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
                               (* |tc_solve                       (* IntoLaters *) *)
                               |idtac (* new goal *)
                                  (* |idtac "use lwp_finish to cleanup new lwp"    (* new goal *) *)
                                  (* |lwp_finish                      (* new goal *) *)
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

Tactic Notation "lwp_if_no_lc" := lwp_pure_no_lc (If _ _ _).
Tactic Notation "lwp_if_true_no_lc" := lwp_pure_no_lc (If (LitV (LitBool true)) _ _).
Tactic Notation "lwp_if_false_no_lc" := lwp_pure_no_lc (If (LitV (LitBool false)) _ _).
Tactic Notation "lwp_unop_no_lc" := lwp_pure_no_lc (UnOp _ _).
Tactic Notation "lwp_binop_no_lc" := lwp_pure_no_lc (BinOp _ _ _).
Tactic Notation "lwp_op_no_lc" := lwp_unop_no_lc || lwp_binop_no_lc.
Tactic Notation "lwp_lam_no_lc" := lwp_rec_no_lc.
Tactic Notation "lwp_let_no_lc" := lwp_pure_no_lc (Rec BAnon (BNamed _) _).
Tactic Notation "lwp_seq_no_lc" := lwp_pure_no_lc (Rec BAnon BAnon _).
Tactic Notation "lwp_proj_no_lc" := lwp_pure_no_lc (Fst _) || lwp_pure_no_lc (Snd _).
Tactic Notation "lwp_case_no_lc" := lwp_pure_no_lc (Case _ _ _).
Tactic Notation "lwp_inj_no_lc" := lwp_pure_no_lc (InjL _) || lwp_pure_no_lc (InjR _).
Tactic Notation "lwp_pair_no_lc" := lwp_pure_no_lc (Pair _ _).
Tactic Notation "lwp_closure_no_lc" := lwp_pure_no_lc (Rec _ _ _).

Definition loop : val := 
  rec: "loop" <> :=
    "loop" #().

(** Monotone counters *)
Class mcntsG Σ :=
  MCounterG {
      #[local] mcnts_inG :: inG Σ (gmapUR positive mono_natUR);
    }.

Definition mcntsΣ : gFunctors :=
  #[GFunctor (gmapUR positive mono_natUR)].

Global Instance subG_mcntsΣ {Σ} : subG mcntsΣ Σ → mcntsG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !mcntsG Σ} `{@heapGS_no_lc Σ _}.

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
      iMod (own_updateP (λ m', ∃ i, m' = <[i:=●MN n]> ∅ ∧ ∅ !! i = None) with "B") as "(%&%& B)".
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
  Let N_inv := nroot .@ "paradox_cnt".
  Let N1 := nroot .@ "paradox_false".

  Let ℓs : layers := (λ _, 0).

  Definition px_inv r i j k : iProp Σ :=
    ∃ n, cnt_auth r j n (1/2)%Qp ∗
         ([∗ list] a ∈ seq 0 (S n), (£ (1)%ord ∨ cnt_lb r i a) ∗
                                    gl k a ∗ wit_layer k a 0 ∗
                                    gl_variant N_inv k a True (cnt_lb r j (a + 1)) (cnt_lb r j (a + 1))).

  Definition px r i j k : iProp Σ :=
    ∃ x, gl_done x 0 ∗ gl_variant N x 0 False (px_inv r i j k) False.

  (** The main proofs. *)
  Global Instance px_persistent r i j k : Persistent (px r i j k).
  Proof. rewrite /px. apply _. Qed.

  (** Receives later credits via px_inv *)
  Lemma px_loop1_spec i z r ci cj ck :
    l{{{ thread_exec i 1 ∗ th_obls i (<[z:=0]>∅) 1 ∗
         gl_variant N1 z 0 True False False ∗
         £ (1)%ord ∗ px r ci cj ck ∗
         ∃ n, cnt_auth r ci n 1%Qp ∗
              cnt_lb r cj n ∗ gl ck n ∗ wit_layer ck n 0 ∗
              gl_variant N_inv ck n True (cnt_lb r cj (S n)) (cnt_lb r cj (S n)) }}}
      loop #() @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof using Type*.
    iIntros (Φ) "(Tx& TG& #GVz& LC& (%x& #Gdx& #GVx)& %n& Cai& #Cljn& #Gckn& #Wckn& #GVckn) HΦ".
    (** Lob induction *)
    iRevert (n) "Gckn Cljn Wckn GVckn Cai". iLöb as "IH".
    iIntros (n) "#Gckn #Cljn #Wckn #GVckn Cai".
    (** Witness induction *)
    iPoseProof (wit_fuels_init with "Wckn") as "(%& Wfs)".
    (* iPoseProof (tlc_split with "LC") as "[LC LCw]". *)
    (** TODO: make interface defs and lemmas for tlc *)
    (* iApply fupd_lwp. iApply rupd_fupd. iMod (tlc_weaken _ w with "LCw") as "LCw". *)
    (* { subst w. apply lf_cnt_ηξ_lt. } *)
    (* iModIntro. *)
    iRevert "Wfs".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros "#Wfs".
    iEval (rewrite /loop).
    lwp_lam_no_lc. iExists _, ⊤, (<[ck:=n]>∅). iFrame "Tx". iSplitR.
    { rewrite big_sepM_singleton. auto. }
    iIntros "!> Tx Wcs !>". lwp_finish.
    iEval (rewrite -/loop).
    rewrite big_sepM_singleton. iDestruct "Wcs" as "[Wc | #Gdckn]".
    - (** Witness induction *)
      iMod (wit_fuels_decr with "Wfs Wc") as "(%& %LTw& #Wfs'& _)".
      (* iApply fupd_lwp. iApply rupd_fupd. iMod (tlc_weaken _ a0 with "LCw") as "LCw". *)
      (* { apply Ord.lt_le; auto. }       *)
      iPoseProof ("IHα" $! _ LTw with "Tx TG LC HΦ Cai [Wfs']") as "LWP".
      { auto. }
      auto.
    - (** Version n is done; fetch next version and use Löb induction *)
      iAssert (|={⊤}=> cnt_lb r cj (S n))%I with "[]" as ">#Cljn0".
      { iMod (gl_variant_acc_done with "Gdckn GVckn") as "[[>#H | >(Gex& #H)] ACC]". 1: set_solver.
        - iMod ("ACC" with "[]") as "_"; auto.
          iNext. iApply gl_variant_cases_unfold. iLeft. iRight. auto.
        - iMod ("ACC" with "[Gex]") as "_"; auto.
          iNext. iApply gl_variant_cases_unfold. iRight. auto.
      }
      (** TODO: non-atomic invariant access *)
      iApply fupd_lwp. iMod (gl_variant_acc_done with "Gdx GVx") as "[[H | >[_ %HF]] ACC]".
      1: set_solver. 2: done.
      (** TODO: interface lemmas for lwp_lc_later in lifting. also fupd and later-mod comm? *)
      iCombine "IH H" as "H". iMod (lc_fupd_elim_later with "LC H") as "H".
      iClear "IH". iDestruct "H" as "[IH H]". iDestruct "H" as "(%& Caj& Cs)".
      iPoseProof (cnt_auth_lb_valid with "Caj Cljn0") as "%". destruct H0 as [Le _].
      rewrite (seq_S n0) big_sepL_snoc. iDestruct "Cs" as "[Cs (LC& #Gckn0& #Wckn0& #GVckn0)]".
      iDestruct "LC" as "[LC | #Clin0]"; cycle 1.
      { iPoseProof (cnt_auth_lb_valid with "Cai Clin0") as "%". destruct H0.
        exfalso. lia. }
      iPoseProof (get_cnt_lb _ _ _ n0 n0 with "Caj") as "#Cljn0'". 1: auto.
      iMod (cnt_auth_update _ _ _ n0 with "Cai") as "Cai".
      { lia. }
      iPoseProof (get_cnt_lb _ _ _ n0 with "Cai") as "#Clin0". 1: auto.
      iPoseProof (big_sepL_snoc with "[$Cs]") as "Cs".
      { iFrame "Clin0". eauto. }
      rewrite -(seq_S n0). iMod ("ACC" with "[Caj Cs]") as "_".
      { iNext. iApply gl_variant_cases_unfold. iLeft. iRight. rewrite /px_inv. iFrame. eauto. }
      iModIntro. iPoseProof ("IH" with "Tx TG LC HΦ") as "H".
      iPoseProof ("H" $! n0 with "Gckn0 Cljn0' Wckn0 [GVckn0] Cai") as "H".
      { simpl. replace (S n0) with (n0 + 1) by lia. eauto. }
      iFrame.
  Qed.

  Lemma px_loop2_spec j n r ci cj ck :
    l{{{ thread_exec j 1 ∗ th_obls j (<[ck:=n]>∅) 1 ∗
         gl_variant N_inv ck n True (cnt_lb r cj (n + 1)) (cnt_lb r cj (n + 1)) ∗
         gl_layers ck ℓs ∗ gl_fuel ck 0 10 ∗
         px r ci cj ck ∗ cnt_auth r cj n (1/2)%Qp }}}
      loop #() @ j
    l{{{ RET #(); lift_term j fork_post #() }}}.
  Proof using Type*.
    iIntros (Φ) "(Tx& TG& #GVck& #Gw& Gf& (%x& #Gdx& #GVx)& Caj) HΦ".
    (** Lob induction *)
    iRevert (n) "GVck TG Gf Caj". iLöb as "IH".
    iIntros (n) "#GVck TG Gf Caj".
    iEval (rewrite /loop).
    rewrite (gl_fuel_eq ck 0 0 10 (9 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (gl_fuel_add with "Gf") as "[_ Gf1]".
    lwp_lam. iFrame "Tx TG". iExists ⊤, ∅, 2. iSplitR; first done.
    iModIntro. iSplitL "Gf1".
    { rewrite insert_empty dom_singleton_L big_sepS_singleton. eauto. }
    iIntros "Tx TG _ !> LC !>". lwp_finish.
    iEval (rewrite -/loop).
    iPoseProof (tlc_split_nat 1 1 with "LC") as "[LC LC1]".
    (** TODO: better interface for sfgupd-fupd access patterns *)
    iApply sfgupd_elim_lwp. iApply (sfgupd_fupd_acc _ ∅).
    iMod (gl_variant_acc_done with "Gdx GVx") as "[[H | >[_ %HF]] ACC]".
    1: set_solver. 2: done.
    (** TODO: interface lemmas for lwp_lc_later in lifting. also fupd and later-mod comm? *)
    iCombine "IH H" as "H". iMod (lc_fupd_elim_later with "LC1 H") as "H".
    iClear "IH". iDestruct "H" as "[IH H]". iDestruct "H" as "(%& Caj2& Cs)".
    iPoseProof (cnt_auth_op_valid with "Caj Caj2") as "%". destruct H0 as [? _]. subst n0.
    iCombine "Caj Caj2" as "Caj".
    iMod (cnt_auth_update _ _ _ (n + 1) with "Caj") as "[Caj Caj2]". 1: lia.
    iPoseProof (get_cnt_lb _ _ _ (n + 1) (n + 1) with "Caj") as "#Cljn1". 1: lia.
    assert (NDisj : N ## N_inv).
    { subst N N_inv. apply ndot_ne_disjoint. done. }
    iMod (gl_unlock with "TG GVck") as "[>(TG& Glock& _) ACC2]".
    { set_solver. }
    { rewrite lookup_insert_eq. done. }
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iMod ("ACC2" with "TG Glock Cljn1") as "ACC2".
    iApply fupd_sfgupd_elim. iMod "close" as "_". iMod "ACC2" as "(TG& Gcur& #Gdckn)".
    iMod (gl_lock ∅ _ _ ∅ _ _ _ _ _ _ (n + 1) _ _ _ True (cnt_lb r cj (n + 2)) (cnt_lb r cj (n + 2))
           with "Gcur Gdckn GVck") as "[>[Gcur _] ACC2]".
    1: lia. 1: set_solver.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iMod ("ACC2" with "[TG] Gcur Gw [//]") as "ACC2".
    { rewrite delete_insert_id. 1: iFrame. done. }
    iMod "ACC2" as "((TG& %& #Glckn1& Gf& #GVckn1& #Wckn1& _& _)& ACC2)".
    iApply fupd_sfgupd_elim. iMod "close" as "_".
    iMod ("ACC2" with "Cljn1") as "_".
    iMod ("ACC" with "[LC Cs Caj2]") as "_".
    { iNext. iApply gl_variant_cases_unfold. iLeft. iRight. rewrite /px_inv.
      iFrame "Gdx Caj2". rewrite (seq_S (n + 1)). iApply big_sepL_app.
      replace (S n) with (n + 1) by lia. iFrame "Cs".
      iApply big_sepL_singleton. iEval (simpl). replace (n + 1 + 1) with (n + 2) by lia.
      iFrame "LC Glckn1 Wckn1 GVckn1".
    }
    iApply fupd_mask_intro. 1: set_solver. iIntros "close !>". iMod "close" as "_". iModIntro.
    iApply ("IH" with "Tx HΦ [GVckn1] TG [Gf] Caj").
    { replace (n + 1 + 1) with (n + 2) by lia. auto. }
    { replace (S n) with (n + 1) by lia. auto. }
  Qed.

End proof.
