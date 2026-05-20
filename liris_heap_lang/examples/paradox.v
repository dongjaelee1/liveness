From iris.bi Require Import lib.fractional.
From iris.algebra Require Import gmap mono_nat.
From iris.proofmode Require Import proofmode.
(* From transfinite.base_logic Require Import lib.ghost_map. *)
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.

(** "pure" steps that are reducible with the thread_exec predicate, without submitting fuels. *)
Class heapGS_no_lc `(HGS : heapGS Σ) := {
    lwp_pure_step_no_lc :
    ∀ n s i E E' e1 e2 φ Φ,
      PureExec φ n e1 e2 →
      φ →
      Nat.iter n
        (λ P,
           |={E,E'}=> ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                          (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                           (|={E',E}=> |={E}=>m P)))
        (lwpupd i E e2 (lWP e2 @ s; i; E {{ v, Φ v }}))
      ⊢ lWP e1 @ s; i; E {{ Φ }};    
  }.

Lemma lwp_pure_step_no_lc_alt `{!heapGS Σ} `{@heapGS_no_lc Σ _} (n : nat) R s i E E' e1 e2 φ Φ :
  PureExec φ n e1 e2 →
  φ →
  ([∗ set] r ∈ R, oblP_id r) ∗
  (Nat.iter n (λ P, |={E,E'}=> (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                               (|={E',E}=> |={E}=>m P)))
     (lwpupd i E e2 (lWP e2 @ s; i; E {{ Φ }})))
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

Lemma tac_lwp_pure_no_lc `{!heapGS Σ} `{@heapGS_no_lc Σ _}
  Δ (s : stuckness) i E (K : list (ectxi_language.ectx_item _)) e1 e2 φ n (Φ : val → iProp Σ) :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (∃ E' R,
        ([∗ set] r ∈ R, oblP_id r) ∗
        (Nat.iter n (λ (P : iProp Σ), |={E,E'}=>
                       (([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗ (|={E',E}=> |={E}=>m P)))
           (lwpupd i E (fill K e2) (lWP (fill K e2) @ s; i; E {{ Φ }}))))%I →
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

(** The program. *)
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
  Let Nu := nroot .@ "paradox_until".
  Let N1 := nroot .@ "paradox_false".

  Definition px_inv_tf r rm i j : tf Σ :=
    (∃ n (os : gmap nat oid),
        ⟨cnt_auth r j n (1/2)%Qp ∗
         ghost_map_auth rm 1 os⟩ ∗
        ([^tf_sep map] a ↦ k ∈ os,
           ⟨(£ (10)%ord ∨ cnt_lb r i a) ∗
            a ↪[rm]□ k ∗ cnt_lb r j a ∗
            oblP_id k ∗ witP_layer k 0⟩ ∗
           ((tf_eventually Nu k false (1/2) ⟨(cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')⟩) ∨
              (⟨oblP_fulfilled k ∗ (cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')⟩))))%F.

  Definition px_tf r rm i j : tf Σ :=
    tf_always N (px_inv_tf r rm i j).

  Definition px_inv r rm i j : iProp Σ :=
    ∃ n (os : gmap nat oid),
      (cnt_auth r j n (1/2)%Qp ∗
       ghost_map_auth rm 1 os) ∗
      ([∗ map] a ↦ k ∈ os,
         ((£ (10)%ord ∨ cnt_lb r i a) ∗
          a ↪[rm]□ k ∗ cnt_lb r j a ∗
          oblP_id k ∗ witP_layer k 0) ∗
         ((⟦tf_eventually Nu k false (1/2) ⟨(cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')⟩⟧ₗ) ∨
            (oblP_fulfilled k ∗ (cnt_lb r j (a + 1) ∗ ∃ k', (a + 1) ↪[rm]□ k')))).

  Definition px r rm i j : iProp Σ :=
    inv N (px_inv r rm i j).

  Lemma px_inv_red r rm i j :
    ⟦px_inv_tf r rm i j⟧ₗ ⊣⊢ px_inv r rm i j.
  Proof.
    rewrite /px_inv_tf /px_inv. 
    tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. f_equiv.
    rewrite tf_big_opM_interp. do 3 f_equiv. tf_red. f_equiv. done.
  Qed.

  Lemma px_red r rm i j :
    ⟦px_tf r rm i j⟧ₗ ⊣⊢ px r rm i j.
  Proof.
    rewrite /px_tf /px. tf_red. f_equiv. apply px_inv_red.
  Qed.

  (** The main proofs. *)
  Global Instance px_persistent r i j k : Persistent (px r i j k).
  Proof. rewrite /px. apply _. Qed.

  (** Receives later credits via px_inv *)
  Lemma px_loop1_spec i g z r rm ci cj :
    l{{{ thP_groups i ({[g]}) ∗
         ogP_obls i g 1 {[z]} ∗
         ⟦tf_until N1 z false 1 (⌜ True ⌝) (⌜ False ⌝)⟧ₗ ∗
         £ (10)%ord ∗
         px r rm ci cj ∗
         ∃ n, cnt_auth r ci n 1%Qp ∗ cnt_lb r cj n ∗
              ∃ ck, oblP_id ck ∗ witP_layer ck 0 ∗ n ↪[rm]□ ck
      }}}
      loop #() @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof using Type*.
    iIntros (Φ) "(TG& Gg& TUz& LC& #Ipx& %& Cai& #Cljn& %& #Gckn& #Wckn& #Mn) HΦ".
    (** Lob induction *)
    iRevert (n ck) "Cljn Gckn Wckn Mn Cai". iLöb as "IH".
    iIntros (n ck) "#Cljn #Gckn #Wckn #Mn Cai".
    (** Witness induction *)
    iPoseProof (wit_fuels_init with "Wckn") as "(%& Wfs)".
    iRevert "Wfs".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros "Wfs".
    iEval (rewrite /loop).
    lwp_lam_no_lc. simpl. iExists ⊤, ({[ck]}). iSplitR.
    { rewrite big_sepS_singleton. auto. }
    iIntros "!> Wcs !> !>".
    iEval (rewrite -/loop).
    iEval (rewrite big_sepS_singleton) in "Wcs". iDestruct "Wcs" as "[Wc | #Gdckn]".
    - (** Witness induction *)
      iMod (wit_fuels_decr with "Wfs Wc") as "(%& %LTw& #Wfs'& _)".
      iPoseProof ("IHα" $! _ LTw with "TG Gg TUz LC HΦ Cai Wfs'") as "LWP".
      eauto.
    - (** Counter is at least n; fetch next count and use Löb induction *)
      iApply lwpupd_fupd_l. iInv "Ipx" as "H".
      iPoseProof (tlc_split_nat 9 1 with "LC") as "[LC LCw]".
      (** TODO: make interface defs and lemmas for tlc *)
      iApply (lc_fupd_add_later with "LCw"). iNext.
      iDestruct "H" as "(%& %& (Ca& GMA)& HM)".
      iPoseProof (ghost_map_lookup with "GMA Mn") as "%LU".
      iPoseProof (big_sepM_delete _ _ _ _ LU with "HM") as "[Hm HM]".
      iDestruct "Hm" as "(Hm& [F | (_& (#Cljn1& %& #Mn1))])".
      { rewrite /tf_eventually tf_until_logic. iDestruct "F" as "(Ga& _)".
        iPoseProof (oblP_assigned_fulfilled_false with "Ga Gdckn") as "%". done. }
      iPoseProof (big_sepM_delete _ _ _ _ LU with "[Hm $HM]") as "HM".
      { iFrame. iRight. eauto. }
      iPoseProof (ghost_map_lookup with "GMA Mn1") as "%LU1".
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "HM") as "[Hm HM]".
      iDestruct "Hm" as "(([LC1 | #Flb]& _& #Clbj1& #Gckn1& #Wckn1)& Hm)"; cycle 1.
      { iPoseProof (cnt_auth_lb_valid with "Cai Flb") as "%". destruct H0. lia. }
      iMod (cnt_auth_update _ _ _ (n + 1) with "Cai") as "Cai".
      { lia. }
      iPoseProof (get_cnt_lb _ _ _ (n + 1) with "Cai") as "#Clbi1". 1: lia.
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "[Hm $HM]") as "HM".
      { iFrame. iFrame "Clbj1". eauto. }
      iModIntro. iSplitL "Ca GMA HM".
      { iFrame. }
      iIntros "!> !>". iApply ("IH" with "TG Gg TUz LC1 HΦ Cljn1 Gckn1 Wckn1 Mn1 Cai").
  Qed.

  Lemma px_loop2_spec j n r rm ci cj ck :
    l{{{ ∃ g, thP_groups j {[g]} ∗
              ogP_obls j g 0 {[ck]} ∗
              ⟦tf_eventually Nu ck false (1/2) ⟨(cnt_lb r cj (n + 1) ∗ ∃ k', (n + 1) ↪[rm]□ k')⟩⟧ₗ ∗
              ogP_fuel g 0 10 ∗
              px r rm ci cj ∗
              cnt_auth r cj n (1/2) ∗ n ↪[rm]□ ck }}}
      loop #() @ j
    l{{{ RET #(); lift_term j fork_post #() }}}.
  Proof using Type*.
    iIntros (Φ) "(%& TG& Gg& Uck& Gf& #Ipx& Caj& #Mn) HΦ".
    (** Lob induction *)
    iRevert (n g ck) "TG Gg Uck Gf Caj Mn". iLöb as "IH".
    iIntros (n g ck) "TG Gg Uck Gf Caj #Mn".
    iEval (rewrite /loop).
    rewrite (ogP_fuel_eq g 0 10 (9 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add with "Gf") as "[_ Gf1]".
    lwp_lam. iEval (simpl). iFrame "TG". iExists ⊤, ∅, 100. iSplitR; first done.
    iModIntro. iSplitL "Gf1".
    { rewrite big_sepS_singleton. iFrame. }
    iIntros "TG _ !> LC !>".
    iEval (rewrite -/loop).
    iPoseProof (tlc_split_nat 90 10 with "LC") as "[LC LC']".
    (** TODO: better interface for sfmupd-fupd access patterns *)
    iApply (sfmupd_fupd_acc _ ∅).
    iMod (inv_acc with "Ipx") as "[H IpxACC]". 1: set_solver.
    iPoseProof (tlc_split_nat 89 1 with "LC") as "[LC LC1]".
    (** TODO: make interface defs and lemmas for tlc *)
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%& %& (Ca& GMA)& HM)".
    iAssert (⌜ os !! (n + 1)%nat = None ⌝)%I as "%Nin".
    { destruct (os !! (n + 1)) eqn:LU1; last auto.
      iPoseProof (big_sepM_delete _ _ _ _ LU1 with "HM") as "[Hm HM]".
      iDestruct "Hm" as "((_& _& #Clbj1& _)& _)". iPoseProof (cnt_auth_lb_valid with "Caj Clbj1") as "%".
      destruct H0. lia. }
    iPoseProof (ghost_map_lookup with "GMA Mn") as "%LU".
    iPoseProof (big_sepM_delete _ _ _ _ LU with "HM") as "[Hm HM]".
    iDestruct "Hm" as "(Hm& [Uck1 | (#F& _)])"; cycle 1.
    { rewrite /tf_eventually tf_until_logic. iDestruct "Uck" as "(Ga& _)".
      iPoseProof (oblP_assigned_fulfilled_false with "Ga F") as "%". done. }
    iPoseProof (tf_until_frac_add with "Uck Uck1") as "Uck".
    { rewrite Qp.div_2. reflexivity. }
    iPoseProof (cnt_auth_op_valid with "Caj Ca") as "%". destruct H0 as [? _]. subst n0.
    iCombine "Ca Caj" as "Caj".
    iMod (cnt_auth_update _ _ _ (n + 1) with "Caj") as "[Caj Caj2]". 1: lia.
    iPoseProof (get_cnt_lb _ _ _ (n + 1) (n + 1) with "Caj") as "#Cljn1". 1: lia.
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    iMod (group_alloc _ _ _ 0 10 with "TG") as "(%g'& %Ning'& TG& Gg'& Gf')".
    iMod (tf_until_alloc _ _ _ _ false 0 0 10 with "Gg'") as "(%ck1& %Nin1& Gg'& #Ok1& Of1& #Wlk1& A)". 1: by left.
    iApply fupd_sfmupd_elim. iMod "mask" as "_".
    iMod ("A" $! _ Nu ⌜True⌝%F ⟨ cnt_lb r cj (n + 2) ∗ ∃ k' : oid, (n + 2) ↪[rm]□ k' ⟩%F with "[//]") as "Unew".
    iMod (ghost_map_insert_persist (n + 1) ck1 with "GMA") as "[GMA #Mn1]". 1: auto.
    assert (NDisj : N ## Nu).
    { subst N Nu. apply ndot_ne_disjoint. done. }
    iMod (tf_until_fulfill with "Uck") as "H". 1: set_solver.
    iPoseProof (tlc_split_nat 88 1 with "LC") as "[LC LC1]".
    (** TODO: make interface defs and lemmas for tlc *)
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(_& H)".
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "mask" as "_".
    iMod ("H" with "[]") as "H".
    { iNext. tf_red. eauto. }
    iPoseProof ("H" with "[] Gg") as "H".
    { iPureIntro. set_solver. }
    iPoseProof (tlc_split_nat 87 1 with "LC") as "[LC LC1]".
    (** TODO: make interface defs and lemmas for tlc *)
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "mask" as "_".
    iMod "H" as "(_& Gg& #Ofck)".
    iDestruct "Unew" as "[Unew Unew1]".
    iMod ("IpxACC" with "[Caj2 GMA Hm LC' Unew1 HM]") as "_".
    { iNext. iFrame "Caj2 GMA". iApply big_sepM_insert. 1: auto. iSplitL "LC' Unew1".
      { iFrame. iSplitR; first eauto. iLeft. replace (n + 1 + 1) with (n + 2) by lia. iFrame. }
      iApply (big_sepM_delete _ _ _ _ LU). iFrame. iRight. eauto. }
    iApply (fupd_mask_intro). 1: set_solver. iIntros "mask".
    replace ({[ck]} ∖ {[ck]}) with (∅ : gset oid) by set_solver.
    iMod (group_delete with "TG Gg") as "TG".
    replace ({[g'; g]} ∖ {[g]}) with ({[g']} : gset _) by set_solver.
    rewrite union_empty_r_L.
    iModIntro. iMod "mask" as "_". iIntros "!> !>".
    iApply ("IH" with "HΦ TG Gg' [Unew] Gf' Caj Mn1").
    replace (n + 1 + 1) with (n + 2) by lia. iFrame.
  Qed.

End proof.
