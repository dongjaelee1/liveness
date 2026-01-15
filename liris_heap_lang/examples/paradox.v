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
                      ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
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
                       (thread_exec i q -∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗ (|={E',E}=> P)))
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

  End cnt.

  Context (N N_inv N1 : namespace).
  Hypothesis N_disj_1 : N ## N_inv.

  Definition cnt_ξ : gl_witness := λ _, 100.
  Definition cnt_ηξ : gl_witness := λ v, gupd_η (Σ[cnt_ξ] v).

  Definition px_inv r i j k : iProp Σ :=
    ∃ n, cnt_auth r j n (1/2)%Qp ∗
         ([∗ list] a ∈ seq 0 (S n), (£ 100 ∨ cnt_lb r i a) ∗
                                    gl k a ∗ wit k a (cnt_ηξ a) ∗
                                    gl_variant N_inv k a True (cnt_lb r j (a + 1)) (cnt_lb r j (a + 1))).

  Definition px r i j k : iProp Σ :=
    ∃ x, gl_done x 0 ∗ gl_variant N x 0 False (px_inv r i j k) False.

  (** The main proofs. *)
  Global Instance px_persistent r i j k : Persistent (px r i j k).
  Proof. rewrite /px. apply _. Qed.

  (** Receives later credits via px_inv *)
  Lemma px_loop1_spec i α r ci cj ck :
    l{{{ thread_exec i 1 ∗ th_obls i (<[α:=0]>∅) 1 ∗ gl_variant N1 α 0 True False False ∗
         px r ci cj ck ∗
         ∃ n, cnt_auth r ci n 1%Qp ∗
              cnt_lb r cj n ∗ gl ck n ∗ wit ck n (cnt_ηξ n) ∗
              gl_variant N_inv ck n True (cnt_lb r cj (S n)) (cnt_lb r cj (S n)) }}}
      loop #() @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "(Tx& TG& #GVα& (%x& #Gdx& #GVx)& %n& Cai& #Cljn& #Gckn& #Wckn& #GVckn) HΦ".
    (* iApply fupd_lwp. *)
    (* iMod (gl_variant_acc_done with "Gdx GVx") as "[[H | H] ACC]". 1: done. *)
    (* 2:{ iMod "H" as "[_ %]". done. } *)
    (** Lob induction *)
    iRevert (n) "Gckn Cljn Wckn GVckn Cai". iLöb as "IH".
    rewrite /loop.
    lwp_lam_no_lc. iExists _, ⊤,  iFrame "Tx".

  Abort.

  Lemma px_loop2_spec j r ci cj ck :
    l{{{ thread_exec j 1 ∗ th_obls j (<[ck:=0]>∅) 1 ∗ gl_fuel ck 100 ∗
         px r ci cj ck ∗ cnt_auth r cj 0 (1/2)%Qp }}}
      loop #() @ j
    l{{{ RET #(); lift_term j fork_post #() }}}.
  Proof.

  Abort.

  Lemma px_writer_spec i l :
    l{{{ ∃ k, mp k l ∗
              thread_exec i 1 ∗ th_obls i (<[k:=0]>∅) 1 ∗
              gl_fuel k (Σ[px_ξ] 0) }}}
      writer #l @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    (* iApply lwp_sfgupd. *)
    iDestruct "HP" as "(%& (#Gwfk& #Gk& #Wkv& #GVkv)& Tx& TG& Gfk)".
    rewrite /writer /=.
    iMod (gl_fuel_lt k 100 with "Gfk") as "[Gfk Gfk1]".
    { apply Ord.omega_upperbound. }
    (* Pure steps *)
    lwp_lam. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done.
    iSplitL "Gfk1".
    { iModIntro. rewrite big_sepM_singleton. iFrame. }
    iIntros "!> Tx TG _ !> _ !>".
    lwp_finish.
    iMod (gl_fuel_mon_split k 99 1 with "Gfk") as "[Gfk Gfk1]".
    { rewrite -Hessenberg.add_from_nat. reflexivity. }
    lwp_bind (Store _ _).
    iMod (gl_unlock with "TG GVkv") as "[>(TG& Glk& VP) ACC]".
    { set_solver. }
    { rewrite lookup_insert_eq. auto. }
    iApply lwp_sfgupd.
    iApply (lwp_store _ ∅ 0 with "[$VP $Tx $TG Gfk1]").
    { rewrite !big_sepM_singleton. iFrame. by iApply big_sepM_empty. }
    iIntros "[(_& Tx& TG& _) ptl]".
    iPoseProof ("ACC" with "TG Glk ptl") as ">ACC".
    iModIntro. iMod "ACC" as "(TG& Gc& #Gd)". iModIntro.
    (* simpl. *)
    lwp_pure.
    simpl. iFrame "Tx". iExists ⊤, ∅, ∅, 0. iSplitR; first done. iModIntro. iSplitL "TG".
    { rewrite delete_insert_id; auto. }
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    lwp_pure.
    simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    iApply (lwp_exit with "TG Tx [HΦ]").
    iModIntro. iIntros "#Tt1 #Tt2". iIntros "!>".
    iApply "HΦ". rewrite /lift_term. iFrame "Tt1".
    rewrite -thread_term_unfold. auto.
  Qed.

  Lemma px_reader_spec i l :
    l{{{ ∃ k, mp k l ∗
              thread_exec i 1 ∗ th_obls i ∅ 1 }}}
      reader #l @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as "(%& (#Gwfk& #Gk& #Wkv& #GVkv)& Tx& TG)".
    rewrite /reader /=.
    (* Liveness induction *)
    remember (px_ηξ 0) as a. clear Heqa.
    iStopProof. induction a using WFOCM.ind. rename x into a, H into IHa.
    iIntros "(#(Gwfk& Gk& Wkv& GVkv)& Tx& TG& HΦ)".
    (* Pure steps *)
    lwp_rec. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    lwp_bind (Load _).
    iMod (gl_variant_acc with "GVkv") as "[>PQR ACC]". 1: set_solver.
    iDestruct "PQR" as "[[HP | HQ] | HR]"; cycle -1.
    { iDestruct "HR" as "[_ %]". done. }
    - iDestruct "HP" as "[Glk ptr]".
      iApply (lwp_load _ (<[k:=0]>∅) 0 with "[$ptr $Tx $TG]").
      { rewrite big_sepM_singleton. iSplitR; first done. auto. }
      iIntros "[(_& Tx& TG& Rs) ptr]".
      rewrite big_sepM_singleton. iDestruct "Rs" as "[Wck | #Gdk]"; cycle 1.
      { iPoseProof (gl_locked_done_false with "Glk Gdk") as "%". done. }
      iMod ("ACC" with "[Glk ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iLeft. iFrame. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      iMod (wit_credit_spend_one with "Wkv Wck") as "(%& %LTa& #Wkv')".
      iApply (IHa a0 LTa). iFrame. auto.
    - iDestruct "HQ" as "[#Gdk ptr]".
      iApply (lwp_load _ ∅ 0 with "[$ptr $Tx $TG]").
      { iSplit; done. }
      iIntros "[(_& Tx& TG& _) ptr]".
      iMod ("ACC" with "[ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iRight. iFrame. auto. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      iApply (lwp_exit with "TG Tx [HΦ]").
      iModIntro. iIntros "#Tt1 #Tt2". iIntros "!>".
      iApply "HΦ". rewrite /lift_term. iFrame "Tt1".
      rewrite -thread_term_unfold. auto.
  Qed.

End proof.
