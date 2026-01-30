From iris.proofmode Require Import proofmode.
From liris.prelude Require Import axioms.
From liris.algebra Require Export execution.
From liris.program_logic Require Export total_weakestpre.

Section adequacy.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Local Definition Ψ : Type := (expr Λ).
  Local Definition ΨR i : Ψ → Ψ → Prop :=
    λ e1 e2,
      ∀ σ1 Θ1, reducible i e1 σ1 Θ1 → ∃ κ σ2 efs, prim_step i e1 σ1 Θ1 κ e2 σ2 efs.
  (* Local Definition Ψ : Type := (expr Λ * state Λ * thread_ids * list (observation Λ)). *)
  (* Local Definition ΨR i : Ψ → Ψ → Prop := *)
  (*   λ '(e1, σ1, Θ1, κs1) '(e2, σ2, Θ2, κs2), *)
  (*     ∃ κ, κs1 = κ ++ κs2 ∧ ∃ efs, Θ2 = Θ1 ∪ (dom efs) ∧ prim_step i e1 σ1 Θ1 κ e2 σ2 efs. *)

  Local Lemma ΨR_classical i ψ :
    (ex_loop (ΨR i) ψ) ∨ (∃ (μ : ord_tree Ψ), Acc_ord_tree (flip (ΨR i)) ψ μ).
  Proof.
    destruct (classic (ex_loop (ΨR i) ψ)); first auto.
    right. apply not_ex_loop_sn in H. apply Acc_Acc_ord_tree in H. auto.
  Qed.

  (* define loop wp that is inductive and angelic, and insert False in the postcond *)

  Lemma twp_ex_loop_false s i E e Φ :
    (tWP e @ s; i; E {{ Φ }})
    ⊢ (⌜ ex_loop (ΨR i) e ⌝) -∗
    ∀ σ Θ κ κs Ω W, state_interp σ Θ (κ ++ κs) -∗ gproto Ω W Θ -∗ |={E}=> False.
  Proof.
    iApply (twp_ind s (λ i E e Φ, (⌜ ex_loop (ΨR i) e ⌝) -∗ ∀ σ Θ κ κs Ω W, state_interp σ Θ (κ ++ κs) -∗ gproto Ω W Θ -∗ |={E}=> False)%I with "[]").
    clear i E e Φ. iIntros "!> %i %e %E %Φ IH %Hloop %σ %Θ %κ %κs %Ω %W SI G".
    inversion Hloop as [e1 e2 HR Hloop']. clear Hloop. subst.
    rewrite /twp_pre. rewrite (val_stuck _ _ _ _ _ _ _ _ Step).
    destruct (HR σ Θ) as (σ2& Θ2& κs2& κ& Hκ& efs& HΘ& Step). subst.
    iMod ("IH" with "SI") as "IH".
    iMod (gproto_gupd_steps with "IH G") as "[(%Red& IH) (%&%& G)]".
    iMod ("IH" with "[//] G") as "[G IH]".
    iMod (gproto_gupd_steps with "IH G") as "[>(SI& [IH _]) (%&%& G)]".
    iApply ("IH" with "[//] SI G").
  Qed.

  (* Lemma twp_ex_loop_false s i E e Φ : *)
  (*   (tWP e @ s; i; E {{ Φ }}) *)
  (*   ⊢ ∀ σ Θ κs Ω W, (⌜ ex_loop (ΨR i) (e, σ, Θ, κs) ⌝) -∗ *)
  (*                   state_interp σ Θ κs -∗ *)
  (*                   gproto Ω W Θ -∗ *)
  (*                   |={E}=> False. *)
  (* Proof. *)
  (*   iApply (twp_ind s (λ i E e Φ, ∀ σ Θ κs Ω W, (⌜ ex_loop (ΨR i) (e, σ, Θ, κs) ⌝) -∗ state_interp σ Θ κs -∗ gproto Ω W Θ -∗ |={E}=> False)%I with "[]"). *)
  (*   clear i E e Φ. iIntros "!> %i %e %E %Φ IH %σ %Θ %κs %Ω %W %Hloop SI G". *)
  (*   inversion Hloop as [(((e1& σ1)& Θ1)& κs1) (((e2& σ2)& Θ2)& κs2) HR Hloop']. clear Hloop. subst. *)
  (*   destruct HR as (κ& Hκ& efs& HΘ& Step). subst. *)
  (*   rewrite /twp_pre. rewrite (val_stuck _ _ _ _ _ _ _ _ Step). *)
  (*   iMod ("IH" with "SI") as "IH". *)
  (*   iMod (gproto_gupd_steps with "IH G") as "[(%Red& IH) (%&%& G)]". *)
  (*   iMod ("IH" with "[//] G") as "[G IH]". *)
  (*   iMod (gproto_gupd_steps with "IH G") as "[>(SI& [IH _]) (%&%& G)]". *)
  (*   iApply ("IH" with "[//] SI G"). *)
  (* Qed. *)

  Lemma twp_lwp s i E e Φ G R :
    TCEq (to_val e) None →
    (tWP e @ s; i; E {{ λ v, th_obls i G 1 -∗ ([∗ map] r↦u ∈ R, wit r u Ord.one ∨ gl_done r u) -∗ Φ v }})
    ⊢ th_obls i G 1 -∗
    ([∗ map] g↦v ∈ G, ∀ μ0, ∃ ℓ μ, ⌜ (measure 0ₗ%L μ0 <= measure ℓ μ)%ord ⌝ ∗ gl_fuel g ℓ μ) -∗
    ([∗ map] r↦v ∈ R, gl r v) -∗
    lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hnv) "TWP TG Fs Rs".
    destruct (ΨR_classical i e) as [Loop | [μ Term]].
    { iApply sfgupd_elim_lwp. iIntros "%%% SI". iApply fupd_mask_intro. 1: set_solver.
      iIntros "close". iApply gupd_unfold. iRight. iIntros "%% G".
      iPoseProof (twp_ex_loop_false with "TWP [//] SI G") as "F". iMod "close" as "_".
      iMod "F" as "%". done. }
    iAssert (|==> [∗ map] g↦v ∈ G, gl_fuel g 0ₗ%L (ms_nondet (Ψ:=Ψ) μ))%I with "[Fs]" as ">Fs".
    { rewrite -big_sepM_bupd. iApply (big_sepM_impl with "Fs"). iIntros "!> %%% H".
      iSpecialize ("H" $! (ms_nondet (Ψ:=Ψ) μ)). iDestruct "H" as "(%&%& %LE& H)".
      iApply (gl_fuel_mon with "H"). auto. }
    iStopProof. revert e Hnv Term G R.
    induction μ as [μ IH] using (well_founded_ind (ord_tree_lt_tc_well_founded _)).
    iIntros "%e %Hnv %Term %G %R (TWP& TG& #Rs& Fs)".
    rewrite lwp_unfold /lwp_pre twp_unfold /twp_pre. rewrite Hnv.
    iIntros "%Θ %σ1 %κ %κs SI". iMod ("TWP" with "SI") as "TWP".
    iModIntro. iMod "TWP" as "(%Red& TWP)".
    iModIntro. iSplitR; first done. iIntros "%%% %Step".
    iApply gtp_gprog. iMod ("TWP" with "[//]") as "TWP".
    inv Term. rename H into LTμ, H0 into Term.
    iApply fupd_gprog.
    iAssert (|==> ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L (ms_nondet μ')) ∗ ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L 1))%I
      with "[Fs]" as ">[Fs Fs0]".
    { rewrite !big_sepM_dom. iApply (gl_fuel_lt_set with "Fs"). apply measure_nondet_lt. auto. }
    iModIntro.
    iApply (gprog_step _ _ ∅).
    1,2: set_solver.
    iModIntro. iExists G. iFrame "TG Fs0". iExists R. iSplitR; first eauto.
    iIntros "(TG& Ws& _) !> !>". iMod "TWP". iModIntro. iMod "TWP" as "($& TWP& $)".
    iModIntro.
    assert (flip (ΨR i) e2 e).
    { simpl. unfold ΨR. intros.
      exists κ. split; first auto. exists efs. split; auto. }
  Local Definition ΨR i : Ψ → Ψ → Prop :=
    λ e1 e2,
      ∀ σ1 Θ1 κs1, ∃ σ2 Θ2 κs2 κ, κs1 = κ ++ κs2 ∧ ∃ efs, Θ2 = Θ1 ∪ (dom efs) ∧ prim_step i e1 σ1 Θ1 κ e2 σ2 efs.
    apply H in H0. clear H. destruct H0 as (μ'& LTμ& Term).
    assert (

    rewrite lwp_unfold /lwp_pre.
    destruct (to_val e2) eqn:Hnv2.
    - rewrite twp_unfold /twp_pre Hnv2. iMod "TWP". iApply ("TWP" with "TG Ws").
    - assert (TCEq (to_val e2) None).
      { rewrite Hnv2. done. }
      clear Hnv2. rename H into Hnv2.
    

    
    inv Term. rename H into LTμ, H0 into Term.
    (* assert (flip (ΨR i) (e2, σ2, (Θ ∪ dom efs), κs) (e, σ1, Θ, κ ++ κs)). *)
    (* { exists κ. split; first auto. exists efs. split; auto. } *)
    (* apply H in H0. clear H. destruct H0 as (μ'& LTμ& Term). *)
    iApply fupd_gprog.
    iAssert (|==> ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L (ms_nondet μ')) ∗ ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L 1))%I
      with "[Fs]" as ">[Fs Fs0]".
    { rewrite !big_sepM_dom. iApply (gl_fuel_lt_set with "Fs"). apply measure_nondet_lt. auto. }
    iModIntro.
    iApply gtp_gprog. iMod ("TWP" with "[//]") as "TWP".
    iApply (gprog_step _ _ ∅).
    1,2: set_solver.
    iModIntro. iExists G. iFrame "TG Fs0". iExists R. iSplitR; first eauto.
    iIntros "(TG& Ws& _) !> !>". iMod "TWP". iModIntro. iMod "TWP" as "($& TWP& $)".
    iModIntro. rewrite lwp_unfold /lwp_pre.
    destruct (to_val e2) eqn:Hnv2.
    - rewrite twp_unfold /twp_pre Hnv2. iMod "TWP". iApply ("TWP" with "TG Ws").
    - assert (TCEq (to_val e2) None).
      { rewrite Hnv2. done. }
      clear Hnv2. rename H into Hnv2.

      TODO

      TODO

      clear dependent e σ1 Θ κ κs σ2 efs.
      iIntros "%Θ %σ1 %κ %κs SI". iApply fupd_mask_intro. 1: set_solver.
      
      
      
gprog_step:
  ∀ {SI : indexT} {Λ : language} {Σ : gFunctors} {lirisGS0 : lirisGS Λ Σ} (Θ π : gset positive) (i : positive) (P : iPropI Σ),
    Θ ## π
    → (|={∅}=>
         ∃ G : gmap gl_id ghost_lock_version, th_obls i G 1 ∗ ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L 1) ∗
           ∃ R : gmap gl_id ghost_lock_version, ([∗ map] r↦v ∈ R, gl r v) ∗
             (th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit r v Ord.one ∨ gl_done r v) ∗ ([∗ set] j ∈ π, th_obls j ∅ 1) ={∅}=∗ P))
      ⊢ @={Θ,Θ ∪ π,i}=↓ P

twp_step =
λ (SI : indexT) (Λ : language) (Σ : gFunctors) (lirisGS0 : lirisGS Λ Σ) 
  s i (E : coPset) (e1 : expr Λ) (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ),
  (∀ (Θ : thread_ids) (σ1 : state Λ) (κ κs : list (observation Λ)),
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     |=[Θ]=>g ⌜match s with
               | NotStuck => reducible i e1 σ1 Θ
               | MaybeStuck => True
               end⌝ ∗
     ∀ (e2 : expr Λ) (σ2 : state Λ) (efs : thread_pool Λ),
       ⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝ -∗
       @={Θ,Θ ∪ dom efs}=> |=[Θ ∪ dom efs]=>g |={∅,E}=>
                                                state_interp σ2 
                                                 (Θ ∪ dom efs) κs ∗
                                                ν e2 efs)%I
  (* Lemma twp_lwp s i E e Φ G R : *)
  (*   TCEq (to_val e) None → *)
  (*   (tWP e @ s; i; E {{ λ v, th_obls i G 1 -∗ ([∗ map] r↦u ∈ R, wit r u Ord.one ∨ gl_done r u) -∗ Φ v }}) *)
  (*   ⊢ th_obls i G 1 -∗ *)
  (*   ([∗ map] g↦v ∈ G, ∀ μ0, ∃ ℓ μ, ⌜ (measure 0ₗ%L μ0 <= measure ℓ μ)%ord ⌝ ∗ gl_fuel g ℓ μ) -∗ *)
  (*   ([∗ map] r↦v ∈ R, gl r v) -∗ *)
  (*   lWP e @ s; i; E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hnv) "TWP TG Fs Rs". *)
  (*   rewrite lwp_unfold /lwp_pre Hnv. *)
  (*   iIntros "%Θ %σ1 %κ %κs SI". iApply fupd_mask_intro. 1: set_solver. *)
  (*   iIntros "close". iApply gupd_unfold. iRight. iIntros "%Ω1 %W1 G". *)
  (*   destruct (ΨR_classical i (e, σ1, Θ, (κ ++ κs))) as [Loop | [μ Term]]. *)
  (*   { iPoseProof (twp_ex_loop_false with "TWP [//] SI G") as "F". iMod "close" as "_". *)
  (*     iMod "F" as "%". done. } *)
  (*   iAssert (|==> [∗ map] g↦v ∈ G, gl_fuel g 0ₗ%L (ms_nondet (Ψ:=Ψ) μ))%I with "[Fs]" as ">Fs". *)
  (*   { rewrite -big_sepM_bupd. iApply (big_sepM_impl with "Fs"). iIntros "!> %%% H". *)
  (*     iSpecialize ("H" $! (ms_nondet (Ψ:=Ψ) μ)). iDestruct "H" as "(%&%& %LE& H)". *)
  (*     iApply (gl_fuel_mon with "H"). auto. } *)
  (*   iModIntro. iExists Ω1. iSplitR; first done. *)
  (*   iIntros (? (Prog& OW2)). *)
  (*   iModIntro. rewrite /gproto. iDestruct "G" as "($& $& $& N& %OW1)". *)
  (*   pose proof (glwit_inv_rc_step_same_gls _ _ _ OW1 Prog OW2). *)
  (*   iPoseProof (glwit_mon _ _ H with "N") as "$". *)
  (*   iSplitR; first done. *)
  (*   iMod "close" as "_". clear dependent Ω1 W1 W2. *)
  (*   iStopProof. revert e σ1 Θ κ κs Hnv Term G R. *)
  (*   induction μ as [μ IH] using (well_founded_ind (ord_tree_lt_tc_well_founded _)). *)
  (*   iIntros "%e %σ1 %Θ %κ %κs %Hnv %Term %G %R (TWP& TG& #Rs& SI& Fs)". *)
  (*   rewrite twp_unfold /twp_pre Hnv. iMod ("TWP" with "SI") as "TWP". *)
  (*   iModIntro. iMod "TWP" as "($& TWP)". iIntros "!> %%% %Step". *)
  (*   inv Term. rename H into LTμ, H0 into Term. *)
  (*   (* assert (flip (ΨR i) (e2, σ2, (Θ ∪ dom efs), κs) (e, σ1, Θ, κ ++ κs)). *) *)
  (*   (* { exists κ. split; first auto. exists efs. split; auto. } *) *)
  (*   (* apply H in H0. clear H. destruct H0 as (μ'& LTμ& Term). *) *)
  (*   iApply fupd_gprog. *)
  (*   iAssert (|==> ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L (ms_nondet μ')) ∗ ([∗ map] g↦_ ∈ G, gl_fuel g 0ₗ%L 1))%I *)
  (*     with "[Fs]" as ">[Fs Fs0]". *)
  (*   { rewrite !big_sepM_dom. iApply (gl_fuel_lt_set with "Fs"). apply measure_nondet_lt. auto. } *)
  (*   iModIntro. *)
  (*   iApply gtp_gprog. iMod ("TWP" with "[//]") as "TWP". *)
  (*   iApply (gprog_step _ _ ∅). *)
  (*   1,2: set_solver. *)
  (*   iModIntro. iExists G. iFrame "TG Fs0". iExists R. iSplitR; first eauto. *)
  (*   iIntros "(TG& Ws& _) !> !>". iMod "TWP". iModIntro. iMod "TWP" as "($& TWP& $)". *)
  (*   iModIntro. rewrite lwp_unfold /lwp_pre. *)
  (*   destruct (to_val e2) eqn:Hnv2. *)
  (*   - rewrite twp_unfold /twp_pre Hnv2. iMod "TWP". iApply ("TWP" with "TG Ws"). *)
  (*   - assert (TCEq (to_val e2) None). *)
  (*     { rewrite Hnv2. done. } *)
  (*     clear Hnv2. rename H into Hnv2. *)

End adequacy.
