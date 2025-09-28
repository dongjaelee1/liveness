From iris.proofmode Require Import base proofmode classes.
(* From transfinite.base_logic.lib Require Export fancy_updates. *)
From liris Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From liris.base_logic Require Export otree fancy_updates.
(* From liris.program_logic Require Export thread_obligation. *)
From liris.algebra Require Import ordinal_wfocm.
Import uPred.

Class lirisGS `{SI : indexT} (Λ : language) (Σ : gFunctors) := LirisG {
  (** Invariants. *)
  #[global] liris_invGS :: invGS Σ;
  (** Liveness obligation interpretation. *)
  #[global] liris_osatGS :: osatGS.osatGS (WF:=ord_wfocm_pack) (state Λ) thread_id Σ;
  (** Liveness obligations assigned to threads. *)
  #[global] liris_othreadGS :: othreadGS.othreadGS Σ;
  (** Forest of liveness obligation. *)
  #[global] liris_otreeGS :: otreeGS.otreeGS Ord.t Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction.
  Here [state] is the global state, [thread_ids] is the allocated thread ids,
  and [list (observation Λ)] are the remaining observations. *)
  state_interp : state Λ → thread_ids → list (observation Λ) → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : thread_id → val Λ → iProp Σ;
}.
Global Opaque liris_invGS liris_osatGS liris_othreadGS liris_otreeGS.
Global Arguments LirisG {SI Λ Σ}.

Global Instance wp_obl_class {Λ : language} : obl_class Ord.t (state Λ) thread_id Ord.lt.
Proof. econstructor; try apply _. apply Ord.lt_well_founded. Qed.

(* Notation lirisGS := (lirisGS_gen HasLc). *)
(* Notation "'⌈' Λ '⌉'" := (Ord.from_wf_set (@WFOCM.lt_wf _ _ _ _ (@fuel_wf Λ))). *)
(* Notation schedfairIL Λ := (schedfairI (H:=@fuel_wf Λ)). *)
(* Notation toIL Λ := (toI (WF:=@fuel_wf Λ) (ps:=state Λ)). *)
(* Notation oftIL Λ := (oftI (WF:=@fuel_wf Λ) (obl_ps:=state Λ)). *)
(* Notation obl_statesL Λ := (obl_states' (@wp_obl_class Λ)). *)

(** Predicates we take the fixpoint of in order to define the lWP. *)
(* Ω must make strict progress *)
Definition lwp_step `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ (Ω1 : obl_states) (Θ : thread_ids) σ1 κ κs,
     (osat Ω1 ∗ othread Θ ∗ osuspend (dom Ω1) ∗ oforest (dom Ω1) ∗ state_interp σ1 Θ (κ ++ κs)) ={E,∅}=∗
     (⌜if s is NotStuck then reducible e1 σ1 Θ else True⌝) ∗
     ∃ (b : bool), ALC? b |={∅}=>
     ∃ Ω1', (⌜ Ω1 ↪ₛ⋆ Ω1' @ σ1 ⌝) ∗
            ∀ e2 σ2 efs, (⌜ prim_step e1 σ1 Θ κ e2 σ2 efs ⌝) -∗ |={∅,E}=>
     ∃ Ω2 Ω2', (⌜ (if b then (Ω1' ↪ₚ Ω2 | (obl_cond_owner i)) else Ω1' = Ω2) ∧ (Ω2 ↪ₛ⋆ Ω2' @ σ2) ⌝) ∗
               (osat Ω2' ∗ othread (Θ ∪ dom efs) ∗ osuspend (dom Ω2') ∗ oforest (dom Ω2') ∗
                state_interp σ2 (Θ ∪ dom efs) κs) ∗
               ν e2 efs)%I.

Section lwp_step.

  Global Instance lwp_step_ne `{SI : indexT} `{!lirisGS Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step.
    do 15 (f_equiv || done). destruct a4.
    - apply ALC_ne. do 19 (f_equiv || done).
    - do 20 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper `{SI : indexT} `{!lirisGS Λ Σ} s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono `{SI : indexT} `{!lirisGS Λ Σ} s
    (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (?????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "($& %& Hwp)".
    iModIntro. iExists b. iMod "Hwp" as ">(%& $& Hwp)".
    iModIntro. iIntros (???) "H0". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%&%&H0&H1&H2)".
    iModIntro. iFrame. by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step `{SI : indexT} `{!lirisGS Λ Σ} s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

End lwp_step.

(** Modality for updating obligation state. *)
(* Can allocate, transfer, progress, or fulfills obligations. Note this has no later modality. *)
Definition ghost_step `{SI : indexT} `{!lirisGS Λ Σ} (E : coPset)
  (ν : iPropO Σ) : iPropO Σ :=
  (∀ (Ω : obl_states) (Θ : thread_ids) σ κs,
     (osat Ω ∗ othread Θ ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗ state_interp σ Θ κs) ={E}=∗
     ∃ Ω', (⌜(Ω ↪ₛ⋆ Ω' @ σ)⌝) ∗
           (osat Ω' ∗ othread Θ ∗ osuspend (dom Ω') ∗ oforest (dom Ω') ∗ state_interp σ Θ κs) ∗
           ν)%I.

Section ghost_step.

  Global Instance ghost_step_ne `{SI : indexT} `{!lirisGS Λ Σ} E :
    NonExpansive (ghost_step E).
  Proof.
    intros n Φ Ψ HΦ. rewrite /ghost_step. do 15 (f_equiv || done).
  Qed.
  Global Instance ghost_step_proper `{SI : indexT} `{!lirisGS Λ Σ} E :
    Proper ((≡) ==> (≡)) (ghost_step E).
  Proof.
    intros Φ Φ' ?. apply equiv_dist=>n. apply ghost_step_ne. by apply equiv_dist.
  Qed.

  Lemma ghost_step_mono_fupd `{SI : indexT} `{!lirisGS Λ Σ} E (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ |={E}=> ν2) -∗
       ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros "Hwp". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%&H0&H1&Hwp)". iFrame. by iApply "Hmono".
  Qed.

  Lemma ghost_step_mono `{SI : indexT} `{!lirisGS Λ Σ} (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ ν2) -∗
       ∀ E, ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros (E) "Hwp". iApply (ghost_step_mono_fupd with "[Hmono] Hwp").
    iIntros "H". iModIntro. by iApply "Hmono".
  Qed.

  Lemma fupd_ghost_step `{SI : indexT} `{!lirisGS Λ Σ} E lwp :
    (|={E}=> ghost_step E lwp) ⊢ ghost_step E lwp.
  Proof.
    iIntros "Hf". rewrite /ghost_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

  Lemma ghost_step_intro `{SI : indexT} `{!lirisGS Λ Σ} E Ψ :
    Ψ ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hlwp". rewrite /ghost_step.
    iIntros "%%%% H". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_strong_mono `{SI : indexT} `{!lirisGS Λ Σ} E1 E2 Ψ1 Ψ2 :
    E1 ⊆ E2 →
    ghost_step E1 Ψ1 -∗ (Ψ1 ={E2}=∗ Ψ2) -∗ ghost_step E2 Ψ2.
  Proof.
    iIntros (HE) "IH Hu". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_subseteq E1) as "close"; first done.
    iMod "IH" as "(%&H0&H1&IH)". iFrame. iMod "close" as "_".
    by iApply "Hu".
  Qed.

  Lemma ghost_step_atomic `{SI : indexT} `{!lirisGS Λ Σ} E1 E2 Ψ :
    (|={E1,E2}=> ghost_step E2 (|={E2,E1}=> Ψ)) ⊢ ghost_step E1 Ψ.
  Proof.
    iIntros "IH". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("IH" with "[$]").
    iMod "IH". iMod "IH". iDestruct "IH" as "(%&%&H&Hwp)".
    iMod "Hwp". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_idemp `{SI : indexT} `{!lirisGS Λ Σ} E Ψ :
    ghost_step E (ghost_step E Ψ) ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hg". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("Hg" with "[$]"). iMod "Hg".
    iDestruct "Hg" as "(%&%&H&Hg)". iSpecialize ("Hg" with "[-]"); first by iFrame.
    iDestruct "Hg" as ">(%&%&H&Hg)". iModIntro. iFrame.
    iPureIntro. by etransitivity.
  Qed.

End ghost_step.

Definition lift_term `{SI : indexT} `{!lirisGS Λ Σ} (i :thread_id) (Φ : thread_id → val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (othreadG_term i ∗ Φ i v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Liris, postcondition of a thread i must include othreadG_term i. *)
Definition lwp_pre `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => ghost_step E (Φ v)
     | None => lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef (lift_term j fork_post))
     end)%I.

Lemma lwp_pre_mono `{SI : indexT} `{!lirisGS Λ Σ} s
  (lwp1 lwp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, lwp1 i E e Φ -∗ lwp2 i E e Φ) →
     ∀ i E e Φ, lwp_pre s lwp1 i E e Φ -∗ lwp_pre s lwp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Hlwp". rewrite /lwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (lwp_step_mono with "[] Hlwp"). iModIntro.
  iIntros (e efs) "[Hlwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  iApply (@big_sepM_impl with "Hefs"); iIntros "!#" (k e' _) "Hlwp". by iApply "Hmono".
Qed.

(* Uncurry [lwp_pre] and equip its type with an OFE structure *)
Definition lwp_pre' `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : indexT} `{!lirisGS Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step.
    do 16 (f_equiv || done). destruct a4.
    + apply ALC_ne. do 20 (f_equiv || done). by apply pair_ne.
    + do 21 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition *)
Local Definition lwp_def `{SI : indexT} `{!lirisGS Λ Σ} : lWp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, (bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ).
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI Λ Σ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : indexT} `{!lirisGS Λ Σ} : lwp = @lwp_def SI Λ Σ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.


Section lwp.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma lwp_pre_lwp_pre' s _lwp i E e Φ :
  lwp_pre s _lwp i E e Φ = lwp_pre' s (λ '(i,E,e,Φ), _lwp i E e Φ) (i,E,e,Φ).
Proof. rewrite /lwp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.
Lemma lwp_unfold s i E e Φ :
  lWP e @ s; i; E {{ Φ }} ⊣⊢ lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ.
Proof. rewrite lwp_unseal. rewrite lwp_pre_lwp_pre' /lwp_def. rewrite (least_fixpoint_unfold (lwp_pre' s)). done. Qed.

Lemma lwp_ind_strong s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ ∧ lWP e @ s; i; E {{ Φ }}) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (i e E Φ) "H". rewrite lwp_unseal.
  set (Ψ' := uncurry4 Ψ :
         prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[[i1 E1] e1] Φ1] [[[i2 E2] e2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. }
  iApply (least_fixpoint_ind _ Ψ' with "[] H").
  iIntros "!#" ([[[??] ?] ?]) "H". by iApply "IH".
Qed.

Lemma lwp_ind s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply lwp_ind_strong. iIntros "!>" (i e E Φ) "Hrwp".
  iApply "H". iApply (lwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (i E e Φ) "[$ _]".
Qed.

Global Instance lwp_ne s i E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !lwp_unseal. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance lwp_proper s i E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_ne=>v; apply equiv_dist.
Qed.

Lemma ghost_step_elim s i E e Φ :
  ghost_step E (lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "Hg". rewrite !lwp_unfold /lwp_pre /lwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { by iApply ghost_step_idemp. }
  iIntros (?????) "H".
  rewrite /ghost_step. iSpecialize ("Hg" with "[$]"). iMod "Hg".
  iDestruct "Hg" as "(%&%&H&Hg)". iSpecialize ("Hg" with "[-]"); first by iFrame.
  iMod "Hg". iModIntro. iDestruct "Hg" as "($& %& Hg)". iExists b. iMod "Hg" as ">(%&%& Hg)".
  iModIntro. iExists Ω1'. iSplitR.
  { iPureIntro. etransitivity; eauto. }
  iFrame.
Qed.

Lemma lwp_value_fupd' s i E Φ v : lWP of_val v @ s; i; E {{ Φ }} ⊣⊢ ghost_step E (Φ v).
Proof.
  iSplit; iIntros "H".
  - by rewrite lwp_unfold /lwp_pre to_of_val.
  - by rewrite lwp_unfold /lwp_pre to_of_val.
Qed.

Lemma lwp_stuckness_mono s1 s2 i E e Φ :
  s1 ⊑ s2 →
  lWP e @ s1; i; E {{ Φ }} -∗ lWP e @ s2; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iRevert (i e E Φ) "H".
  iApply lwp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
  rewrite !lwp_unfold /lwp_pre /=. destruct (to_val e) as [v|] eqn:?; first done.
  iIntros (?????) "H". iSpecialize ("IH" with "[$]").
  iMod "IH" as "(%& %& IH)". iModIntro.
  iSplit; [by destruct s1, s2|clear H0].
  iExists b. iMod "IH" as ">(%&%&IH)".
  iModIntro. iExists _. iSplitR; first done.
  iIntros (????). iMod ("IH" with "[//]") as "IH".
  iIntros "!>". iDestruct "IH" as "(%&%&%&H0&[H1 _]&Hefs)".
  iFrame. iExists _. iSplitR; first done.
  iApply (big_sepM_impl with "Hefs"). iIntros "!>" (k ef _). iIntros "[H _]". done.
Qed.

Lemma lwp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  lWP e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ lWP e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
  iApply lwp_ind_strong; [solve_proper|]. iModIntro. iIntros (i e E1 Φ) "IH % %HE HΦ".
  rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply (ghost_step_strong_mono with "IH"); done. }
  iIntros (?????) "H". iSpecialize ("IH" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "IH" as "(%& %& IH)". iModIntro.
  iSplit; [by destruct s1, s2|clear H0].
  iExists b. iMod "IH" as ">(%&%&IH)".
  iModIntro. iExists _. iSplitR; first done.
  iIntros (????). iMod ("IH" with "[//]") as "IH".
  iMod "Hclose" as "_". iModIntro. iDestruct "IH" as "(%&%&%&H0&[H1 _]&Hefs)".
  iFrame. iExists _. iSplit; first done. iSplitR "Hefs".
  + by iApply "H1".
  + iApply (big_sepM_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
Qed.

Lemma fupd_lwp s i E e Φ : (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  rewrite /lwp_step. iIntros (?????) "Hp". iMod "H".
  iSpecialize ("H" with "[$]"). done.
Qed.
Lemma lwp_fupd s i E e Φ : lWP e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
Proof. iIntros "H". iApply (lwp_strong_mono s s i E with "H"); auto. Qed.

Lemma lwp_atomic s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !lwp_unfold /lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iApply ghost_step_atomic. }
  rewrite /lwp_step.
  iIntros (?????) "Hp".
  iMod ("H" with "[$]") as ">(%& %& H)".
  iModIntro. iSplitR; first done.
  iExists b. iMod "H" as ">(%&%&H)". iModIntro. iExists _. iSplitR; first done.
  iIntros (????). iSpecialize ("H" with "[//]").
  iMod "H" as "(%&%&%&H0&H&Hefs)".
  destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iSpecialize ("H" with "[H0]"); first by iFrame.
      iMod "H". iDestruct "H" as "(%&%&H0&H)". iMod "H". iFrame.
      iModIntro. iExists Ω2. iSplit.
      * iPureIntro. destruct b, H2; split; auto; by etransitivity.
      * rewrite lwp_unfold /lwp_pre. rewrite He2. by iApply ghost_step_intro.
    + iMod ("H" $! _ _ _ [] _ with "H0") as "[H H']".
      iDestruct "H" as %(? & ? & ? & ? & ?). by edestruct (atomic _ _ _ _ _ _ H1).
  - destruct (atomic _ _ _ _ _ _ H1) as [v <-%of_to_val].
    rewrite lwp_value_fupd'. iMod ("H" with "[H0]") as "H"; first by iFrame.
    iDestruct "H" as "(%&%&H0&>H)". iModIntro. iFrame.
    iExists Ω2. iSplit.
    { iPureIntro. destruct b, H2; split; auto; by etransitivity. }
    iApply lwp_value_fupd'. by iApply ghost_step_intro.
Qed.

Lemma lwp_step_fupd s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1,E2}=> |={E2,E1}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (? ?) "[HP Hwp]". iApply (lwp_strong_mono with "Hwp"); [done..|].
  iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
Qed.

Lemma lwp_bind K `{!LanguageCtx K} s i E e Φ :
  lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }} ⊢ lWP K e @ s; i; E {{ Φ }}.
Proof.
  revert Φ.
  cut (∀ Φ', lWP e @ s; i; E {{ Φ' }} -∗ ∀ Φ, (∀ v, Φ' v -∗ lWP K (of_val v) @ s; i; E {{ Φ }}) -∗ lWP K e @ s; i; E {{ Φ }}).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (i e E Φ') "H". iApply lwp_ind_strong; first solve_proper.
  iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /lwp_pre /lwp_step.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply ghost_step_elim. iApply (ghost_step_mono with "HΦ IH"). }
  (* rewrite lwp_unfold /lwp_pre /lwp_step fill_not_val //. *)
  rewrite lwp_unfold /lwp_pre /lwp_step fill_not_val; last auto.
  iIntros (?????) "H". iMod ("IH" with "H") as "(%& %& IH)". iModIntro. iSplit.
  { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
  iExists b. iMod "IH" as ">(%& %& IH)".
  iModIntro. iExists _. iSplitR; first done.
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 Θ κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("IH" $! e2' σ2 efs with "[//]") as "(%& %& %& $& IH& IHfork)".
  iIntros "!>". iExists Ω2. iSplitR; first done. iSplitL "IH HΦ".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

Lemma lwp_bind_inv K `{!LanguageCtx K} s i E e Φ :
  lWP K e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}.
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (i e' E Φ) "H". iApply lwp_ind_strong; first solve_proper.
  iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->).
  rewrite !lwp_unfold {2}/lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply ghost_step_intro. rewrite !lwp_unfold.
    iApply (lwp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]". }
  rewrite /lwp_pre fill_not_val; [|done].
  iIntros (?????) "Hσ". iMod ("IH" with "[$]") as "(%& %& IH)".
  iModIntro. iSplitR.
  { destruct s; eauto using reducible_fill_inv. }
  iExists b. iMod "IH" as ">(%& %& IH)"; iModIntro. iExists _. iSplit; first done.
  iIntros (e2 σ2 efs Hstep).
  iMod ("IH" $! (K e2) σ2 efs with "[]") as "(%&%&%& Hσ & IH & IHefs)"; first eauto using fill_step.
  iModIntro. iExists _, _. iSplitR; first done. iFrame "Hσ". iSplitR "IHefs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

(** * Derived rules *)
Lemma lwp_mono s i E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (lwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma lwp_stuck_mono s1 s2 i E e Φ :
  s1 ⊑ s2 → lWP e @ s1; i; E {{ Φ }} ⊢ lWP e @ s2; i; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (lwp_strong_mono with "H"); auto. Qed.
Lemma lwp_stuck_weaken s i E e Φ :
  lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ i; E ?{{ Φ }}.
Proof. apply lwp_stuck_mono. by destruct s. Qed.
Lemma lwp_mask_mono s i E1 E2 e Φ : E1 ⊆ E2 → lWP e @ s; i; E1 {{ Φ }} ⊢ lWP e @ s; i; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (lwp_strong_mono with "H"); auto. Qed.
Global Instance lwp_mono' s i E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (lwp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.
Global Instance lwp_flip_mono' s i E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (lwp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.

Lemma lwp_value_fupd s i E Φ e v : IntoVal e v → lWP e @ s; i; E {{ Φ }} ⊣⊢ ghost_step E (Φ v).
Proof. intros <-. by apply lwp_value_fupd'. Qed.
Lemma lwp_value' s i E Φ v : Φ v ⊢ lWP (of_val v) @ s; i; E {{ Φ }}.
Proof. rewrite lwp_value_fupd'. apply ghost_step_intro. Qed.
Lemma lwp_value s i E Φ e v : IntoVal e v → Φ v ⊢ lWP e @ s; i; E {{ Φ }}.
Proof. intros <-. apply lwp_value'. Qed.

Lemma lwp_frame_l s i E e Φ R : R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma lwp_frame_r s i E e Φ R : lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the lWP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma lwp_step_fupd_2 s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1∖E2,∅}=> |={∅,E1∖E2}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (lwp_step_fupd with "[H]"); [done|].
  iApply (sep_mono_l with "H"). iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply fupd_mask_frame; [|iMod "HP"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.

Lemma lwp_frame_step_l s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1,E2}=> |={E2,E1}=> R) ∗ lWP e @ s; i; E2 {{ Φ }} ⊢ lWP e @ s; i; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply lwp_step_fupd; first done.
  iFrame "Hu". iApply (lwp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma lwp_frame_step_r s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  lWP e @ s; i; E2 {{ Φ }} ∗ (|={E1,E2}=> |={E2,E1}=> R) ⊢ lWP e @ s; i; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(lWP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply lwp_frame_step_l.
Qed.
Lemma lwp_frame_step_l' s i E e Φ R :
  TCEq (to_val e) None → R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s i E E); try iFrame; eauto. Qed.
Lemma lwp_frame_step_r' s i E e Φ R :
  TCEq (to_val e) None → lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_r s i E E); try iFrame; eauto. Qed.

Lemma lwp_wand s i E e Φ Ψ :
  lWP e @ s; i; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ lWP e @ s; i; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (lwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma lwp_wand_l s i E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_wand_r s i E e Φ Ψ :
  lWP e @ s; i; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_frame_wand s i E e Φ R :
  R -∗ lWP e @ s; i; E {{ v, R -∗ Φ v }} -∗ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (lwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_lwp p s i E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite lwp_frame_l. apply lwp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_lwp s i E e Φ : IsExcept0 (lWP e @ s; i; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_lwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_lwp p s i E e P Φ :
    ElimModal True p false (|==> P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  Global Instance elim_modal_fupd_lwp p s i E e P Φ :
    ElimModal True p false (|={E}=> P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_lwp.
  Qed.
  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_lwp_wrong_mask p s i E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_lwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (lWP e @ s; i; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_lwp_atomic p s i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (lWP e @ s; i; E1 {{ Φ }}) (lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r lwp_atomic.
  Qed.
  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_lwp_atomic_wrong_mask p s i E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (lWP e @ s; i; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance elim_modal_ghost_step_lwp p s i E e P Φ :
    ElimModal True p false (ghost_step E P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim. iIntros (?) "[H1 H2]".
    iApply ghost_step_elim. iApply (ghost_step_mono with "H2 H1").
  Qed.

  Global Instance add_modal_fupd_lwp s i E e P Φ :
    AddModal (|={E}=> P) P (lWP e @ s; i; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_lwp. Qed.

  Global Instance add_modal_ghost_step_lwp s i E e P Φ :
    AddModal (ghost_step E P) P (lWP e @ s; i; E {{ Φ }}).
  Proof. rewrite /AddModal. iIntros "[H1 H2]". iMod "H1". by iApply "H2". Qed.

  Global Instance elim_acc_lwp_atomic {X} i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (lWP e @ s; i; E1 {{ Φ }})
            (λ x, lWP e @ s; i; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_lwp_nonatomic {X} i E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (lWP e @ s; i; E {{ Φ }})
            (λ x, lWP e @ s; i; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_fupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
