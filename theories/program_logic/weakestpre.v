From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From liris Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.
From liris.program_logic Require Export thread_obligation.
From liris.algebra Require Import ordinal_wfocm.

Class lirisGS_gen `{SI : indexT} (hlc : has_lc) (Λ : language) (Σ : gFunctors) := LirisG {
  (** Invariants. *)
  #[global] liris_invGS :: invGS_gen hlc Σ;
  (** Liveness obligation interpretation. *)
  #[global] liris_osatGS :: osatGS.osatGS (WF:=ord_wfocm_pack) (state Λ) Σ;
  (** Scheduler fairness interpretation. *)
  #[global] liris_schedfairGS :: schedfairGS.schedfairGS (WF:=@fuel_wf Λ) Σ;
  (** Connecting liveness obligations and scheduler fairness. *)
  #[global] liris_threadoblGS :: threadoblGS.threadoblGS Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last thread_ids is the set of allocated thread identifiers. *)
  state_interp : state Λ → nat → list (observation Λ) → thread_ids → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

  (** The number of additional logical steps (i.e., later modality in the
  definition of lWP) and later credits per physical step is
  [S (num_laters_per_step ns)], where [ns] is the number of physical steps
  executed so far. We add one to [num_laters_per_step] to ensure that there
  is always at least one later and later credit for each physical step. *)
  num_laters_per_step : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs τ:
    state_interp σ ns κs τ ⊢ |={∅}=> state_interp σ (S ns) κs τ
}.
Global Opaque liris_invGS liris_osatGS liris_schedfairGS liris_threadoblGS.
Global Arguments LirisG {SI hlc Λ Σ}.

Global Instance wp_obl_class {Λ : language} : obl_class (state Λ) (prod Ord.t (fuel Λ)) :=
  osat_obl_class_def ord_wfocm_pack (WFOCM.lt_wf (t:=@fuel_wf Λ)) (state Λ).

Notation lirisGS := (lirisGS_gen HasLc).
Notation "'⌈' Λ '⌉'" := (Ord.from_wf_set (@WFOCM.lt_wf _ _ _ _ (@fuel_wf Λ))).
Notation schedfairIL Λ := (schedfairI (H:=@fuel_wf Λ)).
Notation toIL Λ := (toI (WF:=@fuel_wf Λ) (ps:=state Λ)).
Notation oftIL Λ := (oftI (WF:=@fuel_wf Λ) (obl_ps:=state Λ)).
Notation obl_statesL Λ := (obl_states' (@wp_obl_class Λ)).

(** The predicate we take the fixpoint of in order to define the lWP. *)
(** In the step case, we both provide [S (num_laters_per_step ns)]
  later credits, as well as an iterated update modality that allows
  stripping as many laters, where [ns] is the number of steps already taken.
  We have both as each of these provides distinct advantages:
  - Later credits do not have to be used right away, but can be kept to
    eliminate laters at a later point.
  - The step-taking update composes well in parallel: we can independently
    compose two clients who want to eliminate their laters for the same
    physical step, which is not possible with later credits, as they
    can only be used by exactly one client.
  - The step-taking update can even be used by clients that opt out of
    later credits, e.g. because they use [BiFUpdPlainly]. *)

(* Ω must make strict progress *)
Definition lwp_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (⌜ τ = dom δ1 ⌝ ∗ schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     (⌜if s is NotStuck then reducible e1 σ1 τ else True⌝) ∗
     ∃ Ω2, (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗
           ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                        ∀ δ2 δ3, (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
                                 £ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
              ∃ γ2, (schedfairIL Λ δ3 ∗ osat Ω4 ∗ toIL Λ γ2 ∗ oftIL Λ Ω4 δ3 γ2 ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    ν e2 efs
  )%I.

Section lwp_step.

  Global Instance lwp_step_ne `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step.
    do 35 (f_equiv || done). simpl. do 3 f_equiv.
    induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
    do 10 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s
    (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (????????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(H0&%&H1&Hwp)". iModIntro.
    iSplitL "H0"; first done. iExists _. iSplitL "H1"; first done.
    iIntros (???) "H". iSpecialize ("Hwp" with "[$]").
    iIntros (??) "H0 H". iSpecialize ("Hwp" with "[$]").
    iSpecialize ("Hwp" with "H"). iApply (step_fupdN_wand with "Hwp").
    iIntros ">Hwp". iModIntro.
    iDestruct "Hwp" as "(%&%&H0&%&H&Hwp)". iFrame. by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

End lwp_step.

(** Modality for updating obligation state. *)
(* Ω can allocate, progress, or fulfills obligations. Note this has no later modality. *)
Definition ghost_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (E : coPset)
  (ν : iPropO Σ) : iPropO Σ :=
  (∀ δ (Ω : obl_statesL Λ) γ σ ns κs τ,
     (⌜ τ = dom δ ⌝ ∗ schedfairIL Λ δ ∗ osat Ω ∗ toIL Λ γ ∗ oftIL Λ Ω δ γ ∗ state_interp σ ns κs τ) ={E}=∗
     ∃ Ω', (⌜(Ω ↪ₛ⋆ Ω' @ σ)⌝) ∗
           ∃ γ', (schedfairIL Λ δ ∗ osat Ω' ∗ toIL Λ γ' ∗ oftIL Λ Ω' δ γ' ∗ state_interp σ ns κs τ) ∗
                 ν
  )%I.

Section ghost_step.

  Global Instance ghost_step_ne `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E :
    NonExpansive (ghost_step E).
  Proof.
    intros n Φ Ψ HΦ. rewrite /ghost_step. do 23 (f_equiv || done).
  Qed.
  Global Instance ghost_step_proper `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E :
    Proper ((≡) ==> (≡)) (ghost_step E).
  Proof.
    intros Φ Φ' ?. apply equiv_dist=>n. apply ghost_step_ne. by apply equiv_dist.
  Qed.

  Lemma ghost_step_mono_fupd `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}
    E (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ |={E}=> ν2) -∗
       ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros "Hwp". rewrite /ghost_step.
    iIntros (???????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%&H0&%&H1&Hwp)". iFrame. by iApply "Hmono".
  Qed.

  Lemma ghost_step_mono `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}
    (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ ν2) -∗
       ∀ E, ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros (E) "Hwp". iApply (ghost_step_mono_fupd with "[Hmono] Hwp").
    iIntros "H". iModIntro. by iApply "Hmono".
  Qed.

  Lemma fupd_ghost_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E lwp :
    (|={E}=> ghost_step E lwp) ⊢ ghost_step E lwp.
  Proof.
    iIntros "Hf". rewrite /ghost_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

  Lemma ghost_step_intro `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E Ψ :
    Ψ ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hlwp". rewrite /ghost_step.
    iIntros "%%%%%%% [_ H]". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_strong_mono `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E1 E2 Ψ1 Ψ2 :
    E1 ⊆ E2 →
    ghost_step E1 Ψ1 -∗ (Ψ1 ={E2}=∗ Ψ2) -∗ ghost_step E2 Ψ2.
  Proof.
    iIntros (HE) "IH Hu". rewrite /ghost_step.
    iIntros (???????) "H". iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_subseteq E1) as "close"; first done.
    iMod "IH" as "(%&H0&%&IH)". iFrame. iMod "close" as "_".
    iDestruct "IH" as "(H&Hwp)". iFrame. by iApply "Hu".
  Qed.

  Lemma ghost_step_atomic `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E1 E2 Ψ :
    (|={E1,E2}=> ghost_step E2 (|={E2,E1}=> Ψ)) ⊢ ghost_step E1 Ψ.
  Proof.
    iIntros "IH". rewrite /ghost_step.
    iIntros (???????) "H". iSpecialize ("IH" with "[$]").
    iMod "IH". iMod "IH". iDestruct "IH" as "(%&%&%&H&Hwp)".
    iMod "Hwp". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_idemp `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E Ψ :
    ghost_step E (ghost_step E Ψ) ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hg". rewrite /ghost_step.
    iIntros (???????) "H". iAssert (⌜ τ = dom δ ⌝)%I as "%TI".
    { iDestruct "H" as "[H _]". done. }
    iSpecialize ("Hg" with "[$]"). iMod "Hg".
    iDestruct "Hg" as "(%&%&%&H&Hg)". iSpecialize ("Hg" with "[-]"); first by iFrame.
    iDestruct "Hg" as ">(%&%&%&H&Hg)". iModIntro. iFrame.
    iPureIntro. by etransitivity.
  Qed.

End ghost_step.

Definition lift_term `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (i :thread_id) (Φ : val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (toL_term i ∗ Φ v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Liris, postcondition of a thread i must include toL_term i. *)
Definition lwp_pre `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => ghost_step E (Φ v)
     | None => lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef (lift_term j fork_post))
     end)%I.

Lemma lwp_pre_mono `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s
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
Definition lwp_pre' `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step. do 36 (f_equiv || done).
    remember (S (num_laters_per_step a3)) as x. clear Heqx. induction x.
    + simpl. do 11 (f_equiv || done). by apply pair_ne.
    + simpl. do 3 f_equiv. apply IHx.
Qed.

(* take the least fixpoint of the above definition *)
Local Definition lwp_def `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} : lWp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, (bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ).
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI hlc Λ Σ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} : lwp = @lwp_def SI hlc Λ Σ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.


Section lwp.
Context `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}.
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

Global Instance lwp_contractive s i E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !lwp_unfold /lwp_pre /lwp_step He /=.
  do 38 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a *)
  (*      proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 11 f_equiv.
Qed.

Lemma ghost_step_elim s i E e Φ :
  ghost_step E (lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "Hg". rewrite !lwp_unfold /lwp_pre /lwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { by iApply ghost_step_idemp. }
  iIntros (????????) "H". iAssert (⌜τ = dom δ1⌝)%I as "%TI".
  { iDestruct "H" as "[H _]". done. }
  rewrite /ghost_step. iSpecialize ("Hg" with "[$]"). iMod "Hg".
  iDestruct "Hg" as "(%&%&%&H&Hg)". iSpecialize ("Hg" with "[-]"); first by iFrame.
  iMod "Hg". iModIntro. iDestruct "Hg" as "(H&%&%&Hg)". iSplitL "H"; first done.
  iExists Ω2. iSplitR.
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
  iIntros (????????) "H". iSpecialize ("IH" with "[$]").
  iMod "IH" as "(%&%&%&IH)".
  iModIntro. iSplit; [by destruct s1, s2|clear H0]. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred".
  iMod ("IH" with "[//] [//] Hcred") as "IH". iIntros "!> !>".  iMod "IH". iModIntro.
  iApply (step_fupdN_wand with "[IH]"); first by iApply "IH".
  iIntros ">IH". iModIntro. iDestruct "IH" as "(%&%&%&%&H0&[H1 _]&Hefs)".
  iFrame. iExists _. iSplitR; first done.
  iApply (big_sepM_impl with "Hefs"). iIntros "!>" (k ef _). iIntros "[H _]". done.
Qed.

Lemma lwp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  lWP e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ lWP e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  (* iLöb as "IH" forall (e E1 E2 HE Φ Ψ). *)
  iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
  iApply lwp_ind_strong; [solve_proper|]. iModIntro. iIntros (i e E1 Φ) "IH % %HE HΦ".
  rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply (ghost_step_strong_mono with "IH"); done. }
  iIntros (????????) "H". iSpecialize ("IH" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "IH" as "(%&%&%&IH)".
  iModIntro. iSplit; [by destruct s1, s2|clear H0]. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred".
  iMod ("IH" with "[//] [//] Hcred") as "IH". iIntros "!> !>".  iMod "IH". iModIntro.
  iApply (step_fupdN_wand with "[IH]"); first by iApply "IH".
  iIntros ">IH". iMod "Hclose" as "_". iModIntro. iDestruct "IH" as "(%&%&%&%&H0&[H1 _]&Hefs)".
  iFrame. iExists _. iSplit; first done. iSplitR "Hefs".
  + by iApply "H1".
  + iApply (big_sepM_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
Qed.

Lemma fupd_lwp s i E e Φ : (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  rewrite /lwp_step. iIntros (????????) "Hp". iMod "H".
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
  iIntros (????????) "Hp". iAssert (⌜τ = dom δ1⌝)%I as "%TI".
  { iDestruct "Hp" as "[Hp _]". done. }
  iMod "H".  iMod ("H" with "[$]") as "(%&%&%&H)".
  iModIntro. iSplitR; first done. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred". iApply (step_fupdN_wand with "(H [//] [//] Hcred)").
  iIntros ">(%&%&%&%&H0&H&Hefs)".
  assert (TI2 : τ ∪ dom efs = dom δ3).
  { subst. destruct H2. eapply thread_ids_preserve; eauto. eapply fork_thread_ids; eauto. }
  destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iSpecialize ("H" with "[H0]"); first by iFrame.
      iMod "H". iDestruct "H" as "(%&%&%&H0&H)". iMod "H". iFrame.
      iModIntro. iExists Ω3. iSplit.
      * iPureIntro. destruct H3. split; first auto. etransitivity; eauto.
      * rewrite lwp_unfold /lwp_pre. rewrite He2. by iApply ghost_step_intro.
    + iMod ("H" $! _ _ _ _ _ [] _ _ with "[H0]") as "[H H']"; first by iFrame.
      iDestruct "H" as %(? & ? & ? & ? & ?). by edestruct (atomic _ _ _ _ _ _ H1).
  - destruct (atomic _ _ _ _ _ _ H1) as [v <-%of_to_val].
    rewrite lwp_value_fupd'. iMod ("H" with "[H0]") as "H"; first by iFrame.
    iDestruct "H" as "(%&%&%&H0&>H)". iModIntro. iFrame.
    iExists Ω3. iSplit.
    { iPureIntro. destruct H3. split; first auto. etransitivity; eauto. }
    iApply lwp_value_fupd'. by iApply ghost_step_intro.
Qed.

(** This lemma gives us access to the later credits that are generated in each step,
  assuming that we have instantiated [num_laters_per_step] with a non-trivial (e.g. linear)
  function.
  This lemma can be used to provide a "regeneration" mechanism for later credits.
  [state_interp] will have to be defined in a way that involves the required regneration
  tokens. TODO: point to an example of how this is used.

  In detail, a client can use this lemma as follows:
  * the client obtains the state interpretation [state_interp _ ns _ _],
  * it uses some ghost state wired up to the interpretation to know that
    [ns = k + m], and update the state interpretation to [state_interp _ m _ _],
  * _after_ [e] has finally stepped, we get [num_laters_per_step k] later credits
    that we can use to prove [P] in the postcondition, and we have to update
    the state interpretation from [state_interp _ (S m) _ _] to
    [state_interp _ (S ns) _ _] again. *)
Lemma lwp_credit_access s i E e Φ P :
  TCEq (to_val e) None →
  (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) →
  (∀ σ1 ns κs τ, state_interp σ1 ns κs τ ={E}=∗
                 ∃ k m, state_interp σ1 m κs τ ∗ ⌜ns = (m + k)%nat⌝ ∗
                        (∀ τ σ2 κs, £ (num_laters_per_step k) -∗ state_interp σ2 (S m) κs τ ={E}=∗
                                    state_interp σ2 (S ns) κs τ ∗ P)) -∗
  lWP e @ s; i; E {{ v, P ={E}=∗ Φ v }} -∗
                lWP e @ s; i; E {{ Φ }}.
Proof.
  rewrite !lwp_unfold /lwp_pre /=. iIntros (-> Htri) "Hupd Hwp".
  iIntros (????????) "(%Hd & H0 & H1 & H2 & H3 & Hσ1)".
  iMod ("Hupd" with "Hσ1") as (k m) "(Hσ1 & -> & Hpost)".
  iCombine "H0 H1 H2 H3 Hσ1" as "H".
  iMod ("Hwp" with "[H]") as "[$ Hwp]"; first by iFrame. iModIntro.
  iDestruct "Hwp" as "(%&%&Hwp)". iExists _. iSplit; first done.
  iIntros (e2 σ2 efs Hstep ???) "Hc".
  iDestruct "Hc" as "[Hone Hc]".
  iPoseProof (lc_weaken with "Hc") as "Hc"; first apply Htri.
  iDestruct "Hc" as "[Hm Hk]".
  iCombine "Hone Hm" as "Hm".
  iApply (step_fupd_wand with "(Hwp [//] [//] Hm)"). iIntros "Hwp".
  iApply (step_fupdN_le (num_laters_per_step m)); [ | done | ].
  { etrans; last apply Htri. lia. }
  iApply (step_fupdN_wand with "Hwp"). iIntros ">(%&%&%&%& (H0 & H1 & H2 & H3 & Hσ1) & Hwp & $)".
  iMod ("Hpost" with "Hk Hσ1") as "[$ HP]". iFrame. iModIntro.
  iExists _. iSplit; first done.
  iApply (lwp_strong_mono with "Hwp"); [by auto..|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.

(** In this stronger version of [lwp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [lwp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [lwp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma lwp_step_fupdN_strong n s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs τ, state_interp σ ns κs τ
                ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (lwp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !lwp_unfold /lwp_pre /=. iIntros (-> ?) "H".
  iIntros (????????) "(%Hd & H0 & H1 & H2 & H3 & Hσ)".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[-HP]") as "[$ H]"; first by iFrame. iMod "HP".
  iDestruct "H" as "(%&%&H)". iModIntro. iExists _. iSplit; first done.
  iIntros (e2 σ2 efs Hstep ???) "Hcred". iMod ("H" $! e2 σ2 efs with "[% //] [//] Hcred") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n IH] forall (n0 Hn).
  - iApply (step_fupdN_wand with "H").
    iIntros ">(%&%&%&%& (H0 & H1 & H2 & H3 & Hσ1) & Hwp & $)". iMod "HP".
    iModIntro. iFrame. iExists _. iSplit; first done.
    iApply (lwp_strong_mono with "Hwp"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma lwp_bind K `{!LanguageCtx K} s i E e Φ :
  lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }} ⊢ lWP K e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite lwp_unfold /lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply ghost_step_elim. }
  rewrite lwp_unfold /lwp_pre fill_not_val /=; [|done].
  iIntros (??? σ1 step κ κs τ) "(H0 & H1 & H2 & H3 & Hσ)". iMod ("H" with "[$]") as "(%&%&%&H)".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iExists _. iSplit; first done. iIntros (e2 σ2 efs Hstep ???) "Hcred".
  destruct (fill_step_inv e σ1 τ κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//] [//] Hcred") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "(%&%&%&%& (H0 & H1 & H2 & H3 & Hσ1) & Hwp & $)".
  iModIntro. iExists _, _. iSplit; first done. iFrame. by iApply "IH".
Qed.

Lemma lwp_bind_inv K `{!LanguageCtx K} s i E e Φ :
  lWP K e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply ghost_step_intro. by rewrite !lwp_unfold /lwp_pre. }
  rewrite fill_not_val; [|done].
  iIntros (??? σ1 step κ κs τ) "(H0 & H1 & H2 & H3 & Hσ)". iMod ("H" with "[$]") as "(%&%&%&H)".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iExists _. iSplit; first done. iIntros (e2 σ2 efs Hstep ???) "Hcred".
  iMod ("H" $! _ _ _ with "[] [//] Hcred") as "H"; first eauto using fill_step.
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as "(%&%&%&%& (H0 & H1 & H2 & H3 & Hσ1) & Hwp & $)".
  iModIntro. iExists _, _. iSplit; first done. iFrame. by iApply "IH".
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
Lemma lwp_step_fupdN n s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E1,∅}=∗
                 ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (lwp_step_fupdN_strong with "[H]"); [done|].
  iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma lwp_step_fupd s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }} -∗ lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (lwp_step_fupdN_strong 1 _ _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma lwp_frame_step_l s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ lWP e @ s; i; E2 {{ Φ }} ⊢ lWP e @ s; i; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (lwp_step_fupd with "Hu"); try done.
  iApply (lwp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma lwp_frame_step_r s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  lWP e @ s; i; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ lWP e @ s; i; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(lWP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply lwp_frame_step_l.
Qed.
Lemma lwp_frame_step_l' s i E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s i E E); try iFrame; eauto. Qed.
Lemma lwp_frame_step_r' s i E e Φ R :
  TCEq (to_val e) None → lWP e @ s; i; E {{ Φ }} ∗ ▷ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
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
  Context `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}.
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
