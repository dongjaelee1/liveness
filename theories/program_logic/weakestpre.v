From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From liveness Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liveness.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.
From liveness Require Import ordinal_wfocm thread_obligation.

Notation Π Λ := (state Λ).

Class lirisGS_gen `{SI : indexT} (hlc : has_lc) (Λ : language) (Σ : gFunctors) := LirisG {
  (** Invariants. *)
  #[global] liris_invGS :: invGS_gen hlc Σ;
  (** Liveness obligation interpretation. *)
  #[global] liris_osatGS :: osatGS.osatGS (WF:=ord_wfocm_pack) (Π Λ) Σ;
  (** Scheduler fairness interpretation. *)
  #[global] liris_schedfairGS :: schedfairGS.schedfairGS (WF:=@fuel_wf Λ) Σ;
  (** Connecting liveness obligations and scheduler fairness. *)
  (* #[global] liris_oblfuelGS :: ofuelGS.ofuelGS Σ; *)
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
  definition of LWP) and later credits per physical step is
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

Notation lirisGS := (lirisGS_gen HasLc).
Notation "'⌈' Λ '⌉'" := (Ord.from_wf_set (@WFOCM.lt_wf _ _ _ _ (@fuel_wf Λ))).
Notation schedfairIL Λ := (schedfairI (H:=@fuel_wf Λ)).
Notation toIL Λ := (toI (WF:=@fuel_wf Λ) (ps:=Π Λ)).

(** The predicate we take the fixpoint of in order to define the LWP. *)
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
  (∀ ϕ0 Ω0 γ σ1 ns κ κs τ, (schedfairIL Λ ϕ0 ∗ osat Ω0 ∗ toIL Λ γ ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
                           (⌜if s is NotStuck then reducible e1 σ1 τ else True⌝) ∗
                           ∃ Ω1, (⌜(Ω0 ↪ₛ⋆ Ω1 @ σ1)⌝) ∗
                                 ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                                              ∀ ϕ1 ϕ2 ϕ3, (⌜fuels_fair_update {[i]} ϕ0 ϕ1 ∧ ϕ2 = fuels_thread_yield i e2 ϕ1 ∧ fuels_fair_fork efs ϕ2 ϕ3⌝) -∗
                                                          £ (S (num_laters_per_step ns))
                                                          ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ Ω2 Ω3, (⌜(∃ os, γ !! i = Some os ∧ (Ω1 ↪ₗ⁺ Ω2 @ os; σ2)) ∧ (Ω2 ↪ₛ⋆ Ω3 @ σ2)⌝) ∗
              ∃ γ', (schedfairIL Λ ϕ3 ∗ osat Ω3 ∗ toIL Λ γ' ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    ν e2 efs
  )%I.

Section lwp_step.

  Global Instance lwp_step_ne `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step.
    do 37 (f_equiv || done). simpl. do 3 f_equiv.
    induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
    do 13 (f_equiv || done).
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
    iIntros (???) "H0 H". iSpecialize ("Hwp" with "[$]").
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
  (∀ ϕ Ω γ σ ns κs τ, (schedfairIL Λ ϕ ∗ osat Ω ∗ toIL Λ γ ∗ state_interp σ ns κs τ) ={E}=∗
                      ∃ Ω', (⌜(Ω ↪ₛ⋆ Ω' @ σ)⌝) ∗
                            ∃ γ', (schedfairIL Λ ϕ ∗ osat Ω' ∗ toIL Λ γ' ∗ state_interp σ ns κs τ) ∗
                                  ν
  )%I.

Section ghost_step.

  Global Instance ghost_step_ne `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E :
    NonExpansive (ghost_step E).
  Proof.
    intros n Φ Ψ HΦ. rewrite /ghost_step. do 26 (f_equiv || done).
  Qed.
  Global Instance ghost_step_proper `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E :
    Proper ((≡) ==> (≡)) (ghost_step E).
  Proof.
    intros Φ Φ' ?. apply equiv_dist=>n. apply ghost_step_ne. by apply equiv_dist.
  Qed.

  Lemma ghost_step_mono_fupd `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}
    E (ν1 ν2 : iPropO Σ) :
    ⊢ ((□ (ν1 -∗ |={E}=> ν2)) →
       ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros "Hwp". rewrite /ghost_step.
    iIntros (???????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%&H0&%&H1&Hwp)". iFrame. by iApply "Hmono".
  Qed.

  Lemma ghost_step_mono `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}
    (ν1 ν2 : iPropO Σ) :
    ⊢ ((□ (ν1 -∗ ν2)) →
       ∀ E, ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (E) "Hwp". iApply ghost_step_mono_fupd; [|done].
    iModIntro. iIntros "H". iModIntro. by iApply "Hmono".
  Qed.

  Lemma fupd_ghost_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E lwp :
    (|={E}=> ghost_step E lwp) ⊢ ghost_step E lwp.
  Proof.
    iIntros "Hf". rewrite /ghost_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

  Lemma ghost_step_elim `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} E Ψ :
    Ψ ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hlwp". rewrite /ghost_step.
    iIntros "%%%%%%% H". iModIntro. by iFrame.
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
    iIntros (???????) "H". iSpecialize ("Hg" with "[$]"). iMod "Hg".
    iDestruct "Hg" as "(%&%&%&H&Hg)". iSpecialize ("Hg" with "[$]").
    iDestruct "Hg" as ">(%&%&%&H&Hg)". iModIntro. iFrame.
    iPureIntro. by etransitivity.
  Qed.

End ghost_step.


(* pre-definition of lwp of which we take a least fixpoint *)
Definition lwp_pre `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => ghost_step E (Φ v)
     | None => lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef fork_post)
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
    rewrite /curry4 /lwp_pre /lwp_step. do 38 (f_equiv || done).
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

Lemma lwp_value' s i E Φ v : Φ v ⊢ lWP of_val v @ s; i; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite lwp_unfold /lwp_pre to_of_val. by iApply ghost_step_elim. Qed.

Global Instance lwp_contractive s i E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !lwp_unfold /lwp_pre /lwp_step He /=.
  do 40 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a *)
  (*      proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 11 f_equiv.
Qed.

TODO

Lemma ghost_step_intro s i E e Φ :
  ghost_step E (lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "Hg". rewrite !lwp_unfold /lwp_pre /lwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { by iApply ghost_step_idemp. }
  iIntros (????????) "H". rewrite /ghost_step.
  iSpecialize ("Hg" with "[$]"). iMod "Hg".
  iDestruct "Hg" as "(%&%&%&H&Hg)". iSpecialize ("Hg" with "[$]").
  iMod "Hg". iModIntro. iDestruct "Hg" as "(H&%&%&Hg)". iSplitL "H"; first done.
  iExists Ω1. iSplitR.
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
  iIntros (??) "H". iSpecialize ("IH" with "[$]").
  iIntros (??) "H". iSpecialize ("IH" with "[$]").
  iIntros (?????) "H". iSpecialize ("IH" with "[$]"). iMod "IH" as "(%&%&%&IH)".
  iModIntro. iSplit; [by destruct s1, s2|clear H0]. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred".
  iMod ("IH" with "[//] [//] Hcred") as "IH". iIntros "!> !>".  iMod "IH". iModIntro.
  iApply (step_fupdN_wand with "[IH]"); first by iApply "IH".
  iIntros ">IH". iModIntro.
  iDestruct "IH" as "(H0&%&%&H1&H2&H3&[H4 _]&H5)".
  iFrame. iApply (big_sepM_impl with "H5"). iIntros "!>" (k ef _).
  iIntros "[H _]". done.
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
  iIntros (??) "H". iSpecialize ("IH" with "[$]").
  iIntros (??) "H". iSpecialize ("IH" with "[$]").
  iIntros (?????) "H". iSpecialize ("IH" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "IH" as "(%&%&%&IH)".
  iModIntro. iSplit; [by destruct s1, s2|clear H0]. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred".
  iMod ("IH" with "[//] [//] Hcred") as "IH". iIntros "!> !>".  iMod "IH". iModIntro.
  iApply (step_fupdN_wand with "[IH]"); first by iApply "IH".
  iIntros ">IH". iMod "Hclose" as "_". iModIntro.
  iDestruct "IH" as "(H0&%&%&H1&H2&H3&[H4 _]&H5)".
  iFrame. iSplitR "H5".
  + by iApply "H4".
  + iApply (big_sepM_impl with "H5"); iIntros "!>" (k ef _).
    iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
Qed.

Lemma fupd_lwp s i E e Φ : (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  rewrite /lwp_step. iIntros "%% H0 %% H1 %%%%% H2". iMod "H".
  iSpecialize ("H" with "[$] [$] [$]"). done.
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
  iIntros "%% H0 %% H1 %%%%% H2". iMod "H". iMod ("H" with "[$] [$] [$]") as "(%&%&%&H)".
  iModIntro. iSplitR; first done. iExists _. iSplitR; first done.
  iIntros (???????) "Hcred". iApply (step_fupdN_wand with "(H [//] [//] Hcred)").
  iIntros ">(H0 & %&%&% & H1 & Hσ & H & Hefs)".

  TODO

  destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iSpecialize ("H" with "[$] [$] [$]"). iMod "H".
      iDestruct "H" as "(H0&%&%&%&H1&H2&H3)". iMod "H3". iFrame.
      iModIntro. iSplit.
      * iPureIntro. destruct H3 as (?&?&?). eexists. split; eauto.
      2:{ rewrite lwp_unfold /lwp_pre. rewrite He2. by iApply ghost_step_elim. }

      iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite wp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". by iApply wp_value_fupd'.
Qed.


  iIntros ">H".

  TODO

  iIntros (?).
  iIntros "(Hσ & H & Hefs)". destruct s.


  iIntros "%".

  iIntros (??) "H". iSpecialize ("IH" with "[$]").
  iIntros (Ω γ) "H". iSpecialize ("IH" with "[$]").
  iIntros (σ ns κs τ) "H". iSpecialize ("IH" with "[$]").
  iMod "IH". iMod "IH". iDestruct "IH" as "(H0&%&H1&%&H2&H3&H4)". 

  iFrame. by iFrame.


  iApply (ghost_step_atomic E1 E2). 

  iApply (fupd_mask

  iModIntro. iMod "Hwp". iModIntro.
  iApply (ghost_step_mono with  "[] Hwp"). iModIntro. iIntros "Hwp".
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "Hwp" as ">>H". }

  
  iIntros (ϕ) "H". iSpecialize ("IH" with "[$]").
  iIntros (Ω γ) "H". iSpecialize ("IH" with "[$]").
  iIntros (σ ns κs τ) "H". iSpecialize ("IH" with "[$]").
  iModIntro. 

  iMod (fupd_mask_subseteq E1) as "close"; first done. iMod "IH" as "[H IH]". iFrame.
  iMod "close" as "_". iDestruct "IH" as "(%&H0&%&H1&H2&H3)". iFrame. by iApply "Hu".

  iMod "H". iMod "H". iDestruct "H" as "[H | H]".
  - iLeft. destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>H". }

    iMod (fupd_intro E1 with "H") as "H".
    iApply fupd_mask_intro.
    iModIntro.
    
    iIntros (ϕ0 ϕ1) "H". iSpecialize ("Hwp" $! ϕ0 ϕ1 with "H").
    iIntros (Ω γ) "H". iSpecialize ("Hwp" $! Ω γ with "H").
    iIntros (σ1 ns κ κs τ) "H". iSpecialize ("Hwp" $! σ1 ns κ κs τ with "H").
    iMod "Hwp" as "(H&Hwp)". iModIntro. iFrame.
    iIntros (e2 σ2 efs) "H". iSpecialize ("Hwp" $! e2 σ2 efs with "H").
    iIntros "H". iSpecialize ("Hwp" with "H").
    iApply (step_fupdN_wand with "Hwp"). iIntros ">Hwp". iModIntro.
    iIntros (ϕ2 ϕ3) "H". iSpecialize ("Hwp" $! ϕ2 ϕ3 with "H"). iDestruct "Hwp" as "(H0&%&H1&%&H2&H3&H4)".
    iFrame. by iApply "Hmono".
    



    iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep) "Hcred".
    iApply (step_fupdN_wand with "(H [//] Hcred)").
    iIntros ">(Hσ & H & Hefs)". destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite lwp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". by iApply lwp_value_fupd'.
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
Lemma lwp_credit_access s E e Φ P :
  TCEq (to_val e) None →
  (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ∃ k m, state_interp σ1 m κs nt ∗ ⌜ns = (m + k)%nat⌝ ∗
    (∀ nt σ2 κs, £ (num_laters_per_step k) -∗ state_interp σ2 (S m) κs nt ={E}=∗
      state_interp σ2 (S ns) κs nt ∗ P)) -∗
  LWP e @ s; E {{ v, P ={E}=∗ Φ v }} -∗
  LWP e @ s; E {{ Φ }}.
Proof.
  rewrite !lwp_unfold /lwp_pre /=. iIntros (-> Htri) "Hupd Hwp".
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("Hupd" with "Hσ1") as (k m) "(Hσ1 & -> & Hpost)".
  iMod ("Hwp" with "Hσ1") as "[$ Hwp]". iModIntro.
  iIntros (e2 σ2 efs Hstep) "Hc".
  iDestruct "Hc" as "[Hone Hc]".
  iPoseProof (lc_weaken with "Hc") as "Hc"; first apply Htri.
  iDestruct "Hc" as "[Hm Hk]".
  iCombine "Hone Hm" as "Hm".
  iApply (step_fupd_wand with "(Hwp [//] Hm)"). iIntros "Hwp".
  iApply (step_fupdN_le (num_laters_per_step m)); [ | done | ].
  { etrans; last apply Htri. lia. }
  iApply (step_fupdN_wand with "Hwp"). iIntros ">(SI & Hwp & $)".
  iMod ("Hpost" with "Hk SI") as "[$ HP]". iModIntro.
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
Lemma lwp_step_fupdN_strong n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    LWP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  LWP e @ s; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (lwp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !lwp_unfold /lwp_pre /=. iIntros (-> ?) "H".
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". iMod ("H" $! e2 σ2 efs with "[% //] Hcred") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n IH] forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros ">($ & Hwp & $)". iMod "HP".
    iModIntro. iApply (lwp_strong_mono with "Hwp"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma lwp_bind K `{!LanguageCtx K} s E e Φ :
  LWP e @ s; E {{ v, LWP K (of_val v) @ s; E {{ Φ }} }} ⊢ LWP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite lwp_unfold /lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_lwp. }
  rewrite lwp_unfold /lwp_pre fill_not_val /=; [|done].
  iIntros (σ1 step κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//] Hcred") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

Lemma lwp_bind_inv K `{!LanguageCtx K} s E e Φ :
  LWP K e @ s; E {{ Φ }} ⊢ LWP e @ s; E {{ v, LWP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !lwp_unfold /lwp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step.
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma lwp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → LWP e @ s; E {{ Φ }} ⊢ LWP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (lwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma lwp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → LWP e @ s1; E {{ Φ }} ⊢ LWP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (lwp_strong_mono with "H"); auto. Qed.
Lemma lwp_stuck_weaken s E e Φ :
  LWP e @ s; E {{ Φ }} ⊢ LWP e @ E ?{{ Φ }}.
Proof. apply lwp_stuck_mono. by destruct s. Qed.
Lemma lwp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → LWP e @ s; E1 {{ Φ }} ⊢ LWP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (lwp_strong_mono with "H"); auto. Qed.
Global Instance lwp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (lwp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.
Global Instance lwp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (lwp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.

Lemma lwp_value_fupd s E Φ e v : IntoVal e v → LWP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply lwp_value_fupd'. Qed.
Lemma lwp_value' s E Φ v : Φ v ⊢ LWP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite lwp_value_fupd'. auto. Qed.
Lemma lwp_value s E Φ e v : IntoVal e v → Φ v ⊢ LWP e @ s; E {{ Φ }}.
Proof. intros <-. apply lwp_value'. Qed.

Lemma lwp_frame_l s E e Φ R : R ∗ LWP e @ s; E {{ Φ }} ⊢ LWP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma lwp_frame_r s E e Φ R : LWP e @ s; E {{ Φ }} ∗ R ⊢ LWP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the LWP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma lwp_step_fupdN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    LWP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  LWP e @ s; E1 {{ Φ }}.
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
Lemma lwp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ LWP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ LWP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (lwp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma lwp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ LWP e @ s; E2 {{ Φ }} ⊢ LWP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (lwp_step_fupd with "Hu"); try done.
  iApply (lwp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma lwp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  LWP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ LWP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(LWP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply lwp_frame_step_l.
Qed.
Lemma lwp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ LWP e @ s; E {{ Φ }} ⊢ LWP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma lwp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → LWP e @ s; E {{ Φ }} ∗ ▷ R ⊢ LWP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma lwp_wand s E e Φ Ψ :
  LWP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ LWP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (lwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma lwp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ LWP e @ s; E {{ Φ }} ⊢ LWP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_wand_r s E e Φ Ψ :
  LWP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ LWP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_frame_wand s E e Φ R :
  R -∗ LWP e @ s; E {{ v, R -∗ Φ v }} -∗ LWP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (lwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS_gen hlc Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_lwp p s E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (LWP e @ s; E {{ Φ }}) (LWP e @ s; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite lwp_frame_l. apply lwp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_lwp s E e Φ : IsExcept0 (LWP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_lwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_lwp p s E e P Φ :
    ElimModal True p false (|==> P) P (LWP e @ s; E {{ Φ }}) (LWP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  Global Instance elim_modal_fupd_lwp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (LWP e @ s; E {{ Φ }}) (LWP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_lwp.
  Qed.
  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_lwp_wrong_mask p s E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_lwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (LWP e @ s; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_lwp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (LWP e @ s; E1 {{ Φ }}) (LWP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r lwp_atomic.
  Qed.
  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_lwp_atomic_wrong_mask p s E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (LWP e @ s; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_lwp s E e P Φ :
    AddModal (|={E}=> P) P (LWP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_lwp. Qed.

  Global Instance elim_acc_lwp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (LWP e @ s; E1 {{ Φ }})
            (λ x, LWP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_lwp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (LWP e @ s; E {{ Φ }})
            (λ x, LWP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_fupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
