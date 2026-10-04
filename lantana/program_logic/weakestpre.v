From iris.proofmode Require Import base proofmode classes.
From lantana.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi.lib Require Export fixpoint_mono.
From lantana.bi Require Export weakestpre.
From iris.prelude Require Import options.
From lantana.program_logic Require Export temporal_class sfmupd model_physical_updates.
Import uPred.

(* TODO: move to somewhere else *)
Section curry5.
  Definition curry5 {A B C D E F : Type} (f : A * B * C * D * E → F) (a : A) (b : B) (c : C) (d : D) (e : E) : F :=
    f (a, b, c, d, e).
  Definition uncurry5 {A B C D E F : Type} (f : A → B → C → D → E → F) : (A * B * C * D * E) → F :=
    λ '(a, b, c, d, e), f a b c d e.

  Lemma curry5_uncurry5 : ∀ {A B C D E F : Type} (f : A → B → C → D → E → F), curry5 (uncurry5 f) = f.
  Proof. done. Qed.
  Lemma uncurry5_curry5 : ∀ {A B C D E F : Type} (f : A * B * C * D * E → F) (p : A * B * C * D * E), uncurry5 (curry5 f) p = f p.
  Proof. intros. destruct p as [[[[a b] c] d] e]. done. Qed.

  Global Instance uncurry5_proper' : ∀ {A : Type} {RA : relation A} {B : Type} {RB : relation B} {C : Type} {RC : relation C} {D : Type} {RD : relation D} {E : Type} {RE : relation E} {F : Type} {RF : relation F},
    Proper
      ((RA ==> RB ==> RC ==> RD ==> RE ==> RF) ==>
         prod_relation (prod_relation (prod_relation (prod_relation RA RB) RC) RD) RE ==> RF)
      (@uncurry5 A B C D E F).
  Proof.
    intros. repeat intro.
    destruct x0 as [[[[a0 b0] c0] d0] e0], y0 as [[[[a1 b1] c1] d1] e1].
    simpl. destruct H0 as [[[[? ?] ?] ?] ?]. simpl in *. by eapply H.
  Qed.
  Global Instance uncurry5_proper : ∀ {A : Type} {H : Equiv A} {B : Type} {H0 : Equiv B} {C : Type} {H1 : Equiv C} {D : Type} {H2 : Equiv D} {E : Type} {H3 : Equiv E} {F : Type} {H4 : Equiv F},
    Proper ((equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) ==> equiv ==> equiv) (@uncurry5 A B C D E F).
  Proof. intros. eapply uncurry5_proper'. Qed.

  Global Instance uncurry5_ne : ∀ {SI : sidx} {A B C D E F : ofe} (n : SI),
    Proper ((dist n ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n) (@uncurry5 A B C D E F).
  Proof. intros. apply uncurry5_proper. Qed.
End curry5.


(** Running the m-updates of several threads, as the adequacy proofs do. *)
Section run_sfmupd.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!TemporalInterp Λ Σ}.

  Lemma all_interp_sfmupd_steps_gmap (γ : thread_id → nat) E h n σ Θ κs g v Ω W
    (A : Type) (TQ : gmap thread_id ((expr Λ) * A)) (P : thread_id → (expr Λ) → A → iProp Σ) :
    (owit_inv_lb (fair_sched_fun γ) Ω W) →
    ([∗ map] i ↦ '(e, a) ∈ TQ, |={E}=>m (P i e a)) -∗
    history_tinterp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={E}=∗
    (([∗ map] i ↦ '(e, a) ∈ TQ, (P i e a)) ∗ history_tinterp h n σ Θ κs ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb (fair_sched_fun γ) Ω' W' ⌝ ∗ model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (LB) "PS HI MI".
    iAssert (|={E}=>m [∗ map] i ↦ '(e, a) ∈ TQ, P i e a)%I with "[PS]" as "PS".
    { iApply big_sepM_sfmupd. iApply (big_sepM_impl with "PS"). iIntros "!>" (k [e a] _) "H". done. }
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "PS HI MI") as "$".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    { done. }
    done.
  Qed.

End run_sfmupd.

Class lantanaGS `{SI : sidx} (Λ : language) (Σ : gFunctors) :=
  LantanaG {
      (** Ghost states for temporal properties. *)
      #[global] lantana_temporalGS :: temporalGS Λ Σ;

      (** The state (and history) interpretation is an invariant that should hold in
          between each step of reduction.
          Here [state] is the global state, [thread_ids] is the allocated thread ids,
          and [list (observation Λ)] are the remaining observations. *)
      #[global] lantana_state_interp_class :: state_interp_class Λ Σ;

      (** A fixed postcondition for any forked-off thread. For most languages, e.g.
          heap_lang, this will simply be [True]. However, it is useful if one wants to
          keep track of resources precisely, as in e.g. Iron. *)
      fork_post : thread_id → val Λ → iProp Σ;
    }.

Global Opaque lantana_temporalGS lantana_state_interp_class.
Global Arguments LantanaG {SI Λ Σ}.

(** Predicates we take the fixpoint of in order to define the lWP. *)
(* Ω must make strict progress for every step (to bound step-index) *)
(* W witnesses progress of obligations; it relies on the fair scheduler for soundness *)
Definition lwp_step `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ}
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ K h n σ1 Θ κ κs,
     (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
     (history_tinterp h n σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
      (** ** Model update (discharge allowed) for the pre-state; the adequacy proof
          handles a discharge here through the deep records of the until (see
          temporal_guarantee.v, [tguar]). *)
      |=[n,dom Θ]=>m
      (⌜if s is NotStuck then reducible i e1 σ1 (dom Θ) else True⌝) ∗
      ∀ e2 σ2 (efs : thread_pool Λ), (⌜ prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs ⌝) -∗
      @={n,(dom Θ),i}=↓ (@={n,(S n),(dom Θ),(dom (<[i:=K e2]>Θ) ∪ dom efs)}=>
      (** ** Discharge allowed for post-state *)
      (ALC (|=[(S n),(dom (<[i:=K e2]>Θ) ∪ dom efs)]=>m |={∅,E}=>
              ((history_tinterp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)]) (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
               state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
              ν e2 efs))))%I.

Section lwp_step.
  Context `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ}.

  Global Instance lwp_step_ne s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step. do 34 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono s (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (?????????) "H". iSpecialize ("Hwp" $! K with "[//] [//] [$]").
    iMod "Hwp". iModIntro. iMod "Hwp" as "($& Hwp)". iModIntro.
    iIntros (???) "H0".
    iDestruct ("Hwp" with "[$]") as ">>>Hwp".
    iMod "Hwp" as "Hwp". iModIntro. iMod "Hwp" as "[$ H]".
    by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros (?????????). iMod "Hf" as "Hf". iApply ("Hf" $! K with "[//] [//]").
  Qed.

  Lemma sfmupd_lwp_step s i E e lwp :
    (|={E}=>m lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros (?????????) "[HI HA]".
    unfold_sfmupd. iPoseProof ("Hf" with "HI") as ">Hf".
    iModIntro. iMod "Hf". iApply fupd_mupd_elim. iMod "Hf" as "(HI& Hf)".
    iApply ("Hf" with "[//] [//] [$HI $HA]").
  Qed.

  (** An m-update after the step can be absorbed into the step. *)
  Lemma lwp_step_post_sfmupd s i E e ν :
    lwp_step s i E e ν ⊣⊢ lwp_step s i E e (λ e' efs, |={E}=>m ν e' efs).
  Proof.
    iSplit; iIntros "H".
    - iIntros "%%%%%%%%% HI". iMod ("H" $! K with "[//] [//] HI") as "H".
      iModIntro. iMod "H" as "[$ H]".
      iIntros "!> %%% Hs". iMod ("H" with "Hs") as ">>>H".
      iDestruct "H" as ">(HI& H)". iModIntro. iFrame. iApply sfmupd_intro. done.
    - iIntros "%%%%%%% %% HI". iMod ("H" $! K with "[//] [//] HI") as "H".
      iModIntro. iMod "H" as "[$ H]".
      iIntros "!> %%% Hs". iMod ("H" with "Hs") as ">>>H".
      iDestruct "H" as ">([HI SIa]& H)". iEval (unfold_sfmupd) in "H". iMod ("H" with "HI") as "H".
      rewrite /fmupd dom_union_L. iModIntro. iMod "H". iMod "H" as "[HI H]". iModIntro. iFrame.
  Qed.

End lwp_step.

(** Wrapper for the termination condition for soundness. *)
Definition lift_term `{SI : sidx} `{!lantanaGS Λ Σ} (i :thread_id) (Φ : thread_id → val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (thP_done i ∗ Φ i v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Lantana, postcondition of a thread i must include othreadG_term i. *)
Definition lwp_pre `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => |={E}=>m (Φ v)
     | None =>
         (lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef (lift_term j fork_post)))
     end)%I.

Lemma lwp_pre_mono `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} s
  (lwp1 lwp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, lwp1 i E e Φ -∗ lwp2 i E e Φ) →
     ∀ i E e Φ, lwp_pre s lwp1 i E e Φ -∗ lwp_pre s lwp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Hlwp". rewrite /lwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (lwp_step_mono with "[] Hlwp"). iModIntro.
  iIntros (e efs) "[Hlwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  iApply (@big_sepM_impl with "Hefs"); iIntros "!#" (k e' _) "Hlwp".
  by iApply "Hmono".
Qed.

(* Uncurry [lwp_pre] and equip its type with an OFE structure *)
Definition lwp_pre' `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step.
    do 36 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition; we can also just take fixpoint. *)
Definition lwp_fix `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} : stuckness -> thread_id -> coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E e Φ, ((bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ))%I.

Local Definition lwp_def `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} : Lwp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, (lwp_fix s i E e Φ)%I.
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI Λ Σ _ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} : lwp = @lwp_def SI Λ Σ _ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.

Section lwp.
  Context `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance lwp_fix_ne s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_fix s i E e).
  Proof. intros Φ Ψ HΦ. rewrite /lwp_fix. f_equiv. by apply pair_ne. Qed.
  Global Instance lwp_fix_proper s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_fix s i E e).
  Proof. by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_fix_ne=>v; apply equiv_dist. Qed.

  Lemma lwp_pre_lwp_pre' s _lwp i E e Φ :
    lwp_pre s _lwp i E e Φ = lwp_pre' s (λ '(i,E,e,Φ), _lwp i E e Φ) (i,E,e,Φ).
  Proof. rewrite /lwp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.

  Lemma lwp_fix_unfold_fix s i E e Φ :
    lwp_fix s i E e Φ ⊣⊢ (lwp_pre s (lwp_fix s) i E e Φ).
  Proof.
    rewrite /lwp_fix. rewrite lwp_pre_lwp_pre'.
    rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
    - done.
    - done.
  Qed.
  Lemma lwp_fix_unfold s i E e Φ :
    lwp_fix s i E e Φ ⊣⊢ (lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ).
  Proof.
    rewrite /lwp_fix lwp_unseal. rewrite lwp_pre_lwp_pre' /lwp_def.
    rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
    - done.
    - done.
  Qed.

  Lemma lwp_unfold s i E e Φ :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ).
  Proof.
    rewrite lwp_unseal /lwp_def. rewrite lwp_fix_unfold lwp_unseal /lwp_def. auto.
  Qed.
  Lemma lwp_unfold_fix s i E e Φ :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_fix s i E e Φ).
  Proof. rewrite lwp_unfold lwp_fix_unfold. done. Qed.

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
        [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=.
      etransitivity; first apply HΨ, H2. done. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[[? ?] ?] ?]) "H". iApply "IH". rewrite lwp_pre_lwp_pre'.
    iApply (bi_mono_pred with "[] H").
    { repeat intro. do 3 (f_equiv || done). }
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      inv H0; simpl in *. inv H1; simpl in *. inv H0; simpl in *.
      apply leibniz_equiv in H3, H1, H4. subst. f_equiv.
      { f_equiv. done. }
      { rewrite /lwp_def. f_equiv. f_equiv. done. }
    }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ?] ?].
    iSplit.
    - iDestruct "H" as "[H _]". done.
    - iDestruct "H" as "[_ H]". done.
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
    intros Φ1 Φ2 HΦ. rewrite !lwp_unseal /lwp_def.
    by apply (least_fixpoint_ne _), pair_ne, HΦ.
  Qed.
  Global Instance lwp_proper s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp (PROP:=iProp Σ) s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_ne=>v; apply equiv_dist.
  Qed.

  Lemma fupd_lwp s i E e Φ :
    (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_unfold. rewrite /lwp_pre /lwp_step.
    destruct (to_val e) as [v|] eqn:?.
    { iMod "H". rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo. done. }
    iIntros (?????????) "SI". iMod "H".
    rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo.
    iMod ("H" $! K with "[//] [//] SI") as "H". iModIntro. iMod "H" as "[$ h]". done.
  Qed.

  Lemma sfmupd_lwp s i E e Φ :
    (|={E}=>m lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". rewrite !lwp_unfold /lwp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { by iApply sfmupd_trans. }
    by iApply sfmupd_lwp_step.
  Qed.

  Lemma lwp_value_sfmupd' s i E Φ v :
    lWP of_val v @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m (Φ v).
  Proof.
    iSplit; iIntros "H".
    - by rewrite lwp_unfold /lwp_pre to_of_val.
    - by rewrite lwp_unfold /lwp_pre to_of_val.
  Qed.
  Lemma lwp_stuckness_mono s1 s2 i E e Φ :
    s1 ⊑ s2 →
    lWP e @ s1; i; E {{ Φ }} -∗ lWP e @ s2; i; E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iRevert (i e E Φ) "H". iApply lwp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
    rewrite !lwp_unfold /lwp_pre /=.
    destruct (to_val e) as [v|] eqn:?; first done.
    iIntros (??????? ??) "H". iMod ("IH" $! K with "[//] [//] [$]") as "H".
    iModIntro. iMod "H". iModIntro.
    iPoseProof "H" as "[% IH]".
    iSplit; [by destruct s1, s2|clear H0].
    iIntros (????). iMod ("IH" with "[//]") as ">>IH".
    iMod "IH" as "IH". iModIntro.
    iMod "IH" as "($& [IH Efs])". iDestruct "IH" as "[IH _]".
    iModIntro. iFrame.
    iApply (big_sepM_impl with "Efs"). iIntros "!>" (k ef _). iIntros "[H _]". done.
  Qed.

  Lemma lwp_strong_mono_sfmupd s1 s2 i E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    (lWP e @ s1; i; E1 {{ Φ }}) -∗ (∀ v, Φ v -∗ |={E2}=>m (Ψ v)) -∗ (lWP e @ s2; i; E2 {{ Ψ }}).
  Proof.
    iIntros (? HE) "H HΦ".
    iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
    iApply lwp_ind_strong; [solve_proper| ].
    iIntros "!>" (i e E1 Φ) "IH % %HE HΦ".
    rewrite lwp_unfold /lwp_pre /=.
    destruct (to_val e) as [v|] eqn:?.
    { iApply sfmupd_trans. iApply (sfmupd_mask_mono E1 E2 _ HE).
      iMod "IH". iModIntro. iApply ("HΦ" with "IH"). }
    iIntros (??????? ??) "H". iSpecialize ("IH" $! K with "[//] [//] [$]").
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod "IH". iModIntro. iMod "IH" as "(%& IH)".
    iModIntro.
    iSplit; [by destruct s1, s2|clear H0].
    iIntros (????). iMod ("IH" with "[//]") as ">>IH".
    iMod "IH". iModIntro. iMod "IH" as "[$ IH]".
    iMod "Hclose" as "_". iModIntro.
    iDestruct "IH" as "([IH _]& Efs)".
    iSplitR "Efs".
    + by iApply "IH".
    + iApply (big_sepM_impl with "Efs"); iIntros "!>" (k ef _).
      iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
  Qed.
  Lemma lwp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    (lWP e @ s1; i; E1 {{ Φ }}) -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ (lWP e @ s2; i; E2 {{ Ψ }}).
  Proof.
    iIntros (? HE) "H HΦ".
    iApply (lwp_strong_mono_sfmupd with "H [HΦ]"). all: auto.
    iIntros "% H". iMod ("HΦ" with "H") as "$". done.
  Qed.

  Lemma lwp_fupd s i E e Φ :
    lWP e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply (lwp_strong_mono s s i E with "H"); auto. Qed.
  Lemma lwp_atomic_sfmupd s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=>m lWP e @ s; i; E2 {{ v, |={E2,E1}=>m Φ v }})
    ⊢ lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". rewrite !lwp_unfold /lwp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { iMod "H". iMod "H". iMod "H". by iModIntro. }
    iIntros (??????? ??) "[HI HA]".
    unfold_sfmupd. iMod ("H" with "HI") as "H". iModIntro. iMod "H". iMod "H" as "[HI H]".
    iMod ("H" $! K with "[//] [//] [$HI $HA]") as "H".
    iModIntro. iMod "H".
    iModIntro. iPoseProof "H" as "[$ H]".
    iIntros (??? STEP). iMod ("H" with "[//]") as "H".
    iMod "H". iMod "H" as ">>(SI& H& Efs)".
    destruct s.
    - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iEval (unfold_sfmupd) in "H". iDestruct "SI" as "[HI HA]".
        iMod ("H" with "HI") as "H".
        assert (DomEq : dom (<[i:=K e2]> Θ ∪ efs) = dom (<[i:=K e2]> Θ) ∪ dom efs).
        { rewrite dom_union_L. auto. }
        rewrite !DomEq. rewrite /fmupd. iModIntro. iMod "H". iMod "H" as "(HI& H)".
        iMod ("H" with "HI") as "H". iModIntro.
        rewrite !DomEq. iMod "H". iModIntro.
        iMod "H" as "[HI H]". iModIntro. iFrame. iApply sfmupd_intro. done.
      + iMod ("H" $! K _ _ _ _ [] with "[//] [] SI") as "H".
        { iPureIntro. rewrite -insert_union_l lookup_insert_eq; auto. }
        assert (DomEq : dom (<[i:=K e2]> Θ ∪ efs) = dom (<[i:=K e2]> Θ) ∪ dom efs).
        { rewrite dom_union_L. auto. }
        rewrite !DomEq.
        iModIntro. iMod "H" as "[Red H]".
        iDestruct "Red" as %(? & ? & ? & ? & ?).
        replace ((dom (<[i:=K e2]> Θ) ∪ dom efs)) with (dom Θ ∪ dom efs) in H1.
        1: by edestruct (atomic _ _ _ _ _ _ _ STEP).
        rewrite dom_insert_lookup_L; eauto.
    - destruct (atomic _ _ _ _ _ _ _ STEP) as [v <-%of_to_val].
      rewrite lwp_value_sfmupd'.
      iEval (unfold_sfmupd) in "H". iDestruct "SI" as "[HI HA]".
      iMod ("H" with "HI") as "H".
      assert (DomEq : dom (<[i:=K (of_val v)]> Θ ∪ efs) = dom (<[i:=K (of_val v)]> Θ) ∪ dom efs).
      { rewrite dom_union_L. auto. }
      rewrite !DomEq. rewrite /fmupd. iModIntro. iMod "H". iMod "H" as "(HI& H)".
      iMod ("H" with "HI") as "H". iModIntro.
      rewrite !DomEq. iMod "H". iModIntro.
      iMod "H" as "[HI H]". iModIntro. iFrame. rewrite lwp_value_sfmupd'. iApply sfmupd_intro. done.
  Qed.

  Lemma lwp_atomic s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=> lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})
    ⊢ lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_atomic_sfmupd. iMod "H". iModIntro.
    iApply (lwp_strong_mono with "H"). 1,2: done. iIntros (?) "H". iModIntro.
    by iApply fupd_sfmupd.
  Qed.

  Lemma lwp_step_sfmupd s i E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    ((|={E1,E2}=>m |={E2,E1}=>m P) ∗
     lWP e @ s; i; E2 {{ v, P -∗ |={E1}=>m Φ v }}) -∗
    lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros (? ?) "[HP Hwp]". iApply (lwp_strong_mono_sfmupd with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
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
    lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}
                  ⊢ (lWP K e @ s; i; E {{ Φ }}).
  Proof.
    revert Φ.
    cut (∀ Φ', (lWP e @ s; i; E {{ Φ' }}) -∗
               ∀ Φ, (∀ v, (Φ' v) -∗ (lWP K (of_val v) @ s; i; E {{ Φ }})) -∗
                    (lWP K e @ s; i; E {{ Φ }})).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". iIntros (Φ) "H2".
    iRevert (Φ) "H2".
    iRevert (i e E Φ') "H". iApply lwp_ind_strong; first solve_proper.
    iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
    iEval (rewrite /lwp_pre) in "IH". destruct (to_val e) as [v|] eqn:He.
    { apply of_to_val in He as <-. iApply sfmupd_lwp.
      iMod "IH". iModIntro. by iApply "HΦ". }
    rewrite lwp_unfold /lwp_pre /lwp_step. rewrite fill_not_val; last auto.
    iIntros (K1 ?????? HK1 LU1) "SI".
    iSpecialize ("IH" $! (ctx_comp K1 K)). iEval (rewrite !ctx_comp_apply) in "IH".
    iMod ("IH" with "[] [//] SI") as "IH".
    { iPureIntro. apply _. }
    iModIntro. iMod "IH" as "(%& IH)". iModIntro. iSplit.
    { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
    iIntros (e2 σ2 efs Hstep).
    destruct (fill_step_inv (K:=K) i e σ1 (dom Θ) κ e2 σ2 efs) as (e2'&->&?); auto.
    iDestruct ("IH" $! _ _ _ H0) as ">IH".
    iEval (rewrite !ctx_comp_apply) in "IH".
    iMod "IH" as ">>IH". iMod "IH". iDestruct "IH" as "(SI& IH& Efs)".
    rewrite (bi.sep_assoc). iSplitR "Efs"; cycle 1.
    { iModIntro. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% [_ H]". done. }
    iDestruct "IH" as "[IH _]". iPoseProof ("IH" with "HΦ") as "IH".
    by iFrame.
  Qed.

  Lemma lwp_bind_step K `{!LanguageCtx K} s i E e Φ :
    lWP e @ s; i; E {{ v, |={E}=>m (lWP K (of_val v) @ s; i; E {{ Φ }}) }}
    ⊢ lWP K e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_bind. iApply (lwp_strong_mono with "H"); [done..|]. iIntros (v) "H !>". by iApply sfmupd_lwp.
  Qed.

  Lemma lwp_sfmupd s i E e Φ :
    lWP e @ s; i; E {{ v, |={E}=>m (Φ v) }}
    ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply (lwp_strong_mono_sfmupd s s i E with "H"); auto. Qed.

  Lemma lwp_bind_sfmupd K `{!LanguageCtx K} s i E e Φ :
    (|={E}=>m lWP e @ s; i; E {{ v, |={E}=>m (lWP K (of_val v) @ s; i; E {{ Φ }}) }})
    ⊢ |={E}=>m lWP K e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iMod "H". iModIntro. by iApply lwp_bind_step. Qed.

  Lemma sfmupd_lwp_sfmupd s i E e Φ :
    (|={E}=>m lWP e @ s; i; E {{ v, |={E}=>m (Φ v) }})
    ⊢ |={E}=>m lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iMod "H". iModIntro. by iApply lwp_sfmupd. Qed.

  (** FIXME: does this hold when we have ∀ K in lwp? Just remove this if this is not used anywhere else. *)
  (* Lemma lwp_bind_inv K `{!LanguageCtx K} s i E e Φ : *)
  (*   lWP K e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}. *)
  (* Proof. *)
  (*   iIntros "H". remember (K e) as e' eqn:He'. *)
  (*   iRevert (e He'). iRevert (i e' E Φ) "H". iApply lwp_ind_strong; first solve_proper. *)
  (*   iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->). *)
  (*   rewrite !lwp_unfold {2}/lwp_pre. *)
  (*   destruct (to_val e) as [v|] eqn:He. *)
  (*   { apply of_to_val in He as <-. iModIntro. rewrite !lwp_unfold. *)
  (*     iApply (lwp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]". } *)
  (*   rewrite /lwp_pre fill_not_val; [|done]. *)
  (*   iIntros (K1 ?????? HK1 LU1) "SI". iMod ("IH" $! (K1 ∘ K) with "[] [//] SI") as "IH". *)
  (*   iModIntro. iPoseProof "IH" as "(%& IH)". iSplitR. *)
  (*   { destruct s; eauto using reducible_fill_inv. } *)
  (*   iIntros (e2 σ2 efs Hstep). iDestruct ("IH" with "[]") as ">IH". *)
  (*   { eauto using fill_step. } *)
  (*   iMod "IH" as ">>IH". iModIntro. iMod "IH" as "(SI& IH& Efs)". *)
  (*   iModIntro. iFrame. iSplitR "Efs". *)
  (*   - iDestruct "IH" as "[IH _]". by iApply "IH". *)
  (*   - iApply (big_sepM_impl with "Efs"). iIntros "!> %%% >[_ H]". done. *)
  (* Qed. *)

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

  Lemma lwp_value_sfmupd s i E Φ e v :
    IntoVal e v →
    lWP e @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m (Φ v).
  Proof. intros <-. by apply lwp_value_sfmupd'. Qed.
  Lemma lwp_value' s i E Φ v : (Φ v) ⊢ lWP (of_val v) @ s; i; E {{ Φ }}.
  Proof. rewrite lwp_value_sfmupd'. apply sfmupd_intro. Qed.
  Lemma lwp_value s i E Φ e v : IntoVal e v → (Φ v) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. intros <-. apply lwp_value'. Qed.

  Lemma lwp_frame_l s i E e Φ R :
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma lwp_frame_r s i E e Φ R :
    lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
  Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

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
    TCEq (to_val e) None →
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
  Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s i E E); try iFrame; eauto. Qed.
  Lemma lwp_frame_step_r' s i E e Φ R :
    TCEq (to_val e) None →
    lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
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

  (** Later credits. *)
  Lemma lwp_lc_later_ord s i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s i E e Φ :
    £n n -∗ (▷^n lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lantana.base_logic.fancy_updates.lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  (** Modality instances for lwp. *)
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

  Global Instance elim_modal_sfmupd_lwp p s i E e P Φ :
    ElimModal True p false (|={E}=>m P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (_) "[P H]". iApply sfmupd_lwp. iMod "P".
    iModIntro. by iApply ("H" with "P").
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

  Global Instance elim_modal_sfmupd_lwp_atomic p s i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=>m P) P
            (lWP e @ s; i; E1 {{ Φ }}) (lWP e @ s; i; E2 {{ v, |={E2,E1}=>m Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      sfmupd_frame_r wand_elim_r lwp_atomic_sfmupd.
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

  Global Instance add_modal_fupd_lwp s i E e P Φ :
    AddModal (|={E}=> P) P (lWP e @ s; i; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_lwp. Qed.

  Global Instance add_modal_sfmupd_lwp s i E e P Φ :
    AddModal (|={E}=>m P) P (lWP e @ s; i; E {{ Φ }}).
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

  Global Instance elim_acc_lwp_atomic_sfmupd {X} i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
      (sfmupd E1 E2) (sfmupd E2 E1)
      α β γ (lWP e @ s; i; E1 {{ Φ }})
      (λ x, lWP e @ s; i; E2 {{ v, |={E2}=>m β x ∗ (γ x -∗? Φ v) }})%I | 100.
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

  Global Instance elim_acc_lwp_nonatomic_sfmupd {X} i E α β γ e s Φ :
    ElimAcc (X:=X) True (sfmupd E E) (sfmupd E E)
      α β γ (lWP e @ s; i; E {{ Φ }})
      (λ x, lWP e @ s; i; E {{ v, |={E}=>m β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_sfmupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
