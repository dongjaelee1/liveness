From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop.
From lantana.algebra Require Import axioms.

(** * Fair scheduling

    Every thread that is active is eventually scheduled. The fairness counter ([fscnt])
    bounds, for every thread, the steps of other threads until its next turn. *)

Definition thread_active {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '((Θ, σ), _, _) := ξ in ∃ e, Θ !! i = Some e ∧ to_val e = None.

Definition thread_na {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '((Θ, σ), _, _) := ξ in (Θ !! i = None ∨ ∃ e, Θ !! i = Some e ∧ is_Some (to_val e)).

Definition thread_turn {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '(_, j, _) := ξ in i = j.

Definition fair_scheduling {Λ : language} : trProp Λ :=
  tr_always (∀ i, (ts_emb (thread_na i)) ∨
                  ((ts_emb (thread_active i)) ∧ tr_eventually (ts_emb (thread_turn i))))%R.

Section thread_status.
  Context {Λ : language}.
  Implicit Type ξ : trace_state Λ.
  Implicit Type τ : trace Λ.

  Lemma fair_scheduling_next (τ : trace Λ) :
    fair_scheduling τ → fair_scheduling (trace_next τ).
  Proof.
    unfold fair_scheduling, tr_always. destruct τ as (n& τf). simpl. intros.
    specialize (H m). apply H. lia.
  Qed.

  Global Instance thread_na_decide i ξ : Decision (thread_na i ξ).
  Proof.
    unfold thread_na. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + left. right. eauto.
      + right. intros F. destruct F; first done. destruct H as (?&?&?). inv H. rewrite He in H0. done.
    - left. auto.
  Qed.

  Global Instance thread_active_decide i ξ : Decision (thread_active i ξ).
  Proof.
    unfold thread_active. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + right. intros F. destruct F as (?&?&?). inv H.
      + left. eauto.
    - right. intros F. destruct F as (?&?&?). inv H.
  Qed.

  Lemma thread_active_and_not_false i ξ : thread_na i ξ → thread_active i ξ → False.
  Proof.
    unfold thread_na, thread_active. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn.
    intros. destruct (Θ !! i) eqn:LUi.
    + destruct (to_val e) eqn: EQe.
      * destruct H; [done |]. destruct H0 as (?&?&?). inv H0.
      * destruct H; [done |]. destruct H as (?&?&?). inv H. rewrite EQe in H1. done.
    + destruct H0 as (?&?&?). done.
  Qed.
  Lemma ts_emb_thread_active_and_not_false i τ :
    (ts_emb (thread_na i)) τ → (ts_emb (thread_active i)) τ → False.
  Proof.
    destruct τ as (n&τf). unfold ts_emb. simpl. apply thread_active_and_not_false.
  Qed.

  Lemma thread_active_or_not i ξ : thread_na i ξ ∨ thread_active i ξ.
  Proof.
    unfold thread_na, thread_active.
    destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn.
    destruct (Θ !! i) eqn:LUi; eauto.
    destruct (to_val e) eqn: EQe; eauto.
  Qed.
  Lemma ts_emb_thread_active_or_not i τ : (ts_emb (thread_na i)) τ ∨ (ts_emb (thread_active i)) τ.
  Proof.
    destruct τ as (n&τf). unfold ts_emb. simpl. apply thread_active_or_not.
  Qed.

End thread_status.

Section fair_sched_cnt.
  Context {Λ : language}.
  Implicit Type ξ : trace_state Λ.
  Implicit Type τ : trace Λ.

  Definition fscnt : Type := thread_id → nat.

  CoInductive beh_fscnt_th (τ : trace Λ) (i : thread_id) (c : nat) : Prop :=
  | beh_fscnt_th_step ξ j c' :
    j = trace_thread τ →
    ξ = trace_now τ →
    ((thread_na i ξ) ∨ (thread_active i ξ ∧ (if (decide (i = j)) then True else c' < c))) →
    beh_fscnt_th (trace_next τ) i c' →
    beh_fscnt_th τ i c.
  Definition beh_fscnt (τ : trace Λ) (γ : fscnt) : Prop :=
    ∀ (i : thread_id), beh_fscnt_th τ i (γ i).

  (** Uses choice. *)
  Lemma fair_scheduling_fscnt (τ : trace Λ) :
    fair_scheduling τ → ∃ (γ : fscnt), beh_fscnt τ γ.
  Proof.
    intros FS. unfold beh_fscnt. apply choice. intros i. destruct τ as (n&τf).
    assert (∀ (s : nat),
              (((ts_emb (thread_na i) (n, τf))) ∨
               ((ts_emb (thread_active i) (n, τf)) ∧ (ts_emb (thread_turn i) (s + n, τf))))
              → beh_fscnt_th (n, τf) i s); cycle 1.
    { destruct (ts_emb_thread_active_or_not i (n, τf)) as [TH | TH].
      - exists 0. specialize (H 0). apply H. left. auto.
      - specialize (FS n). unshelve edestruct FS. 1: exact i. 1: lia.
        { exfalso. eapply (ts_emb_thread_active_and_not_false _ ((n, τf))); eauto. }
        destruct H0 as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - n) as s. assert (m = s + n) by lia. subst m. clear Heqs LEm.
        exists s. apply H. right. auto. }
    revert n FS. cofix CIH; intros. destruct H as [TH | TH].
    - rename TH into TNA. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
      destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
      + econstructor. 1,2: eauto. 1: auto.
        unshelve eapply (CIH _ _ 0); auto. apply fair_scheduling_next. auto.
      + pose proof FS as FSn'. specialize (FSn' (S n)).
        unshelve edestruct FSn'. 1: exact i. 1: lia.
        { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
        destruct H as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
        eapply (beh_fscnt_th_step _ _ _ _ _ s'). 1,2: eauto. 1: auto.
        eapply CIH.
        * apply fair_scheduling_next; auto.
        * right. eauto.
    - destruct TH as [TA TTurn]. destruct s.
      (* A case split on [s], not an induction (which may break the guard condition). *)
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        unfold ts_emb, thread_turn in TTurn. simpl in TTurn. rewrite Htrn in TTurn. subst j.
        destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
        - econstructor. 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; eauto. }
          unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
        - pose proof FS as FSn'. specialize (FSn' (S n)).
          unshelve edestruct FSn'. 1: exact i. 1: lia.
          { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
          destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
          remember (m - (S n)) as s. assert (m = s + S n) by lia. subst m. clear Heqs LEm.
          eapply (beh_fscnt_th_step _ _ _ _ _ s). 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
          apply CIH; auto. apply fair_scheduling_next; auto. }
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        destruct (decide (j = i)).
        - subst j. destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
          + econstructor. 1,2: eauto.
            { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
            unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
          + pose proof FS as FSn'. specialize (FSn' (S n)).
            unshelve edestruct FSn'. 1: exact i. 1: lia.
            { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
            destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
            remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
            eapply (beh_fscnt_th_step _ _ _ _ _ s'). 1,2: eauto.
            { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
            apply CIH; auto. apply fair_scheduling_next; auto.
        - eapply (beh_fscnt_th_step _ _ _ _ _ s). 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_False; auto. }
          apply CIH; auto.
          + apply fair_scheduling_next; auto.
          + simpl. destruct (ts_emb_thread_active_or_not i (S n, τf)) as [? | TA2]; first auto.
            right. replace (s + S n) with (S (s + n)) by lia. split; auto. }
  Qed.

  Definition fscnt_next_rel_th (τ : trace Λ) i (c1 c2 : nat) : Prop :=
    if (decide (i = trace_thread τ)) then True
    else if (decide (thread_na i (trace_now τ))) then True
         else (c2 < c1).
  Definition fscnt_next_rel (τ : trace Λ) (γ1 γ2 : fscnt) : Prop :=
    ∀ i, fscnt_next_rel_th τ i (γ1 i) (γ2 i).

  (** Uses choice. *)
  Lemma exists_fscnt_next (τ : trace Λ) (γ : fscnt) :
    beh_fscnt τ γ →
    ∃ γ', beh_fscnt (trace_next τ) γ' ∧ fscnt_next_rel τ γ γ'.
  Proof.
    intros Beh. unfold beh_fscnt, fscnt_next_rel.
    cut (∃ γ', ∀ i, (λ i c, beh_fscnt_th (trace_next τ) i c ∧ fscnt_next_rel_th τ i (γ i) c) i (γ' i)).
    { intros. destruct H. exists x. split; intros; firstorder. }
    apply choice. intros i. specialize (Beh i). inv Beh.
    exists c'. split; auto. unfold fscnt_next_rel_th.
    destruct τ as (n&τf). unfold trace_thread, trace_now. simpl in *.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. simpl.
    destruct (decide (i = j)); auto. destruct H1.
    { rewrite decide_True; auto. }
    destruct H.
    rewrite /trace_thread /trace_now in H0. simpl in H0. rewrite Htrn in H0. simpl in H0.
    rewrite decide_False in H0; auto.
    rewrite decide_False; auto.
    intros F. eapply thread_active_and_not_false; by eauto.
  Qed.

End fair_sched_cnt.
