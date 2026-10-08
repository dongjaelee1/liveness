From stdpp Require Import base.
From iris.prelude Require Import options.
From lantana.prelude Require Import axioms.
From lantana.base_logic Require Import obligation.
From lantana.program_logic Require Import temporal_property.

(** * Every obligation is discharged under fairness, without a witness ordinal

  The adequacy proof (adequacy.v) shows that an assigned obligation is
  eventually discharged by building, from the fairness assumption and the
  axiom of choice, a witness ordinal [ω·fuel ⊕ γ(owner)] that strictly
  decreases on every step of every thread ([fair_sched_fun]), and inducting
  on it. This is a global lexicographic ranking function, with the
  scheduler's delay as a component.

  In the style of transition invariants (Podelski & Rybalchenko) the same
  fact follows from a stabilization argument that never builds a bound: an
  obligation's fuel is non-increasing in a well-founded order and strictly
  decreases whenever its owner is scheduled or it changes owner, so if it
  were never discharged its fuel would stabilize, hence its owner would
  stabilize and never be scheduled again, contradicting fairness, since an
  owner is active. Only classical logic is used, not choice.

  The argument is stated over an abstract run: the obligation state at each
  position, the scheduled thread, and which threads are active, under the
  four facts the model provides (see [mprog_exists_step] and
  [obls_thread_active] in adequacy.v). [trace_fair_eventually_turn]
  instantiates the fairness hypothesis from [fair_scheduling]. *)

Section stabilize.
  Context `{OC : obl_class}.

  Variable Ωs : nat → obls.
  Variable sched : nat → obl_owner.
  Variable active : nat → obl_owner → Prop.
  Variable n0 : nat.

  (** (1) Obligations never go up: fuel is non-increasing, an owner change
      needs a strict decrease, a discharged obligation stays discharged. *)
  Hypothesis LE : ∀ n, n0 ≤ n → obls_le (Ωs n) (Ωs (S n)).
  (** (2) The scheduled thread makes strict progress on every obligation it owns. *)
  Hypothesis PROG : ∀ n k f i,
    n0 ≤ n → Ωs n !! k = Some (obl_assigned f i) → sched n = i →
    (∃ f' i', Ωs (S n) !! k = Some (obl_assigned f' i') ∧ f' w< f) ∨
    Ωs (S n) !! k = Some obl_discharged.
  (** (3) The owner of an obligation is an active thread. *)
  Hypothesis ACT : ∀ n k f i,
    n0 ≤ n → Ωs n !! k = Some (obl_assigned f i) → active n i.
  (** (4) Fair scheduling: an active thread is eventually scheduled. *)
  Hypothesis FAIR : ∀ n i, n0 ≤ n → active n i → ∃ m, n ≤ m ∧ sched m = i.

  (** An obligation's entry only moves down [obl_le] along the run. *)
  Local Lemma persist k g n m :
    n0 ≤ n → n ≤ m → Ωs n !! k = Some g → ∃ g', Ωs m !! k = Some g' ∧ obl_le g g'.
  Proof using All.
    intros Hn0 Hle. revert g. induction Hle as [| m Hle IH]; intros g Hk.
    { exists g. split; auto. reflexivity. }
    destruct (IH g Hk) as (g1& Hk1& Hg1).
    destruct (LE m) as (Hdom& Hpt). 1: lia.
    assert (is_Some (Ωs (S m) !! k)) as [g2 Hk2].
    { apply elem_of_dom. apply Hdom. apply elem_of_dom. eauto. }
    exists g2. split; auto. etransitivity; eauto.
  Qed.

  Local Lemma assigned_le f i g :
    obl_le (obl_assigned f i) g →
    g = obl_discharged ∨ ∃ f' i', g = obl_assigned f' i' ∧ f' w≤ f.
  Proof using All.
    destruct g as [f' i' |]; simpl; intros H; [right | by left].
    exists f', i'. split; auto. destruct H as [[? ?] | ?]; auto. by apply WFOCM.lt_le.
  Qed.

  Theorem obl_eventually_discharged k f i :
    Ωs n0 !! k = Some (obl_assigned f i) →
    ∃ m, n0 ≤ m ∧ Ωs m !! k = Some obl_discharged.
  Proof using All.
    intros Hk0.
    destruct (classic (∃ m, n0 ≤ m ∧ Ωs m !! k = Some obl_discharged)) as [| Hnever]; first done.
    exfalso.
    (* Never discharged: assigned at every position, with non-increasing fuel. *)
    assert (ASG : ∀ m, n0 ≤ m → ∃ f' i', Ωs m !! k = Some (obl_assigned f' i') ∧ f' w≤ f).
    { intros m Hm. destruct (persist k _ n0 m ltac:(lia) Hm Hk0) as (g& Hg& Hle).
      destruct (assigned_le _ _ _ Hle) as [-> | (f'& i'& -> & ?)]; eauto.
      exfalso. apply Hnever. eauto. }
    (* Fuel stabilizes: from some N on, no step strictly decreases it. *)
    assert (STAB : ∀ f1, ∀ n, n0 ≤ n → (∃ i1, Ωs n !! k = Some (obl_assigned f1 i1)) →
              ∃ N, n ≤ N ∧ ∀ m, N ≤ m →
                ∀ fm im fm' im', Ωs m !! k = Some (obl_assigned fm im) →
                  Ωs (S m) !! k = Some (obl_assigned fm' im') → ¬ (fm' w< fm)).
    { intros f1. induction f1 as [f1 IH] using WFOCM.ind. intros n Hn (i1& Hk1).
      destruct (classic (∃ m, n ≤ m ∧ ∃ fm im fm' im', Ωs m !! k = Some (obl_assigned fm im) ∧
                                Ωs (S m) !! k = Some (obl_assigned fm' im') ∧ fm' w< fm))
        as [(m& Hm& fm& im& fm'& im'& Hkm& Hkm'& Hlt) | Hno].
      - (* a strict decrease below f1 happens at m: induct from there *)
        destruct (persist k _ n m Hn Hm Hk1) as (g& Hg& Hle).
        rewrite Hkm in Hg. inversion Hg; subst g. clear Hg.
        destruct (assigned_le _ _ _ Hle) as [? | (?& ?& Heq& Hfm)]; first done.
        inversion Heq; subst. clear Heq.
        assert (fm' w< f1) by (eapply WFOCM.lt_le_lt; eauto).
        destruct (IH fm' ltac:(done) (S m) ltac:(lia) ltac:(eauto)) as (N& HN& HNstab).
        exists N. split; [lia | auto].
      - exists n. split; first lia. intros m Hm fm im fm' im' Hkm Hkm' Hlt.
        apply Hno. eauto 10. }
    destruct (ASG n0 ltac:(lia)) as (f1& i1& Hk1& _).
    destruct (STAB f1 n0 ltac:(lia) ltac:(eauto)) as (N& HN& Hstab).
    (* From N on the owner is fixed. *)
    destruct (ASG N ltac:(lia)) as (fN& iN& HkN& _).
    assert (OWN : ∀ m, N ≤ m → ∃ fm, Ωs m !! k = Some (obl_assigned fm iN)).
    { intros m Hm. induction Hm as [| m Hm IHm]; first eauto.
      destruct IHm as (fm& Hkm).
      destruct (ASG (S m) ltac:(lia)) as (fm'& im'& Hkm'& _).
      destruct (LE m ltac:(lia)) as (_& Hpt).
      specialize (Hpt k _ _ Hkm Hkm'). simpl in Hpt.
      destruct Hpt as [[_ <-] | Hlt]; first eauto.
      exfalso. eapply Hstab; eauto. }
    (* The owner is active, hence scheduled at some m ≥ N, where it must make
       strict progress on k: a decrease (excluded) or a discharge (excluded). *)
    destruct (FAIR N iN ltac:(lia) (ACT N k fN iN ltac:(lia) HkN)) as (m& Hm& Hsched).
    destruct (OWN m Hm) as (fm& Hkm).
    destruct (PROG m k fm iN ltac:(lia) Hkm Hsched) as [(fm'& im'& Hkm'& Hlt) | Hdis].
    - eapply Hstab; eauto; lia.
    - apply Hnever. exists (S m). split; [lia | done].
  Qed.

End stabilize.

(** Fair scheduling of a trace supplies hypothesis (4). *)
Lemma trace_fair_eventually_turn {Λ : language} (τf : nat → trace_state Λ) n0 :
  fair_scheduling (n0, τf) →
  ∀ m i, n0 ≤ m → thread_active i (τf m) → ∃ m', m ≤ m' ∧ trace_thread (m', τf) = i.
Proof.
  intros FS m i Hm Hact. specialize (FS m Hm). unshelve edestruct FS as [Hna | [_ Hev]]. 1: exact i.
  { exfalso. eapply (ts_emb_thread_active_and_not_false i (m, τf)); eauto. }
  unfold tr_eventually, tr_until in Hev. destruct Hev as (m'& Hle& Hturn& _).
  exists m'. split; auto.
  unfold ts_emb, thread_turn, trace_thread, trace_now in *. simpl in *.
  destruct (τf m') as (((Θ& σ)& j)& κs). simpl. done.
Qed.
