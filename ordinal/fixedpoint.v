From lantana.ordinal Require Import sflib basics classical_ordinal.
From lantana.ordinal Require Export ordinal.

Set Implicit Arguments.
Set Primitive Projections.


Section FIXPOINT.
  Variable D: Type.
  Variable base: D.
  Variable next: D -> D.
  Variable djoin: forall (A: Type) (ds: A -> D), D.

  Variable dle: D -> D -> Prop.
  Variable wf: D -> Prop.

  Let deq: D -> D -> Prop :=
    fun d0 d1 => dle d0 d1 /\ dle d1 d0.

  Hypothesis dle_reflexive: forall d (WF: wf d), dle d d.
  Hypothesis dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: dle d0 d1) (LE1: dle d1 d2),
      dle d0 d2.

  Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)), dle (ds a) (djoin ds).
  Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
  Hypothesis djoin_wf: forall A (ds: A -> D) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)), wf (djoin ds).

  Hypothesis base_wf: wf base.
  Hypothesis next_wf: forall d (WF: wf d), wf (next d).

  Hypothesis next_le: forall d (WF: wf d), dle d (next d).
  Hypothesis next_eq: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (EQ: deq d0 d1), deq (next d0) (next d1).

  Lemma fixpoint_theorem_le:
    dle (next (ord.rec base next djoin (ord.hartogs D))) (ord.rec base next djoin (ord.hartogs D)).
  Proof.
    eapply (classicOrd._fixpoint_theorem base next djoin dle wf); eauto.
  Qed.

  (* Bourbaki-Witt theorem *)
  Theorem fixpoint_theorem:
    deq (next (ord.rec base next djoin (ord.hartogs D))) (ord.rec base next djoin (ord.hartogs D)).
  Proof.
    split.
    { apply fixpoint_theorem_le. }
    { apply next_le. eapply (classicOrd.rec_wf base next djoin dle wf); auto. }
  Qed.
End FIXPOINT.


Section ALGEBRA.
  Variable A: Type.
  Let kappa := ord.hartogs (A -> Prop).
  Let le: (A -> Prop) -> (A -> Prop) -> Prop :=
    fun P0 P1 => forall a (IN0: P0 a), P1 a.
  Let ge: (A -> Prop) -> (A -> Prop) -> Prop :=
    fun P0 P1 => forall a (IN0: P1 a), P0 a.
  Let join (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
    fun a => exists x, Ps x a.
  Let meet (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
    fun a => forall x, Ps x a.
  Let bot: A -> Prop := fun _ => False.
  Let top: A -> Prop := fun _ => True.

  Variable f: (A -> Prop) -> (A -> Prop).
  Hypothesis mon: forall (P0 P1: A -> Prop) (LE: le P0 P1), le (f P0) (f P1).

  Let mon_rev: forall (P0 P1: A -> Prop) (LE: ge P0 P1), ge (f P0) (f P1).
  Proof.
    ii. eapply mon; eauto.
  Qed.

  Definition mu := ord.rec bot f join kappa.
  Definition nu := ord.rec top f meet kappa.

  Theorem mu_fixpoint:
    le mu (f mu) /\ le (f mu) mu.
  Proof.
    split.
    { hexploit (ord.rec_wf bot f join le (fun P => le P (f P))); eauto.
      { ii. eapply LE1; eauto. }
      { ii. exists a. auto. }
      { ii. inv IN0. eapply LE; eauto. }
      { ii. inv IN0. eapply WF in H.
        eapply mon; eauto. ii. exists x. auto. }
      { ii. ss. }
    }
    { hexploit (fixpoint_theorem_le bot f join le (fun P => le P (f P))); eauto.
      { ii. ss. }
      { ii. eapply LE1; eauto. }
      { ii. exists a. auto. }
      { ii. inv IN0. eapply LE; eauto. }
      { ii. inv IN0. eapply WF in H.
        eapply mon; eauto. ii. exists x. auto. }
      { ii. ss. }
      { ii. des. split; apply mon; auto. }
    }
  Qed.

  Theorem mu_least P (LE: le (f P) P): le mu P.
  Proof.
    eapply (ord.rec_wf bot f join le (fun P0 => le P0 (f P0) /\ le P0 P)); eauto.
    { ii. eapply LE1; eauto. }
    { ii. exists a. auto. }
    { ii. inv IN0. eapply LE0; eauto. }
    { ii. split; auto.
      - ii. inv IN0. destruct (WF x). eapply H0 in H.
        eapply mon; eauto. ii. exists x. auto.
      - ii. inv IN0. destruct (WF x). eapply H1 in H; auto. }
    { split; ss. }
    { i. des. splits; auto. ii. eapply LE. eapply mon; eauto. }
  Qed.

  Theorem nu_fixpoint:
    le nu (f nu) /\ le (f nu) nu.
  Proof.
    split.
    { hexploit (fixpoint_theorem_le top f meet ge (fun P => le (f P) P)); eauto.
      { ii. ss. }
      { ii. eapply LE0; eauto. }
      { ii. eapply IN0; eauto. }
      { ii. eapply LE. auto. }
      { ii. eapply WF. eapply mon_rev in IN0; eauto.
        ii. eapply IN1; auto. }
      { ii. ss. }
      { ii. des. split; apply mon_rev; auto. }
    }
    { hexploit (ord.rec_wf top f meet ge (fun P => le (f P) P)); eauto.
      { ii. eapply LE0; eauto. }
      { ii. eapply IN0; eauto. }
      { ii. eapply LE. auto. }
      { ii. eapply WF. eapply mon_rev in IN0; eauto.
        ii. eapply IN1; auto. }
      { ii. ss. }
    }
  Qed.

  Theorem nu_greatest P (LE: le P (f P)): le P nu.
  Proof.
    eapply (ord.rec_wf top f meet ge (fun P0 => le (f P0) P0 /\ le P P0)); eauto.
    { ii. eapply LE0; eauto. }
    { ii. eapply IN0; eauto. }
    { ii. eapply LE0. auto. }
    { ii. split.
      - ii. edestruct (WF x). eapply H. eapply mon_rev in IN0; eauto.
        ii. eapply IN1; auto.
      - ii. eapply WF. auto. }
    { ii. ss. }
    { ii. des. splits; auto. ii. eapply LE in IN0. eapply mon; eauto. }
  Qed.
End ALGEBRA.
