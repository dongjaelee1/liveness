From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop.
From lantana.algebra Require Import axioms.

(** * Rules for trace properties ([trProp])

    The interface for the external reading of what a program guarantees: entailment
    [R ⊆ S] with the rules of the connectives and the state atoms, the laws of LTL and the
    fixpoint rules. Trace properties are predicates on traces (trace_prop.v), so every valid
    rule is provable from the definitions, classically; [tr_unfold] is the escape hatch.

    Connectives (scope [%R]): [⌜φ⌝], [∧], [∨], [→], [∀], [∃], the state atom [tr_state φ]
    (a fact about the current state and thread pool), [□ R], [◇ R], [○ R], [R Uₜ S]. *)

Global Instance tr_le_preorder {Λ : language} : PreOrder (⊆@{trProp Λ}).
Proof. split; [by intros R τ|intros R S T HRS HST τ HR; by apply HST, HRS]. Qed.


Ltac tr_unfold :=
  unfold subseteq, tr_subseteq, tr_le, tr_next, tr_eventually, tr_until, tr_always, tr_exist,
    tr_forall, tr_impl, tr_or, tr_and, tr_pure, tr_state, ts_emb, ts_state, trace_now in *; simpl in *.

(** ** Propositional rules, quantifiers and state atoms *)
Section tr_rules.
  Context {Λ : language}.
  Implicit Types R S A X : trProp Λ.

  (** Pure facts, truth and falsity. *)
  Lemma tr_pure_intro R (φ : Prop) : φ → R ⊆ (⌜φ⌝)%R.
  Proof. intros Hφ τ _. exact Hφ. Qed.
  Lemma tr_pure_elim (φ : Prop) S : (φ → ∀ τ, S τ) → (⌜φ⌝)%R ⊆ S.
  Proof. intros HS τ Hφ. by apply HS. Qed.
  Lemma tr_pure_mono (φ ψ : Prop) : (φ → ψ) → (tr_pure φ : trProp Λ) ⊆ tr_pure ψ.
  Proof. intros Hφψ τ. apply Hφψ. Qed.
  (** A pure atom at a position is the fact itself (in intro patterns: [H%tr_pure_at]). *)
  Lemma tr_pure_at (φ : Prop) (τ : trace Λ) : tr_pure φ τ → φ.
  Proof. done. Qed.
  Lemma tr_true_intro R : R ⊆ (⌜True⌝)%R.
  Proof. by intros τ. Qed.
  Lemma tr_false_elim S : (⌜False⌝)%R ⊆ S.
  Proof. by intros τ []. Qed.

  (** Conjunction. *)
  Lemma tr_and_intro R S1 S2 : R ⊆ S1 → R ⊆ S2 → R ⊆ (S1 ∧ S2)%R.
  Proof. intros H1 H2 τ HR. tr_unfold. auto. Qed.
  Lemma tr_and_elim_l S1 S2 : (S1 ∧ S2)%R ⊆ S1.
  Proof. intros τ [? _]. done. Qed.
  Lemma tr_and_elim_r S1 S2 : (S1 ∧ S2)%R ⊆ S2.
  Proof. intros τ [_ ?]. done. Qed.
  Lemma tr_and_mono R1 R2 S1 S2 : R1 ⊆ S1 → R2 ⊆ S2 → (R1 ∧ R2)%R ⊆ (S1 ∧ S2)%R.
  Proof. intros H1 H2 τ [??]. tr_unfold. auto. Qed.
  Lemma tr_and_comm R S : (R ∧ S)%R ⊆ (S ∧ R)%R.
  Proof. intros τ [??]. by split. Qed.

  Lemma tr_and_assoc R S T : ((R ∧ S) ∧ T)%R ⊆ (R ∧ (S ∧ T))%R.
  Proof. intros τ [[??]?]. tr_unfold. auto. Qed.
  Lemma tr_and_assoc' R S T : (R ∧ (S ∧ T))%R ⊆ ((R ∧ S) ∧ T)%R.
  Proof. intros τ [?[??]]. tr_unfold. auto. Qed.
  (** A pure conjunct or an existential on the left goes to the Rocq context. *)
  Lemma tr_pure_elim_l (φ : Prop) R S : (φ → R ⊆ S) → (⌜φ⌝ ∧ R)%R ⊆ S.
  Proof. intros H τ [Hφ HR]. by apply H. Qed.
  Lemma tr_exist_elim_l {Y} (R : Y → trProp Λ) S T :
    (∀ y, (R y ∧ S)%R ⊆ T) → (tr_exist Y R ∧ S)%R ⊆ T.
  Proof. intros H τ [[y Hy] HS]. by apply (H y). Qed.

  (** Disjunction. *)
  Lemma tr_or_intro_l R S1 S2 : R ⊆ S1 → R ⊆ (S1 ∨ S2)%R.
  Proof. intros H τ HR. left. by apply H. Qed.
  Lemma tr_or_intro_r R S1 S2 : R ⊆ S2 → R ⊆ (S1 ∨ S2)%R.
  Proof. intros H τ HR. right. by apply H. Qed.
  Lemma tr_or_elim R1 R2 S : R1 ⊆ S → R2 ⊆ S → (R1 ∨ R2)%R ⊆ S.
  Proof. intros H1 H2 τ [?|?]; [by apply H1|by apply H2]. Qed.
  Lemma tr_or_mono R1 R2 S1 S2 : R1 ⊆ S1 → R2 ⊆ S2 → (R1 ∨ R2)%R ⊆ (S1 ∨ S2)%R.
  Proof. intros H1 H2 τ [?|?]; [left; by apply H1|right; by apply H2]. Qed.

  Lemma tr_and_or_distr R1 R2 S : ((R1 ∨ R2) ∧ S)%R ⊆ ((R1 ∧ S) ∨ (R2 ∧ S))%R.
  Proof. intros τ [[?|?] ?]; [left|right]; tr_unfold; auto. Qed.

  (** Implication: the antecedent joins the hypotheses. *)
  Lemma tr_impl_intro R A S : (R ∧ A)%R ⊆ S → R ⊆ (A → S)%R.
  Proof. intros H τ HR HA. by apply H. Qed.
  Lemma tr_impl_elim A S : ((A → S) ∧ A)%R ⊆ S.
  Proof. intros τ [HAS HA]. by apply HAS. Qed.
  Lemma tr_impl_mono A A' S S' : A' ⊆ A → S ⊆ S' → (A → S)%R ⊆ (A' → S')%R.
  Proof. intros HA HS τ HAS HA'. by apply HS, HAS, HA. Qed.

  (** Quantifiers. *)
  Lemma tr_forall_intro {Y} R (S : Y → trProp Λ) : (∀ y, R ⊆ S y) → R ⊆ tr_forall Y S.
  Proof. intros H τ HR y. by apply H. Qed.
  Lemma tr_forall_elim {Y} (S : Y → trProp Λ) y : tr_forall Y S ⊆ S y.
  Proof. intros τ H. apply H. Qed.
  Lemma tr_forall_mono {Y} (R S : Y → trProp Λ) : (∀ y, R y ⊆ S y) → tr_forall Y R ⊆ tr_forall Y S.
  Proof. intros H τ HR y. by apply H. Qed.
  Lemma tr_exist_intro {Y} (S : Y → trProp Λ) y : S y ⊆ tr_exist Y S.
  Proof. intros τ H. by exists y. Qed.
  Lemma tr_exist_elim {Y} (R : Y → trProp Λ) S : (∀ y, R y ⊆ S) → tr_exist Y R ⊆ S.
  Proof. intros H τ [y Hy]. by apply (H y). Qed.
  Lemma tr_exist_mono {Y} (R S : Y → trProp Λ) : (∀ y, R y ⊆ S y) → tr_exist Y R ⊆ tr_exist Y S.
  Proof. intros H τ [y Hy]. exists y. by apply H. Qed.

  (** State atoms combine, and are decided by the current configuration. *)
  Lemma tr_state_mono (φ ψ : state Λ → thread_pool Λ → Prop) :
    (∀ σ Θ, φ σ Θ → ψ σ Θ) → tr_state φ ⊆ tr_state ψ.
  Proof. intros H [n τf]. tr_unfold. destruct (τf n) as (((Θ&σ)&?)&?). apply H. Qed.
  Lemma tr_state_and (φ ψ : state Λ → thread_pool Λ → Prop) :
    (tr_state φ ∧ tr_state ψ)%R ⊆ tr_state (λ σ Θ, φ σ Θ ∧ ψ σ Θ).
  Proof. intros [n τf]. tr_unfold. by destruct (τf n) as (((Θ&σ)&?)&?). Qed.
  Lemma tr_and_state (φ ψ : state Λ → thread_pool Λ → Prop) :
    tr_state (λ σ Θ, φ σ Θ ∧ ψ σ Θ) ⊆ (tr_state φ ∧ tr_state ψ)%R.
  Proof. intros [n τf]. tr_unfold. by destruct (τf n) as (((Θ&σ)&?)&?). Qed.
  Lemma tr_state_pure (φ : state Λ → thread_pool Λ → Prop) (ψ : Prop) :
    (∀ σ Θ, φ σ Θ → ψ) → tr_state φ ⊆ (⌜ψ⌝)%R.
  Proof. intros H [n τf]. tr_unfold. destruct (τf n) as (((Θ&σ)&?)&?). apply H. Qed.
  Lemma tr_pure_state (ψ : Prop) (φ : state Λ → thread_pool Λ → Prop) :
    (ψ → ∀ σ Θ, φ σ Θ) → (⌜ψ⌝)%R ⊆ tr_state φ.
  Proof. intros H [n τf]. tr_unfold. destruct (τf n) as (((Θ&σ)&?)&?). intros Hψ. by apply H. Qed.

  (** Next. *)
  Lemma tr_next_mono R S : R ⊆ S → (○ R)%R ⊆ (○ S)%R.
  Proof. intros H τ. apply H. Qed.
End tr_rules.

(** ** The laws of LTL

    Stated as entailments, so they compose by [etrans]. *)
Section tr_laws.
  Context {Λ : language}.
  Implicit Types R S X : trProp Λ.

  (** Always: reflexive, transitive, monotone, distributes over [∧], and is the greatest
      fixpoint of [R ∧ ○ -] ([tr_always_coind]). *)
  Lemma tr_always_elim R : (□ R)%R ⊆ R.
  Proof. intros [n τf]. tr_unfold. intros H. apply H. lia. Qed.
  Lemma tr_always_next R : (□ R)%R ⊆ (○ □ R)%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm. apply H. lia. Qed.
  Lemma tr_always_idemp R : (□ R)%R ⊆ (□ □ R)%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm m' Hm'. apply H. lia. Qed.
  Lemma tr_always_mono R S : R ⊆ S → (□ R)%R ⊆ (□ S)%R.
  Proof. intros HRS [n τf]. tr_unfold. intros H m Hm. apply HRS, H. lia. Qed.
  Lemma tr_always_and R S : (□ (R ∧ S))%R ⊆ (□ R ∧ □ S)%R.
  Proof. intros [n τf]. tr_unfold. intros H. split; intros m Hm; by apply H. Qed.
  Lemma tr_and_always R S : (□ R ∧ □ S)%R ⊆ (□ (R ∧ S))%R.
  Proof. intros [n τf]. tr_unfold. intros [H1 H2] m Hm. auto. Qed.
  Lemma tr_always_impl R S : (□ (R → S) ∧ □ R)%R ⊆ (□ S)%R.
  Proof. intros [n τf]. tr_unfold. intros [H1 H2] m Hm. auto. Qed.
  Lemma tr_always_coind R X : X ⊆ (R ∧ ○ X)%R → X ⊆ (□ R)%R.
  Proof.
    intros HX [n τf]. tr_unfold. intros Hx m Hm.
    assert (∀ d n', X (n', τf) → R (n' + d, τf)) as Hd.
    { induction d as [|d IH]; intros n' Hn'.
      - rewrite Nat.add_0_r. by apply HX.
      - destruct (HX (n', τf) Hn') as [_ Hnext]. replace (n' + S d) with (S n' + d) by lia.
        apply IH. exact Hnext. }
    replace m with (n + (m - n)) by lia. by apply Hd.
  Qed.

  (** Until: the least fixpoint of [S ∨ (R ∧ ○ -)] ([tr_until_now], [tr_until_step],
      [tr_until_ind]), monotone, and stronger than finally. *)
  Lemma tr_until_now R S : S ⊆ tr_until R S.
  Proof. intros [n τf]. tr_unfold. intros H. exists n. split_and!; [lia|done|lia]. Qed.
  Lemma tr_until_step R S : (R ∧ ○ tr_until R S)%R ⊆ tr_until R S.
  Proof.
    intros [n τf]. tr_unfold. intros [HR (m & Hm & HS & HRs)]. exists m. split_and!; [lia|done|].
    intros l Hl. destruct (decide (l = n)) as [->|]; [done|apply HRs; lia].
  Qed.
  Lemma tr_until_unfold R S : tr_until R S ⊆ (S ∨ (R ∧ ○ tr_until R S))%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & HS & HRs).
    destruct (decide (m = n)) as [->|]; first by left.
    right. split; first (apply HRs; lia). exists m. split_and!; [lia|done|]. intros l Hl. apply HRs. lia.
  Qed.
  Lemma tr_until_ind R S X : S ⊆ X → (R ∧ ○ X)%R ⊆ X → tr_until R S ⊆ X.
  Proof.
    intros HS HR [n τf]. tr_unfold. intros (m & Hm & HSm & HRs).
    assert (∀ d n', n' + d = m → (∀ l, n' ≤ l < m → R (l, τf)) → X (n', τf)) as Hd.
    { induction d as [|d IH]; intros n' Hd HRs'.
      - rewrite Nat.add_0_r in Hd. subst. by apply HS.
      - apply HR. split; first (apply HRs'; lia).
        change (X (Datatypes.S n', τf)). apply IH; first lia. intros l Hl. apply HRs'. lia. }
    apply (Hd (m - n) n); [lia|exact HRs].
  Qed.
  Lemma tr_until_mono R R' S S' : R ⊆ R' → S ⊆ S' → tr_until R S ⊆ tr_until R' S'.
  Proof.
    intros HR HS [n τf]. tr_unfold. intros (m & Hm & HSm & HRs). exists m. split_and!; [lia|by apply HS|].
    intros l Hl. apply HR, HRs. lia.
  Qed.
  Lemma tr_until_finally R S : tr_until R S ⊆ (◇ S)%R.
  Proof. apply tr_until_mono; [by intros ?|done]. Qed.

  (** Finally. *)
  Lemma tr_finally_intro S : S ⊆ (◇ S)%R.
  Proof. apply tr_until_now. Qed.
  Lemma tr_finally_mono S S' : S ⊆ S' → (◇ S)%R ⊆ (◇ S')%R.
  Proof. intros HS. by apply tr_until_mono. Qed.
  Lemma tr_finally_idemp S : (◇ ◇ S)%R ⊆ (◇ S)%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & (m' & Hm' & HS & _) & _). exists m'. split_and!; [lia|done|done].
  Qed.
  Lemma tr_finally_or S S' : (◇ (S ∨ S'))%R ⊆ (◇ S ∨ ◇ S')%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & [HS|HS] & _); [left|right]; exists m; split_and!; done.
  Qed.
  Lemma tr_always_finally_resp R S : (□ (R → ◇ S) ∧ ◇ R)%R ⊆ (◇ S)%R.
  Proof.
    intros [n τf]. tr_unfold. intros [H (m & Hm & HR & _)].
    destruct (H m Hm HR) as (m' & Hm' & HS & _). exists m'. split_and!; [lia|done|done].
  Qed.
  Lemma tr_always_finally_mono R S : R ⊆ S → (□ ◇ R)%R ⊆ (□ ◇ S)%R.
  Proof. intros HRS. by apply tr_always_mono, tr_finally_mono. Qed.

  (** Duality: [□] and [◇] are each other's negation (classically). *)
  Lemma tr_not_finally R : (□ (R → ⌜False⌝))%R ⊆ (◇ R → ⌜False⌝)%R.
  Proof. intros [n τf]. tr_unfold. intros H (m & Hm & HR & _). by apply (H m). Qed.
  Lemma tr_not_always R : (◇ R → ⌜False⌝)%R ⊆ (□ (R → ⌜False⌝))%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm HR. apply H. exists m. split_and!; done. Qed.
  Lemma tr_not_always_finally R : (□ R → ⌜False⌝)%R ⊆ (◇ (R → ⌜False⌝))%R.
  Proof.
    intros [n τf]. tr_unfold. intros H.
    destruct (Classical_Prop.classic (∃ m, n ≤ m ∧ ¬ R (m, τf))) as [(m & Hm & HR)|Hno].
    - exists m. split_and!; done.
    - exfalso. apply H. intros m Hm. destruct (Classical_Prop.classic (R (m, τf))); [done|].
      exfalso. apply Hno. by exists m.
  Qed.
End tr_laws.

(** ** Fixpoints of trace predicates *)
Section tr_fixpoint_rules.
  Context {Λ : language}.
  Implicit Types R : trProp Λ.
  Implicit Types Φ : trProp Λ → trProp Λ.

  Lemma tr_gfp_coind Φ R : (∀ τ, R τ → Φ R τ) → ∀ τ, R τ → tr_gfp Φ τ.
  Proof. intros HR τ Hτ. by exists R. Qed.
  Lemma tr_gfp_unfold_l Φ : tr_mono Φ → ∀ τ, tr_gfp Φ τ → Φ (tr_gfp Φ) τ.
  Proof.
    intros Hm τ (R & HR & Hτ). eapply Hm; last by apply HR. intros τ' Hτ'. by exists R.
  Qed.
  Lemma tr_gfp_unfold_r Φ : tr_mono Φ → ∀ τ, Φ (tr_gfp Φ) τ → tr_gfp Φ τ.
  Proof.
    intros Hm τ Hτ. exists (Φ (tr_gfp Φ)). split; last done.
    intros τ' Hτ'. eapply Hm; [|exact Hτ']. by apply tr_gfp_unfold_l.
  Qed.

  Lemma tr_lfp_ind Φ R : (∀ τ, Φ R τ → R τ) → ∀ τ, tr_lfp Φ τ → R τ.
  Proof. intros HR τ H. by apply H. Qed.
  Lemma tr_lfp_unfold_r Φ : tr_mono Φ → ∀ τ, Φ (tr_lfp Φ) τ → tr_lfp Φ τ.
  Proof. intros Hm τ Hτ R HR. apply HR. eapply Hm; [|exact Hτ]. intros τ' H'. by apply H'. Qed.
  Lemma tr_lfp_unfold_l Φ : tr_mono Φ → ∀ τ, tr_lfp Φ τ → Φ (tr_lfp Φ) τ.
  Proof.
    intros Hm τ H. apply H. intros τ' H'. eapply Hm; [|exact H']. intros τ'' H''.
    by apply tr_lfp_unfold_r.
  Qed.
End tr_fixpoint_rules.
