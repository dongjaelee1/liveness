From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.algebra Require Import ordinal_wfocm.
From liris.base_logic Require Export mupd oinv.

(** All Local Definitions are only for internal uses and users should not need them. *)
(** ** Obl predicates. *)
Local Definition oblP_id_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  oblG_elem k.
Local Definition oblP_id_aux : seal (@oblP_id_def). Proof. by eexists. Qed.
Definition oblP_id := oblP_id_aux.(unseal).
Local Definition oblP_id_unseal :
  @oblP_id = @oblP_id_def := oblP_id_aux.(seal_eq).
Global Arguments oblP_id {SI Σ _}.

Local Definition oblP_assigned_def `{SI : indexT} `{@mupdGS SI Σ}
  k b q : iProp Σ :=
  oblP_id k ∗ oblG_assigned k b  (q/2 + q/2/2)%Qp.
Local Definition oblP_assigned_aux : seal (@oblP_assigned_def). Proof. by eexists. Qed.
Definition oblP_assigned := oblP_assigned_aux.(unseal).
Local Definition oblP_assigned_unseal :
  @oblP_assigned = @oblP_assigned_def := oblP_assigned_aux.(seal_eq).
Global Arguments oblP_assigned {SI Σ _}.

Local Definition oblP_fulfilled_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  oblP_id k ∗ oblG_fulfilled k.
Local Definition oblP_fulfilled_aux : seal (@oblP_fulfilled_def). Proof. by eexists. Qed.
Definition oblP_fulfilled := oblP_fulfilled_aux.(unseal).
Local Definition oblP_fulfilled_unseal :
  @oblP_fulfilled = @oblP_fulfilled_def := oblP_fulfilled_aux.(seal_eq).
Global Arguments oblP_fulfilled {SI Σ _}.

Local Definition oblP_fuel_val `{SI : indexT} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  oblP_id k ∗ oblG_fuel k α.

Local Definition oblP_fuel_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ μ : iProp Σ :=
  oblP_fuel_val k (measure (ℓ, 1) ((1 ⊕ ▽) × μ)%M).
Local Definition oblP_fuel_aux : seal (@oblP_fuel_def). Proof. by eexists. Qed.
Definition oblP_fuel := oblP_fuel_aux.(unseal).
Local Definition oblP_fuel_unseal :
  @oblP_fuel = @oblP_fuel_def := oblP_fuel_aux.(seal_eq).
Global Arguments oblP_fuel {SI Σ _ _}.

Local Definition oblP_variant_def `{SI : indexT} `{@mupdGS SI Σ}
  k (P Q R : iProp Σ) : iProp Σ :=
  ((oblP_assigned k false (1/2)%Qp ∗ P) ∨
     (oblP_assigned k true (1/2)%Qp ∗ Q) ∨
     (oblP_fulfilled k ∗ R))%I.
Local Definition oblP_variant_aux : seal (@oblP_variant_def). Proof. by eexists. Qed.
Definition oblP_variant := oblP_variant_aux.(unseal).
Local Definition oblP_variant_unseal :
  @oblP_variant = @oblP_variant_def := oblP_variant_aux.(seal_eq).
Global Arguments oblP_variant {SI Σ _}.

Local Definition oblP_inv_def `{SI : indexT} `{@mupdGS SI Σ}
  N k (P Q R : iProp Σ) : iProp Σ :=
  oblP_id k ∗ oblG_inv N k ((1/2)/2 + (1/2)/2/2)%Qp P Q R.
Local Definition oblP_inv_aux : seal (@oblP_inv_def). Proof. by eexists. Qed.
Definition oblP_inv := oblP_inv_aux.(unseal).
Local Definition oblP_inv_unseal :
  @oblP_inv = @oblP_inv_def := oblP_inv_aux.(seal_eq).
Global Arguments oblP_inv {SI Σ _}.

(** ** Witness predicates *)
Local Definition witP_bound_val `{SI : indexT} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  oblP_id k ∗ witG_bound k α.

Local Definition witP_layer_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ : iProp Σ :=
  ∃ μ, witP_bound_val k (η (measure (ℓ, 1) μ)).
Local Definition witP_layer_aux : seal (@witP_layer_def). Proof. by eexists. Qed.
Definition witP_layer := witP_layer_aux.(unseal).
Local Definition witP_layer_unseal :
  @witP_layer = @witP_layer_def := witP_layer_aux.(seal_eq).
Global Arguments witP_layer {SI Σ _ _}.

Local Definition witP_cred_def `{SI : indexT} `{@mupdGS SI Σ}
  k a : iProp Σ :=
  oblP_id k ∗ witG_witness k a.
Local Definition witP_cred_aux : seal (@witP_cred_def). Proof. by eexists. Qed.
Definition witP_cred := witP_cred_aux.(unseal).
Local Definition witP_cred_unseal :
  @witP_cred = @witP_cred_def := witP_cred_aux.(seal_eq).
Global Arguments witP_cred {SI Σ _}.

(** ** Obligation group predicates *)
Local Definition ogP_bound `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  g ℓ μ : iProp Σ :=
  ogroupG_bound g (measure (ℓ, 0) μ).

Local Definition ogP_fuel_val `{SI : indexT} `{@mupdGS SI Σ}
  s α : iProp Σ :=
  ogroupG_fuel s α.

Local Definition ogP_fuel_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  s ℓ μ : iProp Σ :=
  ogP_fuel_val s (measure (ℓ, 0) ((1 ⊕ ▽) × μ)%M).
Local Definition ogP_fuel_aux : seal (@ogP_fuel_def). Proof. by eexists. Qed.
Definition ogP_fuel := ogP_fuel_aux.(unseal).
Local Definition ogP_fuel_unseal :
  @ogP_fuel = @ogP_fuel_def := ogP_fuel_aux.(seal_eq).
Global Arguments ogP_fuel {SI Σ _ _}.

Local Definition ogP_obls_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  i g ℓ (K : oids) : iProp Σ :=
  othreadG_elem i ∗ ogroupG_group i g K ∗ ogroupG_thread i g ∗ (∃ μ, ogP_bound g ℓ μ) ∗
  ([∗ set] k ∈ K, oblP_id k ∗ oblG_owner k i (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns i k (1/2 + 1/2/2)%Qp).
Local Definition ogP_obls_aux : seal (@ogP_obls_def). Proof. by eexists. Qed.
Definition ogP_obls := ogP_obls_aux.(unseal).
Local Definition ogP_obls_unseal :
  @ogP_obls = @ogP_obls_def := ogP_obls_aux.(seal_eq).
Global Arguments ogP_obls {SI Σ _ _}.

(** ** Thread predicates *)
Local Definition thP_groups_def `{SI : indexT} `{@mupdGS SI Σ}
  i G : iProp Σ :=
  othreadG_elem i ∗ othreadG_exec i (1/2)%Qp ∗ ogroupG_thread_auth i G (1/2)%Qp.
Local Definition thP_groups_aux : seal (@thP_groups_def). Proof. by eexists. Qed.
Definition thP_groups := thP_groups_aux.(unseal).
Local Definition thP_groups_unseal :
  @thP_groups = @thP_groups_def := thP_groups_aux.(seal_eq).
Global Arguments thP_groups {SI Σ _}.

Local Definition thP_done_def `{SI : indexT} `{@mupdGS SI Σ}
  i : iProp Σ :=
  othreadG_elem i ∗ othreadG_done i.
Local Definition thP_done_aux : seal (@thP_done_def). Proof. by eexists. Qed.
Definition thP_done := thP_done_aux.(unseal).
Local Definition thP_done_unseal :
  @thP_done = @thP_done_def := thP_done_aux.(seal_eq).
Global Arguments thP_done {SI Σ _}.

(** ** Additional definitions for managing collection of fules for convenient induction *)
Local Definition collect_fuels `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  α (F : gmap ogid (ord.t * measurable_syntax)) : iProp Σ :=
  ([∗ map] s ↦ '(l, m) ∈ F, ogP_fuel_val s ((measure (l, 0) ((1 ⊕ ▽) × m)%M) × α)%ord).

Local Definition embed_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (a : A) (F : gmap ogid (ord.t * measurable_syntax)) : iProp Σ :=
  collect_fuels (measure (0 : ord.t, 0) (⟪wf_ltA, a⟫)%M) F.
Local Definition embed_fuels_aux : seal (@embed_fuels_def). Proof. by eexists. Qed.
Definition embed_fuels := embed_fuels_aux.(unseal).
Local Definition embed_fuels_unseal :
  @embed_fuels = @embed_fuels_def := embed_fuels_aux.(seal_eq).
Global Arguments embed_fuels {SI Σ _ _ A ltA}.

Local Definition wit_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ α (F : gmap ogid (ord.t * measurable_syntax)) : iProp Σ :=
  ∃ μ, ⌜ (α <= η (measure (ℓ, 1) μ))%ord ⌝ ∗ witP_bound_val k α ∗ collect_fuels α F.
Local Definition wit_fuels_aux : seal (@wit_fuels_def). Proof. by eexists. Qed.
Definition wit_fuels := wit_fuels_aux.(unseal).
Local Definition wit_fuels_unseal :
  @wit_fuels = @wit_fuels_def := wit_fuels_aux.(seal_eq).
Global Arguments wit_fuels {SI Σ _ _}.

Ltac unfold_opreds :=
  try rewrite !wit_fuels_unseal /wit_fuels_def;
  try rewrite !embed_fuels_unseal /embed_fuels_def;
  try rewrite /collect_fuels;
  try rewrite !thP_done_unseal /thP_done_def;
  try rewrite !thP_groups_unseal /thP_groups_def;
  try rewrite !ogP_obls_unseal /ogP_obls_def;
  try rewrite !ogP_fuel_unseal /ogP_fuel_def;
  try rewrite /ogP_fuel_val;
  try rewrite /ogP_bound;
  try rewrite !witP_cred_unseal /witP_cred_def;
  try rewrite !witP_layer_unseal /witP_layer_def;
  try rewrite /witP_bound_val;
  try rewrite !oblP_variant_unseal /oblP_variant_def;
  try rewrite !oblP_inv_unseal /oblP_inv_def;
  try rewrite !oblP_fuel_unseal /oblP_fuel_def;
  try rewrite /oblP_fuel_val;
  try rewrite !oblP_fulfilled_unseal /oblP_fulfilled_def;
  try rewrite !oblP_assigned_unseal /oblP_assigned_def;
  try rewrite !oblP_id_unseal /oblP_id_def.

Ltac unfold_oblP_fuel :=
  try rewrite !oblP_fuel_unseal /oblP_fuel_def.
Ltac unfold_ogP_fuel :=
  try rewrite !ogP_fuel_unseal /ogP_fuel_def.

Section preds.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Section liveness_preds.

    (** ** Instances *)
    Global Instance oblP_id_persistent k : Persistent (oblP_id k).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_fulfilled_persistent k : Persistent (oblP_fulfilled k).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_inv_persistent N k P Q R : Persistent (oblP_inv N k P Q R).
    Proof. unfold_opreds. apply _. Qed.

    Local Instance witP_bound_val_persistent k α : Persistent (witP_bound_val k α).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance witP_layer_persistent k ℓ : Persistent (witP_layer k ℓ).
    Proof. unfold_opreds. apply _. Qed.

    Local Instance ogP_bound_persistent g ℓ μ : Persistent (ogP_bound g ℓ μ).
    Proof. unfold_opreds. apply _. Qed.

    Global Instance thP_done_persistent i : Persistent (thP_done i).
    Proof. unfold_opreds. apply _. Qed.

    Local Instance collect_fuels_empty_persistent α : Persistent (collect_fuels α ∅).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance embed_fuels_empty_persistent {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a :
      Persistent (embed_fuels wf_ltA a ∅).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance wit_fuels_empty_persistent k ℓ α : Persistent (wit_fuels k ℓ α ∅).
    Proof. unfold_opreds. apply _. Qed.

    Global Instance oblP_id_timeless k : Timeless (oblP_id k).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_assigned_timeless k b q : Timeless (oblP_assigned k b q).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_fulfilled_timeless k : Timeless (oblP_fulfilled k).
    Proof. unfold_opreds. apply _. Qed.
    Local Instance oblP_fuel_val_timeless k α : Timeless (oblP_fuel_val k α).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_fuel_timeless k ℓ μ : Timeless (oblP_fuel k ℓ μ).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance oblP_variant_timeless k P Q R :
      Timeless P → Timeless Q → Timeless R → Timeless (oblP_variant k P Q R).
    Proof. intros. unfold_opreds. apply _. Qed.

    Local Instance witP_bound_val_timeless k α : Timeless (witP_bound_val k α).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance witP_layer_timeless k ℓ : Timeless (witP_layer k ℓ).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance witP_cred_timeless k a : Timeless (witP_cred k a).
    Proof. unfold_opreds. apply _. Qed.

    Local Instance ogP_bound_timeless g ℓ μ : Timeless (ogP_bound g ℓ μ).
    Proof. unfold_opreds. apply _. Qed.
    Local Instance ogP_fuel_val_timeless g α : Timeless (ogP_fuel_val g α).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance ogP_fuel_timeless g ℓ μ : Timeless (ogP_fuel g ℓ μ).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance ogP_obls_timeless i g ℓ K : Timeless (ogP_obls i g ℓ K).
    Proof. unfold_opreds. apply _. Qed.

    Global Instance thP_groups_timeless i G : Timeless (thP_groups i G).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_done_timeless i : Timeless (thP_done i).
    Proof. unfold_opreds. apply _. Qed.

    Local Instance collect_fuels_timeless α F : Timeless (collect_fuels α F).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance embed_fuels_empty_timeless {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a :
      Timeless (embed_fuels wf_ltA a ∅).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance wit_fuels_timeless k ℓ α F : Timeless (wit_fuels k ℓ α F).
    Proof. unfold_opreds. apply _. Qed.

    Global Instance oblP_inv_contractive_1 N k Q R : Contractive (λ P, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.
    Global Instance oblP_inv_contractive_2 N k P R : Contractive (λ Q, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.
    Global Instance oblP_inv_contractive_3 N k P Q : Contractive (λ R, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.

    Global Instance oblP_inv_ne_1 N k Q R : NonExpansive (λ P, oblP_inv N k P Q R).
    Proof. apply _. Qed.
    Global Instance oblP_inv_ne_2 N k P R : NonExpansive (λ Q, oblP_inv N k P Q R).
    Proof. apply _. Qed.
    Global Instance oblP_inv_ne_3 N k P Q : NonExpansive (λ R, oblP_inv N k P Q R).
    Proof. apply _. Qed.

    Global Instance oblP_inv_proper_1 N k Q R : Proper (equiv ==> equiv) (λ P, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.
    Global Instance oblP_inv_proper_2 N k P R : Proper (equiv ==> equiv) (λ Q, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.
    Global Instance oblP_inv_proper_3 N k P Q : Proper (equiv ==> equiv) (λ R, oblP_inv N k P Q R).
    Proof.
      unfold_opreds. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.

    Global Instance oblP_assigned_fractional k b : Fractional (oblP_assigned k b).
    Proof.
      rewrite !oblP_assigned_unseal /oblP_assigned_def. intros p q. iSplit.
      - iIntros "(#$& [Gv1 Gv2])". rewrite !Qp.div_add_distr.
        iDestruct "Gv1" as "[Gv1 Gv1']". iDestruct "Gv2" as "[Gv2 Gv2']".
        iCombine "Gv1 Gv2" as "$". iCombine "Gv1' Gv2'" as "$".
      - iIntros "((#$& [Gv1 Gv2])& _& [Gv3 Gv4])". rewrite !Qp.div_add_distr.
        iCombine "Gv1 Gv3" as "Gv1". iSplitL "Gv1"; iFrame. iSplitR "Gv4"; iFrame.
    Qed.
    Global Instance oblP_assigned_as_fractional k b q : AsFractional (oblP_assigned k b q) (oblP_assigned k b) q.
    Proof. split; [auto|apply _]. Qed.

    (** oblP_assigned and oblP_fulfilled rules *)
    Lemma oblP_assigned_agree k b1 b2 q1 q2 :
      oblP_assigned k b1 q1 -∗ oblP_assigned k b2 q2 -∗ ⌜ b1 = b2 ⌝.
    Proof.
      unfold_opreds. iIntros "(#Ge& Gl) (_& Gu)".
      iPoseProof (oblG_assigned_agree with "[$Gl $Gu]") as "%". by destruct H.
    Qed.

    Lemma oblP_assigned_fulfilled_false k b q :
      oblP_assigned k b q -∗ oblP_fulfilled k -∗ False.
    Proof.
      unfold_opreds. iIntros "(#Ge& Gl) (_& #Gu)".
      iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    Qed.

    (** oblP_fuel_val rules *)
    Local Open Scope ord.

    Local Lemma oblP_fuel_val_eq k a0 a1 :
      (a0 == a1) → oblP_fuel_val k a0 = oblP_fuel_val k a1.
    Proof.
      unfold_opreds. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
    Qed.
    Local Lemma oblP_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, oblP_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, oblP_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_val_eq; eauto. Qed.
    Local Lemma oblP_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, oblP_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_val_eq; eauto. Qed.

    Local Lemma oblP_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → oblP_fuel_val k a1 ==∗ oblP_fuel_val k a0.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
    Qed.
    Local Lemma oblP_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_mon.
    Qed.
    Local Lemma oblP_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_mon.
    Qed.

    Local Lemma oblP_fuel_val_add k a0 a1 :
      oblP_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
    Proof.
      unfold_opreds. rewrite oblG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Local Lemma oblP_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, oblP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblP_fuel_val_add.
    Qed.
    Local Lemma oblP_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, oblP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblP_fuel_val_add.
    Qed.

    Local Lemma oblP_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → oblP_fuel_val k a2 ==∗ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(#Be& P)".
      iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Local Lemma oblP_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, oblP_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oblP_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply oblP_fuel_val_add_list.
    Qed.
    Local Lemma oblP_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, oblP_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oblP_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply oblP_fuel_val_add_set.
    Qed.

    Local Lemma oblP_fuel_val_lt k a0 a1 :
      a0 < a1 →
      oblP_fuel_val k a1 ⊢ |==> oblP_fuel_val k a0 ∗ oblP_fuel_val k Ord.one.
    Proof.
      unfold_opreds. iIntros (Hlt) "(#Be& P)".
      iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Local Lemma oblP_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_lt.
    Qed.
    Local Lemma oblP_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_lt.
    Qed.

    Local Lemma oblP_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      oblP_fuel_val k (b × a1)%ord ⊢ |==> oblP_fuel_val k (b × a0) ∗ oblP_fuel_val k b.
    Proof.
      unfold_opreds. intros LT. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (oblG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Local Lemma oblP_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, oblP_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, oblP_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_val_mult. auto.
    Qed.
    Local Lemma oblP_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, oblP_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, oblP_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_val_mult. auto.
    Qed.

    Local Lemma oblP_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      oblP_fuel_val k (b ↑ a1)%ord ⊢ |==> oblP_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_opreds. intros LT Pos. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Local Lemma oblP_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, oblP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_val_expn; auto.
    Qed.
    Local Lemma oblP_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, oblP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_val_expn; auto.
    Qed.

    (** ** oblP_fuel rules *)
    Local Lemma oblP_fuel_unfold k ℓ μ :
      oblP_fuel k ℓ μ = oblP_fuel_val k (measure (ℓ, 1) ((1 ⊕ ▽) × μ)%M).
    Proof. rewrite oblP_fuel_unseal /oblP_fuel_def. auto. Qed.

    Lemma oblP_fuel_layer_eq k ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      oblP_fuel k ℓ1 μ = oblP_fuel k ℓ2 μ.
    Proof.
      unfold_oblP_fuel. intros.
      apply oblP_fuel_val_eq. apply measure_layer_eq. split; auto.
    Qed.
    Lemma oblP_fuel_layer_eq_list K ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_layer_eq; eauto. Qed.
    Lemma oblP_fuel_layer_eq_set K ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_layer_eq; eauto. Qed.

    Lemma oblP_fuel_eq k ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M == measure (ℓ, 1) (μ2)%M) →
      oblP_fuel k ℓ μ1 = oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. intros. rewrite !measure_mult.
      apply oblP_fuel_val_eq. rewrite !H. done.
    Qed.
    Lemma oblP_fuel_eq_list K ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M == measure (ℓ, 1) (μ2)%M) →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.
    Lemma oblP_fuel_eq_set K ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M == measure (ℓ, 1) (μ2)%M) →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.

    Lemma oblP_fuel_mon_gen k ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 1) (μ1)%M <= measure (ℓ2, 1) (μ2)%M)%ord →
      oblP_fuel k ℓ2 μ2 ==∗ oblP_fuel k ℓ1 μ1.
    Proof.
      unfold_oblP_fuel. intros. apply oblP_fuel_val_mon.
      rewrite !measure_mult. etrans; first eapply Jacobsthal.le_mult_r; eauto.
      eapply Jacobsthal.le_mult_l. apply measure_layer_le_proper. destruct H.
      - left. split; auto.
      - right. econstructor 1. auto.
    Qed.
    Lemma oblP_fuel_mon_gen_list K ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 1) (μ1)%M <= measure (ℓ2, 1) (μ2)%M)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LL LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
    Qed.
    Lemma oblP_fuel_mon_gen_set K ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 1) (μ1)%M <= measure (ℓ2, 1) (μ2)%M)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LL LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
    Qed.

    Lemma oblP_fuel_mon k ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M <= measure (ℓ, 1) (μ2)%M)%ord →
      oblP_fuel k ℓ μ2 ==∗ oblP_fuel k ℓ μ1.
    Proof. intros. apply oblP_fuel_mon_gen; auto. left; reflexivity. Qed.
    Lemma oblP_fuel_mon_list K ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M <= measure (ℓ, 1) (μ2)%M)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon.
    Qed.
    Lemma oblP_fuel_mon_set K ℓ μ1 μ2 :
      (measure (ℓ, 1) (μ1)%M <= measure (ℓ, 1) (μ2)%M)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon.
    Qed.

    Lemma oblP_fuel_mon_split k ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 1) (μ1)%M ⊕ measure (ℓ, 1) (μ2)%M) <= measure (ℓ, 1) (μ3)%M)%ord →
      oblP_fuel k ℓ μ3 ==∗ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. intros. apply oblP_fuel_val_mon_split.
      rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_dist.
      apply Jacobsthal.le_mult_r. auto.
    Qed.
    Lemma oblP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 1) (μ1)%M ⊕ measure (ℓ, 1) (μ2)%M) <= measure (ℓ, 1) (μ3)%M)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply oblP_fuel_mon_split; auto.
    Qed.
    Lemma oblP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 1) (μ1)%M ⊕ measure (ℓ, 1) (μ2)%M) <= measure (ℓ, 1) (μ3)%M)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply oblP_fuel_mon_split; auto.
    Qed.

    Lemma oblP_fuel_lt k ℓ μ1 μ2 :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      oblP_fuel k ℓ μ2 ⊢ |==> oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ (1)%M.
    Proof.
      unfold_oblP_fuel. intros. rewrite -oblP_fuel_val_add.
      iIntros "H". iApply oblP_fuel_val_mon. 2: iFrame.
      rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_dist.
      apply Jacobsthal.le_mult_r. rewrite measure_nat. rewrite Hessenberg.add_comm -ord_S_add.
      apply Ord.S_supremum; auto.
    Qed.
    Lemma oblP_fuel_lt_list K ℓ μ1 μ2 :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_lt.
    Qed.
    Lemma oblP_fuel_lt_set K ℓ μ1 μ2 :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_lt.
    Qed.

    (** measurable syntax rules. *)
    Lemma oblP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ oblP_fuel k ℓ 1.
    Proof.
      intros. apply oblP_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma oblP_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_embed. auto.
    Qed.
    Lemma oblP_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_embed. auto.
    Qed.

    Lemma oblP_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      oblP_fuel k ℓ (ℵ)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ oblP_fuel k ℓ 1.
    Proof.
      intros. apply oblP_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma oblP_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, oblP_fuel k ℓ (ℵ)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_large.
    Qed.
    Lemma oblP_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, oblP_fuel k ℓ (ℵ)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_large.
    Qed.

    Lemma oblP_fuel_add k ℓ μ1 μ2 :
      oblP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. rewrite (measure_mult _ _ (μ1 ⊕ μ2)%M) (measure_add _ μ1 μ2).
      etrans.
      { erewrite oblP_fuel_val_eq. 2: apply ClassicJacobsthal.mult_dist. reflexivity. }
      rewrite -!measure_mult. apply oblP_fuel_val_add.
    Qed.
    Lemma oblP_fuel_add_list K ℓ μ1 μ2 :
      ([∗ list] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblP_fuel_add.
    Qed.
    Lemma oblP_fuel_add_set K ℓ μ1 μ2 :
      ([∗ set] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblP_fuel_add.
    Qed.

    Lemma oblP_fuel_mult k ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      oblP_fuel k ℓ (s × μ2)%M ⊢ |==> oblP_fuel k ℓ (s × μ1)%M ∗ oblP_fuel k ℓ s.
    Proof.
      unfold_oblP_fuel. intros. iIntros "H".
      rewrite (oblP_fuel_val_eq _ (measure (ℓ, 1) ((1 ⊕ ▽) × s × μ2)%M) (measure (ℓ, 1) (((1 ⊕ ▽) × s) × μ2)%M)); cycle 1.
      { rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_assoc. done. }
      rewrite !measure_mult. iMod (oblP_fuel_val_mult with "H") as "[H $]". 1: eauto.
      erewrite oblP_fuel_val_eq. 1: by iFrame.
      rewrite -ClassicJacobsthal.mult_assoc. done.
    Qed.
    Lemma oblP_fuel_mult_list K ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_mult. auto.
    Qed.
    Lemma oblP_fuel_mult_set K ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_mult. auto.
    Qed.

    Lemma oblP_fuel_expn k ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      (Ord.O < measure (ℓ, 1) s)%ord →
      oblP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> oblP_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_oblP_fuel. intros LT Pos. rewrite !measure_mult !measure_expn.
      iIntros "H". iPoseProof (oblP_fuel_val_mon with "H") as "$".
      apply Jacobsthal.le_mult_r. rewrite -Jacobsthal.expn_S. 2: auto.
      eapply Jacobsthal.le_expn_r. apply Ord.S_supremum; auto.
    Qed.
    Lemma oblP_fuel_expn_list K ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      (Ord.O < measure (ℓ, 1) s)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_expn; auto.
    Qed.
    Lemma oblP_fuel_expn_set K ℓ μ1 μ2 s :
      (measure (ℓ, 1) μ1 < measure (ℓ, 1) μ2)%ord →
      (Ord.O < measure (ℓ, 1) s)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_expn; auto.
    Qed.

    Lemma oblP_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      oblP_fuel k ℓ2 1 ⊢ |==> oblP_fuel k ℓ1 μ.
    Proof.
      unfold_oblP_fuel. iIntros (LT) "H".
      iPoseProof (oblP_fuel_val_mon with "H") as "$".
      rewrite (measure_mult (ℓ2, 1)) measure_nat Jacobsthal.mult_1_r.
      etrans; first eapply η_mono. etrans; first eapply (measure_extend _ (ℓ2, 1)).
      { econstructor 1. auto. }
      rewrite measure_add measure_nat. apply Hessenberg.add_base_r.
    Qed.
    Lemma oblP_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, oblP_fuel k ℓ2 1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply oblP_fuel_extend; eauto.
    Qed.
    Lemma oblP_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, oblP_fuel k ℓ2 (1)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply oblP_fuel_extend; eauto.
    Qed.

    (** witP_bound_val rules *)
    Local Lemma witP_bound_val_mon k a0 a1 :
      (a0 <= a1)%ord → witP_bound_val k a0 ==∗ witP_bound_val k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_bound_mon.
    Qed.
    Local Lemma witP_bound_val_compare k a0 a1 :
      witP_bound_val k a0 -∗ witP_cred k a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_opreds. iIntros "(P& Be) (_& Cred)". iApply (witG_compare with "[$]").
    Qed.
    Local Lemma witP_bound_val_spend_gen k a0 a1 :
      witP_bound_val k a0 -∗ witP_cred k a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ witP_bound_val k a2.
    Proof.
      unfold_opreds. iIntros "($& Ow) (_& Oc)". iApply (witG_witness_spend_gen with "[$]").
    Qed.
    Local Lemma witP_bound_val_spend k a0 a1 :
      (Ord.O < a1)%ord →
      witP_bound_val k a0 -∗ witP_cred k a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ witP_bound_val k a2.
    Proof.
      unfold_opreds. iIntros (LT) "($& Ow) (_& Oc)". iApply (witG_witness_spend with "[$]"). done.
    Qed.
    Local Lemma witP_bound_val_spend_one k a :
      witP_bound_val k a -∗ witP_cred k Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ witP_bound_val k a0.
    Proof.
      iIntros "Ow Oc". iApply (witP_bound_val_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** witP_layer rules *)
    Local Lemma witP_layer_witP_bound_val k ℓ :
      witP_layer k ℓ -∗ ∃ μ, witP_bound_val k (η (measure (ℓ, 1) μ)).
    Proof. unfold_opreds. eauto. Qed.

    (** witP_cred rules *)
    Lemma witP_cred_eq k a0 a1 :
      (a0 == a1) → witP_cred k a1 = witP_cred k a0.
    Proof.
      unfold_opreds. intros. rewrite (witG_witness_eq k a0 a1); auto.
    Qed.
    Lemma witP_cred_mon k a0 a1 :
      (a0 <= a1) → witP_cred k a1 ==∗ witP_cred k a0.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_witness_mon.
    Qed.
    Lemma witP_cred_split k a0 a1 :
      witP_cred k (a0 ⊕ a1)%ord ⊣⊢ witP_cred k a0 ∗ witP_cred k a1.
    Proof.
      unfold_opreds. rewrite witG_witness_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma witP_cred_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord →
      witP_cred k a2 ==∗ witP_cred k a0 ∗ witP_cred k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(#Be& P)".
      iMod (witG_witness_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma witP_cred_lt k a0 a1 :
      (a0 < a1) → witP_cred k a1 ==∗ witP_cred k a0 ∗ witP_cred k Ord.one.
    Proof.
      unfold_opreds. iIntros (Hlt) "(#Be& P)". iFrame "Be".
      iMod (witG_witness_lt with "P") as "[$ (%& %& C)]"; first done. 
      apply ord_lt_one in H. iMod (witG_witness_mon_split with "C") as "[_ $]"; done.
    Qed.

    (** ogP_fuel_val rules *)
    Local Open Scope ord.

    Local Lemma ogP_fuel_val_eq k a0 a1 :
      (a0 == a1) → ogP_fuel_val k a0 = ogP_fuel_val k a1.
    Proof.
      unfold_opreds. intros. rewrite (ogroupG_fuel_eq k a0 a1); auto.
    Qed.
    Local Lemma ogP_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, ogP_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, ogP_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite ogP_fuel_val_eq; eauto. Qed.
    Local Lemma ogP_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, ogP_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, ogP_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite ogP_fuel_val_eq; eauto. Qed.

    Local Lemma ogP_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → ogP_fuel_val k a1 ==∗ ogP_fuel_val k a0.
    Proof.
      unfold_opreds. iIntros (Hle) "P". iFrame. by iApply ogroupG_fuel_mon.
    Qed.
    Local Lemma ogP_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, ogP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_val_mon.
    Qed.
    Local Lemma ogP_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, ogP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_val_mon.
    Qed.

    Local Lemma ogP_fuel_val_add k a0 a1 :
      ogP_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ ogP_fuel_val k a0 ∗ ogP_fuel_val k a1.
    Proof.
      unfold_opreds. rewrite ogroupG_fuel_split. iSplit.
      - iIntros "(P1& P2)"; iFrame; eauto.
      - iIntros "(P1& P2)"; iFrame.
    Qed.
    Local Lemma ogP_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, ogP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ list] k ∈ K, ogP_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply ogP_fuel_val_add.
    Qed.
    Local Lemma ogP_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, ogP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ set] k ∈ K, ogP_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply ogP_fuel_val_add.
    Qed.

    Local Lemma ogP_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → ogP_fuel_val k a2 ==∗ ogP_fuel_val k a0 ∗ ogP_fuel_val k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "P".
      iMod (ogroupG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Local Lemma ogP_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, ogP_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ list] k ∈ K, ogP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (ogP_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply ogP_fuel_val_add_list.
    Qed.
    Local Lemma ogP_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, ogP_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ set] k ∈ K, ogP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (ogP_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply ogP_fuel_val_add_set.
    Qed.

    Local Lemma ogP_fuel_val_lt k a0 a1 :
      a0 < a1 →
      ogP_fuel_val k a1 ⊢ |==> ogP_fuel_val k a0 ∗ ogP_fuel_val k Ord.one.
    Proof.
      unfold_opreds. iIntros (Hlt) "P".
      iMod (ogroupG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P". apply ord_lt_one in H. iMod (ogroupG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Local Lemma ogP_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, ogP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ list] k ∈ K, ogP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_val_lt.
    Qed.
    Local Lemma ogP_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, ogP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel_val k a0) ∗ ([∗ set] k ∈ K, ogP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_val_lt.
    Qed.

    Local Lemma ogP_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      ogP_fuel_val k (b × a1)%ord ⊢ |==> ogP_fuel_val k (b × a0) ∗ ogP_fuel_val k b.
    Proof.
      unfold_opreds. intros LT. iIntros "Gf".
      apply Ord.S_supremum in LT. iMod (ogroupG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (ogroupG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Local Lemma ogP_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, ogP_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, ogP_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, ogP_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply ogP_fuel_val_mult. auto.
    Qed.
    Local Lemma ogP_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, ogP_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, ogP_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, ogP_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply ogP_fuel_val_mult. auto.
    Qed.

    Local Lemma ogP_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ogP_fuel_val k (b ↑ a1)%ord ⊢ |==> ogP_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_opreds. intros LT Pos. iIntros "Gf".
      apply Ord.S_supremum in LT. iMod (ogroupG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Local Lemma ogP_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, ogP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply ogP_fuel_val_expn; auto.
    Qed.
    Local Lemma ogP_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, ogP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply ogP_fuel_val_expn; auto.
    Qed.

    (** ** ogP_fuel rules *)
    Local Lemma ogP_fuel_unfold k ℓ μ :
      ogP_fuel k ℓ μ = ogP_fuel_val k (measure (ℓ, 0) ((1 ⊕ ▽) × μ)%M).
    Proof. rewrite ogP_fuel_unseal /ogP_fuel_def. auto. Qed.

    Lemma ogP_fuel_layer_eq k ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      ogP_fuel k ℓ1 μ = ogP_fuel k ℓ2 μ.
    Proof.
      unfold_ogP_fuel. intros.
      apply ogP_fuel_val_eq. apply measure_layer_eq. split; auto.
    Qed.
    Lemma ogP_fuel_layer_eq_list K ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      ([∗ list] k ∈ K, ogP_fuel k ℓ1 μ)%I ≡ ([∗ list] k ∈ K, ogP_fuel k ℓ2 μ)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite ogP_fuel_layer_eq; eauto. Qed.
    Lemma ogP_fuel_layer_eq_set K ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2)%ordi →
      ([∗ set] k ∈ K, ogP_fuel k ℓ1 μ)%I ≡ ([∗ set] k ∈ K, ogP_fuel k ℓ2 μ)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite ogP_fuel_layer_eq; eauto. Qed.

    Lemma ogP_fuel_eq k ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M == measure (ℓ, 0) (μ2)%M) →
      ogP_fuel k ℓ μ1 = ogP_fuel k ℓ μ2.
    Proof.
      unfold_ogP_fuel. intros. rewrite !measure_mult.
      apply ogP_fuel_val_eq. rewrite !H. done.
    Qed.
    Lemma ogP_fuel_eq_list K ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M == measure (ℓ, 0) (μ2)%M) →
      ([∗ list] k ∈ K, ogP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, ogP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite ogP_fuel_eq; eauto. Qed.
    Lemma ogP_fuel_eq_set K ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M == measure (ℓ, 0) (μ2)%M) →
      ([∗ set] k ∈ K, ogP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, ogP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite ogP_fuel_eq; eauto. Qed.

    Lemma ogP_fuel_mon_gen k ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 0) (μ1)%M <= measure (ℓ2, 0) (μ2)%M)%ord →
      ogP_fuel k ℓ2 μ2 ==∗ ogP_fuel k ℓ1 μ1.
    Proof.
      unfold_ogP_fuel. intros. apply ogP_fuel_val_mon.
      rewrite !measure_mult. etrans; first eapply Jacobsthal.le_mult_r; eauto.
      eapply Jacobsthal.le_mult_l. apply measure_layer_le_proper. destruct H.
      - left. split; auto.
      - right. econstructor 1. auto.
    Qed.
    Lemma ogP_fuel_mon_gen_list K ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 0) (μ1)%M <= measure (ℓ2, 0) (μ2)%M)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LL LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_mon_gen.
    Qed.
    Lemma ogP_fuel_mon_gen_set K ℓ1 ℓ2 μ1 μ2 :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (measure (ℓ1, 0) (μ1)%M <= measure (ℓ2, 0) (μ2)%M)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LL LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_mon_gen.
    Qed.

    Lemma ogP_fuel_mon k ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M <= measure (ℓ, 0) (μ2)%M)%ord →
      ogP_fuel k ℓ μ2 ==∗ ogP_fuel k ℓ μ1.
    Proof. intros. apply ogP_fuel_mon_gen; auto. left; done. Qed.
    Lemma ogP_fuel_mon_list K ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M <= measure (ℓ, 0) (μ2)%M)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_mon.
    Qed.
    Lemma ogP_fuel_mon_set K ℓ μ1 μ2 :
      (measure (ℓ, 0) (μ1)%M <= measure (ℓ, 0) (μ2)%M)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_mon.
    Qed.

    Lemma ogP_fuel_mon_split k ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 0) (μ1)%M ⊕ measure (ℓ, 0) (μ2)%M) <= measure (ℓ, 0) (μ3)%M)%ord →
      ogP_fuel k ℓ μ3 ==∗ ogP_fuel k ℓ μ1 ∗ ogP_fuel k ℓ μ2.
    Proof.
      unfold_ogP_fuel. intros. apply ogP_fuel_val_mon_split.
      rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_dist.
      apply Jacobsthal.le_mult_r. auto.
    Qed.
    Lemma ogP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 0) (μ1)%M ⊕ measure (ℓ, 0) (μ2)%M) <= measure (ℓ, 0) (μ3)%M)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ μ3) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply ogP_fuel_mon_split; auto.
    Qed.
    Lemma ogP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
      ((measure (ℓ, 0) (μ1)%M ⊕ measure (ℓ, 0) (μ2)%M) <= measure (ℓ, 0) (μ3)%M)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ μ3) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply ogP_fuel_mon_split; auto.
    Qed.

    Lemma ogP_fuel_lt k ℓ μ1 μ2 :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ogP_fuel k ℓ μ2 ⊢ |==> ogP_fuel k ℓ μ1 ∗ ogP_fuel k ℓ (1)%M.
    Proof.
      unfold_ogP_fuel. intros. rewrite -ogP_fuel_val_add.
      iIntros "H". iApply ogP_fuel_val_mon. 2: iFrame.
      rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_dist.
      apply Jacobsthal.le_mult_r. rewrite measure_nat. rewrite Hessenberg.add_comm -ord_S_add.
      apply Ord.S_supremum; auto.
    Qed.
    Lemma ogP_fuel_lt_list K ℓ μ1 μ2 :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_lt.
    Qed.
    Lemma ogP_fuel_lt_set K ℓ μ1 μ2 :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply ogP_fuel_lt.
    Qed.

    (** measurable syntax rules. *)
    Lemma ogP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ogP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> ogP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ ogP_fuel k ℓ 1.
    Proof.
      intros. apply ogP_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma ogP_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply ogP_fuel_embed. auto.
    Qed.
    Lemma ogP_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply ogP_fuel_embed. auto.
    Qed.

    Lemma ogP_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ogP_fuel k ℓ (ℵ)%M ⊢ |==> ogP_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ ogP_fuel k ℓ 1.
    Proof.
      intros. apply ogP_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma ogP_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, ogP_fuel k ℓ (ℵ)%M)
      ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply ogP_fuel_large.
    Qed.
    Lemma ogP_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, ogP_fuel k ℓ (ℵ)%M)
      ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply ogP_fuel_large.
    Qed.

    Lemma ogP_fuel_add k ℓ μ1 μ2 :
      ogP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ ogP_fuel k ℓ μ1 ∗ ogP_fuel k ℓ μ2.
    Proof.
      unfold_ogP_fuel. rewrite (measure_mult _ _ (μ1 ⊕ μ2)%M) (measure_add _ μ1 μ2).
      etrans.
      { erewrite ogP_fuel_val_eq. 2: apply ClassicJacobsthal.mult_dist. reflexivity. }
      rewrite -!measure_mult. apply ogP_fuel_val_add.
    Qed.
    Lemma ogP_fuel_add_list K ℓ μ1 μ2 :
      ([∗ list] k ∈ K, ogP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ list] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply ogP_fuel_add.
    Qed.
    Lemma ogP_fuel_add_set K ℓ μ1 μ2 :
      ([∗ set] k ∈ K, ogP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, ogP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply ogP_fuel_add.
    Qed.

    Lemma ogP_fuel_mult k ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ogP_fuel k ℓ (s × μ2)%M ⊢ |==> ogP_fuel k ℓ (s × μ1)%M ∗ ogP_fuel k ℓ s.
    Proof.
      unfold_ogP_fuel. intros. iIntros "H".
      rewrite (ogP_fuel_val_eq _ (measure (ℓ, 0) ((1 ⊕ ▽) × s × μ2)%M) (measure (ℓ, 0) (((1 ⊕ ▽) × s) × μ2)%M)); cycle 1.
      { rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_assoc. done. }
      rewrite !measure_mult. iMod (ogP_fuel_val_mult with "H") as "[H $]". 1: eauto.
      erewrite ogP_fuel_val_eq. 1: by iFrame.
      rewrite -ClassicJacobsthal.mult_assoc. done.
    Qed.
    Lemma ogP_fuel_mult_list K ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, ogP_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply ogP_fuel_mult. auto.
    Qed.
    Lemma ogP_fuel_mult_set K ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, ogP_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply ogP_fuel_mult. auto.
    Qed.

    Lemma ogP_fuel_expn k ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      (Ord.O < measure (ℓ, 0) s)%ord →
      ogP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> ogP_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_ogP_fuel. intros LT Pos. rewrite !measure_mult !measure_expn.
      iIntros "H". iPoseProof (ogP_fuel_val_mon with "H") as "$".
      apply Jacobsthal.le_mult_r. rewrite -Jacobsthal.expn_S. 2: auto.
      eapply Jacobsthal.le_expn_r. apply Ord.S_supremum; auto.
    Qed.
    Lemma ogP_fuel_expn_list K ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      (Ord.O < measure (ℓ, 0) s)%ord →
      ([∗ list] k ∈ K, ogP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply ogP_fuel_expn; auto.
    Qed.
    Lemma ogP_fuel_expn_set K ℓ μ1 μ2 s :
      (measure (ℓ, 0) μ1 < measure (ℓ, 0) μ2)%ord →
      (Ord.O < measure (ℓ, 0) s)%ord →
      ([∗ set] k ∈ K, ogP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply ogP_fuel_expn; auto.
    Qed.

    Lemma ogP_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ogP_fuel k ℓ2 1 ⊢ |==> ogP_fuel k ℓ1 μ.
    Proof.
      unfold_ogP_fuel. iIntros (LT) "H".
      iPoseProof (ogP_fuel_val_mon with "H") as "$".
      rewrite (measure_mult (ℓ2, 0)) measure_nat Jacobsthal.mult_1_r.
      etrans; first eapply η_mono. etrans; first eapply (measure_extend _ (ℓ2, 0)).
      { econstructor 1. eauto. }
      rewrite measure_add measure_nat. apply Hessenberg.add_base_r.
    Qed.
    Lemma ogP_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, ogP_fuel k ℓ2 1) ⊢ |==> ([∗ list] k ∈ K, ogP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply ogP_fuel_extend; eauto.
    Qed.
    Lemma ogP_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, ogP_fuel k ℓ2 (1)%M) ⊢ |==> ([∗ set] k ∈ K, ogP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply ogP_fuel_extend; eauto.
    Qed.

    (** ** thP_groups rules *)
    Lemma thP_groups_alloc_threads Θ TP :
      Θ ## TP →
      othread TP ∗ ogroup TP
      ⊢ |==> othread (TP ∪ Θ) ∗ ogroup (TP ∪ Θ) ∗ [∗ set] i ∈ Θ, thP_groups i ∅.
    Proof.
      iIntros (Disj) "[T P]".
      iMod (othread_alloc_threads with "T") as "[$ Ts]". 1: auto.
      unfold_opreds.
      iAssert (([∗ set] i ∈ Θ, othreadG_exec i (1 / 2 / 2) ∗ othreadG_obls i ∅)
               ∗ ([∗ set] i ∈ Θ, othreadG_elem i ∗ othreadG_exec i (1 / 2)))%I with "[Ts]" as "[Ts1 Ts2]".
      { iApply big_sepS_sep. iApply (big_sepS_impl with "Ts"). iIntros "!> %% ($& $& [$ $])". }
      iMod (ogroup_alloc_threads with "[$P $Ts1]") as "[$ Ts]". 1: auto.
      iModIntro. iPoseProof (big_sepS_sep with "[$Ts2 $Ts]") as "Ts".
      iApply (big_sepS_impl with "Ts"). iIntros "!> %% (($& $)& $)".
    Qed.

    (** collect_fuels rules *)
    Local Lemma collect_fuels_init α :
      ⊢ collect_fuels α ∅.
    Proof.
      unfold_opreds. rewrite big_sepM_empty. done.
    Qed.

    Local Lemma collect_fuels_add α F f ℓ ν μ :
      (α <= measure (ℓ, 0) ν)%ord →
      collect_fuels α F -∗ ogP_fuel f ℓ (μ × ν)%M ==∗ collect_fuels α (<[f:=(ℓ, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite /collect_fuels.
      unfold_ogP_fuel.
      iMod (ogP_fuel_val_mon _ (measure (ℓ, 0) ((1 ⊕ ▽) × μ)%M × α) with "Gf") as "F".
      { rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_assoc. apply Jacobsthal.le_mult_r. auto. }
      iApply (big_sepM_insert_delete _ _ f). destruct (F !! f) eqn:LUF.
      - iPoseProof (big_sepM_delete _ _ f with "Wfs") as "[_ $]"; eauto.
      - rewrite delete_id; auto. by iFrame.
    Qed.

    Local Lemma collect_fuels_add_map α F (G : gmap ogid (ord.t * measurable_syntax)) ν :
      collect_fuels α F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (α <= measure (l, 0) ν)%ord ⌝ ∗ ogP_fuel g l (m × ν)%M) ==∗
      collect_fuels α (G ∪ F).
    Proof.
      revert α F. induction G using map_ind; intros; iIntros "Wfs Fs".
      { rewrite left_id_L. by iFrame. }
      rewrite big_sepM_insert; last auto.
      rename m into G. destruct x as (l& m). iDestruct "Fs" as "((%Lt& Gf)& Fs)".
      iMod (IHG with "Wfs Fs") as "Wfs".
      replace (<[i:=(l, m)]> G ∪ F) with (<[i:=(l, m)]> (G ∪ F)).
      { iApply (collect_fuels_add with "Wfs Gf"). auto. }
      by rewrite insert_union_l.
    Qed.

    Local Lemma collect_fuels_decr α α0 F :
      (α0 < α)%ord →
      collect_fuels α F ==∗
      (collect_fuels α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, ogP_fuel f l m)).
    Proof.
      rewrite /collect_fuels. iIntros (LT) "Fs".
      rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
      iIntros "!> % % % H". destruct x as (l& m).
      rewrite ogP_fuel_unseal /ogP_fuel_def. rewrite -ogP_fuel_val_add. iApply (ogP_fuel_val_mon with "H").
      rewrite Hessenberg.add_comm -Jacobsthal.mult_S.
      apply Jacobsthal.le_mult_r. apply Ord.S_supremum; auto.
    Qed.

    (** ** embed_fuels rules *)
    Lemma embed_fuels_init {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a :
      ⊢ embed_fuels wf_ltA a ∅.
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def. apply collect_fuels_init.
    Qed.

    Lemma embed_fuels_add {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a F f ℓ μ :
      embed_fuels wf_ltA a F -∗ ogP_fuel f ℓ (μ × ℵ)%M ==∗ embed_fuels wf_ltA a (<[f:=(ℓ, μ)]>F).
      (* embed_fuels wf_ltA a ℓ1 F -∗ ogP_fuel f ℓ2 (μ × ⟪wf_ltA, a⟫)%M ==∗ embed_fuels wf_ltA a ℓ1 (<[f:=(ℓ2, μ)]>F). *)
    Proof.
      iIntros "Wfs Gf". rewrite !embed_fuels_unseal /embed_fuels_def.
      iApply (collect_fuels_add with "Wfs Gf").
      rewrite measure_embed measure_large. apply Ord.lt_le, Ord.large_lt_from_wf.
    Qed.

    Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
      a F (G : gmap ogid (ord.t * measurable_syntax)) :
      embed_fuels wf_ltA a F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ogP_fuel g l (m × ℵ)%M) ==∗
      embed_fuels wf_ltA a (G ∪ F).
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def.
      iIntros "Gfs Fs". iApply (collect_fuels_add_map with "Gfs [Fs]").
      iApply (big_sepM_impl with "Fs"). iIntros "!> %%%". destruct x. iIntros "$".
      iPureIntro. rewrite measure_embed measure_large. apply Ord.lt_le, Ord.large_lt_from_wf.
    Qed.

    Lemma embed_fuels_decr {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a a' F :
      ltA a' a →
      embed_fuels wf_ltA a F ==∗
      embed_fuels wf_ltA a' F ∗ ([∗ map] f ↦ '(l, m) ∈ F, ogP_fuel f l m).
    Proof.
      rewrite embed_fuels_unseal /embed_fuels_def.
      intros LT. apply (collect_fuels_decr). apply measure_embed_lt. auto.
    Qed.

    (** ** wit_fuels rules *)
    Lemma wit_fuels_init k ℓ :
      witP_layer k ℓ -∗ ∃ α, wit_fuels k ℓ α ∅.
    Proof.
      unfold_opreds. iIntros "(%& $& $)". iExists μ. iSplitR; done.
    Qed.

    Lemma wit_fuels_witP_layer k ℓ α F :
      wit_fuels k ℓ α F ==∗ witP_layer k ℓ.
    Proof.
      iIntros "Wl". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wl" as "(%& %& #Wb& _)".
      rewrite !witP_layer_unseal /witP_layer_def.
      iExists μ. iApply witP_bound_val_mon; eauto.
    Qed.

    Lemma wit_fuels_add k ℓ1 α F f ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      wit_fuels k ℓ1 α F -∗ ogP_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wfs" as "(%& %& $& M)".
      iExists _. iSplitR; first eauto.
      iApply (collect_fuels_add with "M Gf").
      etrans; first eauto. apply measure_extend. econstructor 1; eauto.
    Qed.

    Lemma wit_fuels_add_map k ℓ α F (G : gmap ogid (ord.t * measurable_syntax)) :
      wit_fuels k ℓ α F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (ℓ < l)%ordi ⌝ ∗ ogP_fuel g l (m × ▽)%M) ==∗
      wit_fuels k ℓ α (G ∪ F).
    Proof.
      rewrite !wit_fuels_unseal /wit_fuels_def.
      iIntros "(%& %& $& Fs) Gfs". iExists _. iSplitR; first eauto.
      iApply (collect_fuels_add_map _ _ _ (▽)%M with "Fs [Gfs]").
      iApply (big_sepM_impl with "Gfs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. etrans; first eauto. apply measure_extend. econstructor 1; eauto.
    Qed.

    Lemma wit_fuels_decr k ℓ α F :
      wit_fuels k ℓ α F -∗ witP_cred k Ord.one ==∗
      ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗
            ([∗ map] f ↦ '(l, m) ∈ F, ogP_fuel f l m).
    Proof.
      rewrite wit_fuels_unseal /wit_fuels_def. iIntros "(%& %& #Wbk& Fs) Wk".
      iMod (witP_bound_val_spend_one with "Wbk Wk") as "(%& %& #Wbk2)".
      iExists a0. iSplitR; first done. iFrame "Wbk2". assert (a0 <= η (measure (ℓ, 1) μ)).
      { etransitivity; last eauto. apply WFOCM.lt_le. auto. }
      iFrame (H1). iApply (collect_fuels_decr with "Fs"). auto.
    Qed.

  End liveness_preds.

  Section fmupd.

    (** ** Update rules *)
    Lemma thread_terminate_mupd n Θ i :
      thP_groups i ∅ -∗ |=[n,Θ]=>m thP_done i.
    Proof.
      unfold_opreds. iIntros "(#Oe& Ox& Ob)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
      iPoseProof (othread_elem with "[$O $Oe]") as "%Ini".
      iMod (ogroup_exec_to_done with "[$O $G $Ox $Ob]") as "(O& G& #Ot)". 1: auto.
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done.
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O G W A". iSplitR; eauto.
      iIntros "!> !>". auto.
    Qed.

    Lemma group_alloc_mupd n Θ i G ℓ μ :
      thP_groups i G -∗
      |=[n,Θ]=>m ∃ g, (⌜ g ∉ G ⌝) ∗
                     thP_groups i ({[g]} ∪ G) ∗ ogP_obls i g ℓ ∅ ∗ ogP_fuel g ℓ μ.
    Proof.
      unfold_opreds. iIntros "(#Te& Tx& Tpsa)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& G& W& %GWI)".
      iPoseProof (othread_elem with "[$T $Te]") as "%Ini".
      iMod (ogroup_alloc_group _ _ _ (measure (ℓ, 0) ((1 ⊕ ▽) × μ)%M) with "[$G $Tpsa]") as "(%& G& %LUp& Tpsa& Tps& Tpo& #Tb& Tf)".
      1: auto.
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S T G W A". iSplitR; eauto.
      iIntros "!> !>". iFrame "Te Tb". iFrame. iSplit; auto.
    Qed.

    Lemma group_delete_mupd n Θ i G g ℓ :
      thP_groups i G -∗
      ogP_obls i g ℓ ∅ -∗
      |=[n,Θ]=>m thP_groups i (G ∖ {[g]}).
    Proof.
      unfold_opreds. iIntros "(#Te& Tx& Tpsa) (_& Tpo& Tps& _)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& P& W& %GWI)".
      iPoseProof (othread_elem with "[$T $Te]") as "%Ini".
      iMod (ogroup_delete_group with "[$P $Tpsa $Tps $Tpo]") as "(P& Tpsa)".
      1: auto.
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S T P W A". iSplitR; eauto.
      iIntros "!> !>". iFrame "Te". iFrame.
    Qed.

    Lemma obl_alloc_assigned_mupd n Θ i g K b ℓ1 ℓ2 μ :
      (ℓ1 == ℓ2 ∨ ℓ1 < ℓ2)%ordi →
      (* FIXME?: above should be good enough, but below is more concise *)
      (* (ℓ1 <= ℓ2)%ordi → *)
      ogP_obls i g ℓ1 K -∗
      |=[n,Θ]=>m ∃ k, (⌜ k ∉ K ⌝) ∗
                     ogP_obls i g ℓ1 ({[k]} ∪ K) ∗
                     oblP_assigned k b (1/2)%Qp ∗
                     oblP_id k ∗
                     oblP_fuel k ℓ2 μ ∗
                     witP_layer k ℓ2 ∗
                     (∀ E N (P Q R : iProp Σ), (▷ (if b then Q else P)) ={E}=∗ oblP_inv N k P Q R).
    Proof.
      unfold_opreds. iIntros (LTl) "(#Te& Tpo& Tps& (%& #Tb)& TOs)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& P& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (osat_alloc_obl_assigned _ k b (measure (ℓ2, 1) (((1 ⊕ ▽) × μ) ⊕ ▽)%M) i with "S") as "(S& #Gwf& #Ge& Gl& Gf& Go& %OStep)". 1: auto.
      iDestruct "Gl" as "[Gl0 Gl1]".
      iEval (rewrite measure_add) in "Gf". iPoseProof (oblG_fuel_split with "Gf") as "[Gf Gf0]".
      iMod (oblG_fuel_mon _ (measure (ℓ1, 0) μ0) with "Gf0") as "Gf0".
      { etrans; first eapply η_mono. eapply measure_extend. econstructor 2; auto. }
      iPoseProof (othread_elem with "[$T $Te]") as "%Ini".
      iMod (ogroup_alloc_obl with "[$S $T $P $Tpo $Tps $Tb $Ge $Go $Gf0]") as "(S& T& P& %Nink& Tpo& Tps& To& Go)". 1: auto.      
      iMod (owit_alloc_witness_assigned _ k (η (measure (ℓ2, 1) (((1 ⊕ ▽) × μ) ⊕ ▽)%M)) with "W") as "(W& #Ww)".
      { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iDestruct "Go" as "[Go Go']". iDestruct "To" as "[To0 [To1 To']]".
      iPoseProof (oassigned_add_obl with "[$A $Ge Go' To']") as "A".
      { iLeft. iFrame. auto. }
      iDestruct "Gl0" as "[Gl0 Gl0']". iDestruct "Gl1" as "[Gl1 Gl1']".
      iCombine "Gl0 Gl1" as "Gl". iCombine "Gl0' Gl1'" as "Gl'".
      set (Ω2:=(<[k:=(obl_assigned (OC:=ord_obl_class) (measure (ℓ2, 1) (((1 ⊕ ▽) × μ) ⊕ ▽)%M) i)]> Ω1)).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
      iModIntro. iExists Ω2. iSplitR.
      { subst Ω2. iPureIntro. econstructor 2. econstructor 2. eauto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (owit_inv_alloc_assigned Ω1 k W1 NinOk1 GWI _ _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S T P W". iSplitL "A".
      { subst Ω2. rewrite dom_insert_L. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Te Tb Ge Ww Gf Tpo Tps Gl'". iSplitR. 1: auto.
      iSplitL "TOs Go To0 To1".
      { iApply big_sepS_union. 1: set_solver.
        rewrite big_sepS_singleton. iFrame "TOs Ge Go". iCombine "To0 To1" as "$". }
      iIntros (E N P Q R) "HP". destruct b.
      - iMod (oblG_inv_alloc_assigned_true _ N _ _ P Q R with "[$Gl $HP]") as "#GVar". by iModIntro.
      - iMod (oblG_inv_alloc_assigned_false _ N _ _ P Q R with "[$Gl $HP]") as "#GVar". by iModIntro.
    Qed.

    Lemma obl_alloc_fulfilled_mupd n Θ ℓ μ :
      ⊢ |=[n,Θ]=>m ∃ k, oblP_fulfilled k ∗ oblP_id k ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                       (∀ E N (P Q R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P Q R).
    Proof.
      unfold_opreds.
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& P& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (osat_alloc_obl_fulfilled _ k (measure (ℓ, 1) ((1 ⊕ ▽) × μ)%M) with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)".
      { auto. }
      iMod (owit_alloc_witness_fulfilled _ k (η (measure (ℓ, 1) ((1 ⊕ ▽) × μ)%M)) with "[$W $Gu]") as "(W& #Ww)".
      { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
      { iRight. iFrame "Gu". }
      set (Ω2:=(<[k:=(obl_fulfilled)]> Ω1)).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
      iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (owit_inv_alloc_fulfilled Ω1 k W1 NinOk1 GWI W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O P W". iSplitL "A".
      { subst Ω2. rewrite dom_insert_L. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Ge Ww Gf Gu".
      iIntros (E N P Q R) "HQ".
      iMod (oblG_inv_alloc_fulfilled _ N _ _ P Q R with "[$Gu $HQ]") as "#GVar".
      iModIntro. eauto.
    Qed.

    Lemma obl_assigned_to_true_mupd E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R -∗
      |={E,E ∖ ↑N}=> oblP_assigned k false (1/2)%Qp -∗
                    ((▷ (oblP_assigned k false 1 ∗ P)) ∗
                     (∀ b, oblP_assigned k b 1 -∗
                           ∀ n Θ, |=[n,Θ]=>m (oblP_assigned k true (1/2)%Qp) ∗
                                          ((▷ Q) ={E ∖ ↑N,E}=∗ True))).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc_assigned with "Gvar") as "H". 1: auto.
      iModIntro. iIntros "(_& Ga)". iPoseProof ("H" with "Ga") as "[H ACC]". iSplitL "H".
      { iNext. iDestruct "H" as "([Ga1 Ga1']& [Ga2 Ga2']& $)". iFrame "Ge".
        iCombine "Ga1 Ga2" as "Ga". iCombine "Ga1' Ga2'" as "Ga'". iCombine "Ga Ga'" as "$". }
      iIntros (b) "(_& Ga) %%".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& P& W& %GWI1)".
      iMod (osat_assigned_to_true with "[$S $Ge $Ga]") as "(S& Ga)".
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI1 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O P W A". iSplitR; eauto.
      iDestruct "Ga" as "[[Ga1 Ga2] [Ga1' Ga2']]". iCombine "Ga1 Ga1'" as "Ga1". iCombine "Ga2 Ga2'" as "Ga2".
      iFrame "Ge Ga1". iIntros "!> !> HQR". iApply "ACC". iNext. iRight. iLeft. iFrame.
    Qed.

    Lemma obl_fulfill_mupd E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R -∗
      |={E,E ∖ ↑N}=> ∀ i g ℓ K q,
      (⌜k ∈ K⌝) → ogP_obls i g ℓ K -∗ oblP_assigned k true q -∗
      ((▷ (ogP_obls i g ℓ K ∗ oblP_assigned k true q ∗ oblP_assigned k true (1/2) ∗ Q)) ∗
       (ogP_obls i g ℓ K -∗
        oblP_assigned k true 1 -∗
        ∀ n Θ, |=[n,Θ]=>m (ogP_obls i g ℓ (K ∖ {[k]}) ∗ oblP_fulfilled k) ∗
                       ((▷ (R)) ={E ∖ ↑N,E}=∗ True))).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc_assigned with "Gvar") as "H". 1: auto.
      iIntros "!> %%%%% %LUGk (#Tei& Ggg& Gti& #Gbg& OS) (_& Ga)". iPoseProof ("H" with "Ga") as "[H ACC]".
      iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
      iSplitL "Ggg Gti Go Oo OS H".
      { iNext. iFrame "Ge Ggg Gti". iDestruct "H" as "(Gl& $& $)".
        rewrite (big_sepS_delete _ _ _ LUGk). iFrame. iFrame "Ge Tei Gbg". }
      iIntros "(_& Ggg& Gti& _& OS) (_& Gl) %%".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
      iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
      iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
      iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&LUO1o).
      rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into a.
      iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
      { apply elem_of_dom. eauto. }
      2:{ iExFalso. iPoseProof (oblG_assigned_fulfilled_false with "[$Gl $Gu]") as "%". done. }
      iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [<- _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iPoseProof (othread_elem with "[$O $Tei]") as "%Ini".
      iMod (ogroup_delete_obl with "[$O $G $Ggg $Oo]") as "(O& G& Ggg& Go2)". 1,2: auto.
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'". iCombine "Go Go'" as "Go".
      iMod (osat_fulfill with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
      assert (LUW : ∃ b, W1 !! k = Some (witness_assigned b) ∧ (b <= η a)%ord).
      { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y; try done. eauto. }
      destruct LUW as (b&LUW1& LEab).
      iPoseProof (owit_fulfill with "[$W $Gu]") as "W". 1: eauto.
      iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
      { iRight. eauto. }
      set (Ω2:=(<[k:=(obl_fulfilled)]> Ω1)).
      assert (Gstep' : obl_step (obl_assigned a i) obl_fulfilled) by (by econstructor 2).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_fulfill _ _ _ _ _ LUO1l GWI Gstep' W2 WStep GWI2) as (?& LUW& WMon).
      rewrite LUW1 in LUW. inv LUW.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O G W". iSplitL "A".
      { iModIntro. subst Ω2. rewrite dom_insert_L.
        replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)).
        { iFrame. eauto. }
        apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
      iApply fupd_intro. iIntros "!>". iFrame "Tei Ge Gu Ggg Gti".
      iSplitR "ACC". 1: by iFrame.
      iIntros "HQ". iMod ("ACC" with "[HQ]") as "_".
      { iNext. iRight. iFrame. eauto. }
      done.
    Qed.

    Local Lemma obl_change_group_mupd n Θ i g1 g2 K1 K2 ℓ1 ℓ2 ℓ k :
      k ∈ K1 →
      (ℓ2 == ℓ ∨ ℓ2 < ℓ)%ordi →
      ogP_obls i g1 ℓ1 K1 -∗
      ogP_obls i g2 ℓ2 K2 -∗
      oblP_fuel k ℓ 1 -∗
      |=[n,Θ]=>m ogP_obls i g1 ℓ1 (K1 ∖ {[k]}) ∗ ogP_obls i g2 ℓ2 (K2 ∪ {[k]}) ∗ ⌜ k ∉ K2 ⌝.
    Proof.
      unfold_opreds. iIntros (Ink LTl) "(#Tei& Gg1& Gt1& (%& #Gb1)& KS1) (_& Gg2& Gt2& (%& #Gb2)& KS2) Of".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& G& W& %GWI)".
      iPoseProof (othread_elem with "[$T $Tei]") as "%Ini".
      iDestruct "Of" as "(#Oek& Of)".
      iMod (oblG_fuel_mon _ (measure (ℓ2, 0) μ0) with "Of") as "Of".
      { rewrite measure_mult measure_add measure_nat Jacobsthal.mult_1_r.
        etrans; last eapply Hessenberg.add_base_r.
        etrans; first eapply η_mono. apply measure_extend. econstructor 2; auto. }
      iAssert (⌜k ∉ K2⌝)%I as "%Nink2".
      { destruct (decide (k ∈ K2)); auto.
        iPoseProof (big_sepS_delete _ _ _ Ink with "KS1") as "[(_& Go& Oo) KS1]".
        iPoseProof (big_sepS_delete _ _ _ e with "KS2") as "[(_& Go2& Oo2) KS2]".
        iPoseProof (oblG_owner_agree with "[$Go $Go2]") as "%". destruct H. subst. done. }
      iMod (ogroup_obl_change_group with "[$G $Gg1 $Gg2 $Gb2 $Of]") as "(G& Gg1& Gg2)". 1,2: auto.
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S T G W A". iSplitR; eauto.
      iIntros "!> !>". iFrame. iPoseProof (big_sepS_delete _ _ _ Ink with "KS1") as "[Kk KS1]".
      iFrame "Tei Gb1 Gb2 KS1". iSplit; last auto.
      iApply (big_sepS_union_2 with "KS2"). iApply big_sepS_singleton. iFrame.
    Qed.

    Local Lemma obl_change_thread_mupd n Θ i1 i2 g1 g2 K1 K2 ℓ1 ℓ2 ℓ k :
      i1 ≠ i2 →
      k ∈ K1 →
      (ℓ2 == ℓ ∨ ℓ2 < ℓ)%ordi →
      ogP_obls i1 g1 ℓ1 K1 -∗
      ogP_obls i2 g2 ℓ2 K2 -∗
      oblP_fuel k ℓ 1 -∗
      |=[n,Θ]=>m ogP_obls i1 g1 ℓ1 (K1 ∖ {[k]}) ∗ ogP_obls i2 g2 ℓ2 (K2 ∪ {[k]}) ∗ ⌜ k ∉ K2 ⌝.
    Proof.
      unfold_opreds. iIntros (Nei Ink LTl) "(#Tei1& Gg1& Gt1& (%& #Gb1)& KS1) (#Tei2& Gg2& Gt2& (%& #Gb2)& KS2) Of".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& G& W& %GWI)".
      iPoseProof (othread_elem with "[$T $Tei1]") as "%Ini1".
      iPoseProof (othread_elem with "[$T $Tei2]") as "%Ini2".
      iDestruct "Of" as "(#Ge& Of)".
      iMod (oblG_fuel_mon _ (measure (ℓ2, 0) (1 ⊕ μ0)%M) with "Of") as "Of".
      { rewrite measure_mult (measure_add (ℓ, 1)) measure_nat Jacobsthal.mult_1_r.
        etrans; last eapply Hessenberg.add_base_r.
        etrans; first eapply η_mono. apply measure_extend. econstructor 2; auto. }
      iEval (rewrite measure_add) in "Of".
      iPoseProof (oblG_fuel_split with "Of") as "[Of0 Of]".
      iMod (oblG_fuel_mon _ (1) with "Of0") as "Of0".
      { rewrite measure_nat. done. }
      iAssert (⌜k ∉ K2⌝)%I as "%Nink2".
      { destruct (decide (k ∈ K2)); auto.
        iPoseProof (big_sepS_delete _ _ _ Ink with "KS1") as "[(_& Go& Oo) KS1]".
        iPoseProof (big_sepS_delete _ _ _ e with "KS2") as "[(_& Go2& Oo2) KS2]".
        iPoseProof (oblG_owner_agree with "[$Go $Go2]") as "%". destruct H. subst. done. }
      iPoseProof (big_sepS_delete _ _ _ Ink with "KS1") as "[(_& Go& Oo) KS1]".
      iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1o as (?&LUO1o). rename x into a.
      iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
      { apply elem_of_dom. eauto. }
      2:{ iExFalso. iPoseProof (osat_lookup_fulfilled with "[$S $Ge $Gu]") as "%". rewrite H in LUO1o; done. }
      iPoseProof (oblG_owner_agree _ i0 i1 with "[$Go $Go1]") as "%". destruct H as [-> _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (ogroup_obl_change_thread _ i1 i2 g1 g2 with "[$G $Gg1 $Gg2 $Gb2 $Of]")
        as "(%& %& ACC& %Ink1& Tx1& TG1& Tx2& TG2& Gg1& Gg2)". 1,2,3,4: auto.
      iMod (othread_delete_obl with "[$T $TG1 $Oo]") as "(T& TG1& Go2)".
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'". iCombine "Go Go'" as "Go".
      iMod (osat_progress_one_owner _ _ _ _ i2 with "[$S $Go $Of0]") as "(%& S& Go& %Gstep)".
      1: eauto. 1: apply Ord.S_lt.
      iMod (othread_alloc_obl with "[$S $T $TG2 $Ge $Go]") as "(S& T& %NinkG2& TG2& Oo& Go)".
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
      iPoseProof (oassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. auto. }
      set (Ω2:=(<[k:=(obl_assigned a' i2)]> Ω1)).
      assert (Gstep' : obl_step (obl_assigned a i1) (obl_assigned a' i2)) by (by econstructor 1).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iPoseProof ("ACC" with "[//] Tx1 TG1 Tx2 TG2") as "G".
      iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_progress_owner _ k _ _ _ LUO1o GWI _ _ Gstep' W2 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S T G W". iSplitL "A".
      { iModIntro. subst Ω2. rewrite dom_insert_L.
        replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)).
        { iFrame. eauto. }
        apply elem_of_dom_2 in LUO1o. rewrite -union_difference_L; set_solver. }
      iIntros "!> !>". iFrame "Tei1 Tei2 Gt1 Gt2 KS1 Gg1 Gg2 Gb1 Gb2".
      iSplitL; last auto. iApply (big_sepS_union_2 with "KS2").
      rewrite big_sepS_singleton. iFrame. iCombine "Oo Oo1" as "Oo". eauto.
    Qed.

    Lemma obl_offload_mupd n Θ i1 i2 g1 g2 K1 K2 ℓ1 ℓ2 ℓ k :
      k ∈ K1 →
      (ℓ2 == ℓ ∨ ℓ2 < ℓ)%ordi →
      ogP_obls i1 g1 ℓ1 K1 -∗
      ogP_obls i2 g2 ℓ2 K2 -∗
      oblP_fuel k ℓ 1 -∗
      |=[n,Θ]=>m ogP_obls i1 g1 ℓ1 (K1 ∖ {[k]}) ∗ ogP_obls i2 g2 ℓ2 (K2 ∪ {[k]}) ∗ ⌜ k ∉ K2 ⌝.
    Proof.
      intros. destruct (decide (i1 = i2)).
      - subst. apply obl_change_group_mupd; auto.
      - apply obl_change_thread_mupd; auto.
    Qed.

    Lemma obl_offload_set_mupd n Θ i1 i2 g1 g2 K1 K2 K ℓ1 ℓ2 ℓ :
      K ⊆ K1 →
      (ℓ2 == ℓ ∨ ℓ2 < ℓ)%ordi →
      ogP_obls i1 g1 ℓ1 K1 -∗
      ogP_obls i2 g2 ℓ2 K2 -∗
      ([∗ set] k ∈ K, oblP_fuel k ℓ 1) -∗
      |=[n,Θ]=>m ogP_obls i1 g1 ℓ1 (K1 ∖ K) ∗ ogP_obls i2 g2 ℓ2 (K2 ∪ K) ∗ ⌜ K2 ## K ⌝.
    Proof.
      revert K1 K2. pattern K. revert K. apply set_ind.
      { solve_proper. }
      { iIntros (K1 K2 HK LTl) "Gg1 Gg2 Kfs".
        replace (K1 ∖ ∅) with K1 by set_solver. replace (K2 ∪ ∅) with K2 by set_solver.
        iFrame. iModIntro. iPureIntro. set_solver. }
      iIntros (k K Nink IH K1 K2 HK LTl) "Gg1 Gg2 Kfs".
      iPoseProof (big_sepS_union with "Kfs") as "[F Kfs]". 1: set_solver.
      iMod (IH K1 K2 with "Gg1 Gg2 Kfs") as "(Gg1& Gg2& %Disj)". 1: set_solver. 1: auto.
      replace (K1 ∖ ({[k]} ∪ K)) with ((K1 ∖ K) ∖ {[k]}) by set_solver.
      replace (K2 ∪ ({[k]} ∪ K)) with ((K2 ∪ K) ∪ {[k]}) by set_solver.
      rewrite big_sepS_singleton.
      iMod (obl_offload_mupd with "Gg1 Gg2 F") as "($& $& %)". 1: set_solver. 1: auto.
      iPureIntro. set_solver.
    Qed.

    Lemma obl_check_witnesses_mupd n Θ (R : oids) :
      ([∗ set] r ∈ R, oblP_id r) -∗
      |=[n,Θ]=>m ([∗ set] r ∈ R, (witP_cred r Ord.O) ∨ oblP_fulfilled r).
    Proof.
      unfold_opreds. iIntros "#REs".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI1)".
      iPoseProof (owit_get_credit_zero with "W") as "[W Ws]".
      assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
      iAssert (⌜ R ⊆ dom W1 ⌝)%I as "%RWSub".
      { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
        iPoseProof (big_sepS_delete _ _ _ INRx with "REs") as "[#Beg _]".
        iPoseProof (osat_elem with "[$S $Beg]") as "%". done. }
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ R = dom WR).
      { clear GWI1 DomOW WStep.
        revert R RWSub. induction W1 using map_ind; intros.
        { assert (R = ∅) by (set_solver). subst. exists ∅, ∅. done. }
        rename i0 into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ R)).
        - set (R2 := R ∖ {[r]}). assert (R2 ⊆ dom m).
          { subst R2. set_solver. }
          destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
          exists (<[r:=x]>WR), WR'. subst R2.
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. split_and !.
          + apply map_disjoint_insert_l. split; auto.
          + subst. rewrite insert_union_l. done.
          + replace R with ({[r]} ∪ (R ∖ {[r]})).
            * rewrite !dom_insert_L H3. auto.
            * rewrite -union_difference_L; set_solver.
        - assert (R ⊆ dom m).
          { set_solver + RWSub n0. }
          pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. exists WR, (<[r:=x]> WR'). split_and !; auto.
          + apply map_disjoint_insert_r. split; auto.
          + subst. rewrite insert_union_r; done.
      }
      destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
      iAssert (⌜ ∀ k, k ∈ R → ∃ w, WR !! k = Some w ⌝)%I as "%Rver".
      { iPureIntro. intros. subst. apply elem_of_dom in H. destruct H. eauto. }
      iAssert (|==> [∗ set] r ∈ R, (witG_witness r Ord.O) ∨ (oblG_fulfilled r))%I with "[Ws]" as ">Rs".
      { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto. iClear "REs".
        subst R. rewrite -big_sepS_bupd -big_sepM_dom. iApply (big_sepM_impl with "Ws1").
        iIntros "!> %%% H".  destruct x; eauto. }
      iCombine "REs Rs" as "Rs". iPoseProof (big_sepS_sep with "Rs") as "Rs".
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI1 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O W G A". iSplitR; eauto.
      iIntros "!> !>". iApply (big_sepS_impl with "Rs"). iIntros "!> %% (#Ge& [Ww | Gf])".
      - iLeft. eauto.
      - iRight. eauto.
    Qed.

    (** ** Variant access rules *)
    Lemma oblP_variant_unfold k P Q R :
      oblP_variant k P Q R
      ⊣⊢ ((oblP_assigned k false (1/2)%Qp ∗ P) ∨ (oblP_assigned k true (1/2)%Qp ∗ Q) ∨ (oblP_fulfilled k ∗ R))%I.
    Proof. rewrite !oblP_variant_unseal /oblP_variant_def. auto. Qed.

    Local Lemma oblP_variant_oblG_variant k P Q R :
      oblP_variant k P Q R -∗
      oblG_variant k ((1/2)/2 + (1/2)/2/2)%Qp P Q R.
    Proof.
      unfold_opreds. iIntros "[H | [H | H]]".
      - iLeft. iDestruct "H" as "((_& $)& $)".
      - iRight. iLeft. iDestruct "H" as "((_& $)& $)".
      - iRight. iRight. iDestruct "H" as "((_& $)& $)".
    Qed.

    Lemma oblP_inv_acc_cases E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ oblP_variant k P Q R) ∗ (▷ oblP_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc with "Gvar") as "[[H | [H | H]] ACC]". 1: auto.
      - iModIntro. iSplitL "H".
        + iNext. iLeft. iDestruct "H" as "($&$)". auto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply oblP_variant_oblG_variant. unfold_opreds. done.
      - iModIntro. iSplitL "H".
        + iNext. iRight. iLeft. iDestruct "H" as "($& $)". auto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply oblP_variant_oblG_variant. unfold_opreds. done.
      - iModIntro. iSplitL "H".
        + iNext. iRight. iRight. iDestruct "H" as "($& $)". auto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply oblP_variant_oblG_variant. unfold_opreds. done.
    Qed.

    Lemma oblP_inv_acc E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ ((oblP_assigned k false (1/2) ∗ P) ∨ (oblP_assigned k true (1/2) ∗ Q) ∨ (oblP_fulfilled k ∗ R))) ∗
      (▷ oblP_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (H) "Gv". iMod (oblP_inv_acc_cases with "Gv") as "[H $]". 1: auto.
      iModIntro. iNext. by iApply oblP_variant_unfold.
    Qed.

    Lemma oblP_inv_acc_assigned E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R
      ={E,E ∖ ↑N}=∗ ∀ b q,
      oblP_assigned k b q -∗
      (▷ (oblP_assigned k b q ∗ (if b then (oblP_assigned k true (1/2) ∗ Q) else (oblP_assigned k false (1/2) ∗ P)))) ∗
      (▷ oblP_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc_assigned with "Gvar") as "H". 1: auto.
      iIntros "!> %% (_& Ga)". iPoseProof ("H" with "Ga") as "[H ACC]". iFrame "Ge". iSplitL "H".
      { iNext. destruct b.
        - iDestruct "H" as "($& $& $)". auto.
        - iDestruct "H" as "($& $& $)". auto. }
      iIntros "H". iApply "ACC". iNext. iApply oblP_variant_oblG_variant. unfold_opreds. done.
    Qed.

    Lemma oblP_inv_acc_fulfilled E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R
      ={E,E ∖ ↑N}=∗
      oblP_fulfilled k -∗
      ((▷ (R)) ∗
       (▷ oblP_variant k P Q R ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc_fulfilled with "Gvar") as "H". 1: auto.
      iIntros "!> [_ #Gu]". iPoseProof ("H" with "Gu") as "[H ACC]".
      iSplitL "H".
      { iNext. iFrame. }
      iIntros "H". iApply "ACC". iNext. iApply oblP_variant_oblG_variant. unfold_opreds. done.
    Qed.

    Lemma oblP_inv_acc_fulfilled_persistent E N k P Q R :
      Persistent R →
      ↑N ⊆ E →
      oblP_inv N k P Q R -∗
      oblP_fulfilled k ={E}[E ∖ ↑N]▷=∗ R.
    Proof.
      iIntros (PR HE) "#GU #Gf". iMod (oblP_inv_acc_fulfilled with "GU Gf") as "[H ACC]". 1: auto.
      iModIntro. iNext. iPoseProof "H" as "#H". iFrame "H". iApply "ACC".
      rewrite oblP_variant_unfold. iRight. eauto.
    Qed.

  End fmupd.

End preds.
