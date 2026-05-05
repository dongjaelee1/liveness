From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.algebra Require Import ordinal_wfocm.
From liris.base_logic Require Export mupd oinv.

(** All Local Definitions are only for internal uses and users should not need them. *)
(** Obl predicates. *)
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
  oblP_fuel_val k (measure ℓ (▽ × μ)%M).
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

(** Witness predicates *)
Local Definition witP_bound_val `{SI : indexT} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  oblP_id k ∗ witG_bound k α.

Local Definition witP_layer_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ : iProp Σ :=
  ∃ μ, witP_bound_val k (η (measure ℓ μ)).
Local Definition witP_layer_aux : seal (@witP_layer_def). Proof. by eexists. Qed.
Definition witP_layer := witP_layer_aux.(unseal).
Local Definition witP_layer_unseal :
  @witP_layer = @witP_layer_def := witP_layer_aux.(seal_eq).
Global Arguments witP_layer {SI Σ _ _}.

Local Definition witP_cred_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  oblP_id k ∗ witG_witness k Ord.one.
Local Definition witP_cred_aux : seal (@witP_cred_def). Proof. by eexists. Qed.
Definition witP_cred := witP_cred_aux.(unseal).
Local Definition witP_cred_unseal :
  @witP_cred = @witP_cred_def := witP_cred_aux.(seal_eq).
Global Arguments witP_cred {SI Σ _}.

(** Thread predicates *)
Local Definition thP_fuel_val `{SI : indexT} `{@mupdGS SI Σ}
  s α : iProp Σ :=
  othreadG_fuel s α.

Local Definition thP_fuel_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  s ℓ μ : iProp Σ :=
  thP_fuel_val s (measure ℓ μ).
Local Definition thP_fuel_aux : seal (@thP_fuel_def). Proof. by eexists. Qed.
Definition thP_fuel := thP_fuel_aux.(unseal).
Local Definition thP_fuel_unseal :
  @thP_fuel = @thP_fuel_def := thP_fuel_aux.(seal_eq).
Global Arguments thP_fuel {SI Σ _ _}.

Local Definition thP_proxy_auth_def `{SI : indexT} `{@mupdGS SI Σ}
  i PS : iProp Σ :=
  othreadG_exec i (1/2)%Qp ∗ othreadG_proxy_session_auth i PS (1/2)%Qp.
Local Definition thP_proxy_auth_aux : seal (@thP_proxy_auth_def). Proof. by eexists. Qed.
Definition thP_proxy_auth := thP_proxy_auth_aux.(unseal).
Local Definition thP_proxy_auth_unseal :
  @thP_proxy_auth = @thP_proxy_auth_def := thP_proxy_auth_aux.(seal_eq).
Global Arguments thP_proxy_auth {SI Σ _}.

Local Definition thP_layer `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  s ℓ : iProp Σ :=
  ∃ μ, othreadG_bound s (measure ℓ μ).

Local Definition thP_proxy_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  i π s ℓ (K : oids) : iProp Σ :=
  othreadG_elem i ∗
  othreadG_proxy_obls i π K ∗ othreadG_proxy_session i π s (1)%Qp ∗ thP_layer s ℓ ∗
  ([∗ set] k ∈ K, oblP_id k ∗ oblG_owner k i (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns i k (1/2 + 1/2/2)%Qp).
Local Definition thP_proxy_aux : seal (@thP_proxy_def). Proof. by eexists. Qed.
Definition thP_proxy := thP_proxy_aux.(unseal).
Local Definition thP_proxy_unseal :
  @thP_proxy = @thP_proxy_def := thP_proxy_aux.(seal_eq).
Global Arguments thP_proxy {SI Σ _ _}.

Local Definition thP_done_def `{SI : indexT} `{@mupdGS SI Σ}
  i : iProp Σ :=
  othreadG_elem i ∗ othreadG_done i.
Local Definition thP_done_aux : seal (@thP_done_def). Proof. by eexists. Qed.
Definition thP_done := thP_done_aux.(unseal).
Local Definition thP_done_unseal :
  @thP_done = @thP_done_def := thP_done_aux.(seal_eq).
Global Arguments thP_done {SI Σ _}.

(** Additional definitions for more convenient induction rules *)
Local Definition collect_fuels `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  α (F : gmap session (layer * measurable_syntax)) : iProp Σ :=
  ([∗ map] s ↦ '(l, m) ∈ F, thP_fuel_val s ((measure l m) × α)%ord).

Local Definition embed_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (a : A) ℓ (F : gmap session (layer * measurable_syntax)) : iProp Σ :=
  collect_fuels (measure ℓ (⟪wf_ltA, a⟫)%M) F.
Local Definition embed_fuels_aux : seal (@embed_fuels_def). Proof. by eexists. Qed.
Definition embed_fuels := embed_fuels_aux.(unseal).
Local Definition embed_fuels_unseal :
  @embed_fuels = @embed_fuels_def := embed_fuels_aux.(seal_eq).
Global Arguments embed_fuels {SI Σ _ _ A ltA}.

Local Definition wit_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ α (F : gmap session (layer * measurable_syntax)) : iProp Σ :=
  ∃ μ, ⌜ (α <= η (measure ℓ μ))%ord ⌝ ∗ witP_bound_val k α ∗
       collect_fuels α F.
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
  try rewrite !thP_proxy_unseal /thP_proxy_def;
  try rewrite /thP_layer;
  try rewrite !thP_proxy_auth_unseal /thP_proxy_auth_def;
  try rewrite !thP_fuel_unseal /thP_fuel_def;
  try rewrite /thP_fuel_val;
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
Ltac unfold_thP_fuel :=
  try rewrite !thP_fuel_unseal /thP_fuel_def.

Section preds.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Section liveness_preds.

    (** Instances *)
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
    Local Instance thP_layer_persistent e ℓ : Persistent (thP_layer e ℓ).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_done_persistent i : Persistent (thP_done i).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance collect_fuels_empty_persistent α : Persistent (collect_fuels α ∅).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance embed_fuels_empty_persistent {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Persistent (embed_fuels wf_ltA a ℓ ∅).
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
    Global Instance witP_cred_timeless k : Timeless (witP_cred k).
    Proof. unfold_opreds. apply _. Qed.
    Local Instance thP_layer_timeless e ℓ : Timeless (thP_layer e ℓ).
    Proof. unfold_opreds. apply _. Qed.
    Local Instance thP_fuel_val_timeless e α : Timeless (thP_fuel_val e α).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_fuel_timeless e ℓ μ : Timeless (thP_fuel e ℓ μ).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_proxy_auth_timeless i PS : Timeless (thP_proxy_auth i PS).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_proxy_timeless i π s ℓ K : Timeless (thP_proxy i π s ℓ K).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance thP_done_timeless i : Timeless (thP_done i).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance collect_fuels_timeless α F : Timeless (collect_fuels α F).
    Proof. unfold_opreds. apply _. Qed.
    Global Instance embed_fuels_empty_timeless {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Timeless (embed_fuels wf_ltA a ℓ ∅).
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

    Lemma oblP_fuel_val_eq k a0 a1 :
      (a0 == a1) → oblP_fuel_val k a0 = oblP_fuel_val k a1.
    Proof.
      unfold_opreds. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
    Qed.
    Lemma oblP_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, oblP_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, oblP_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_val_eq; eauto. Qed.
    Lemma oblP_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, oblP_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_val_eq; eauto. Qed.

    Lemma oblP_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → oblP_fuel_val k a1 ==∗ oblP_fuel_val k a0.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
    Qed.
    Lemma oblP_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_mon.
    Qed.
    Lemma oblP_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_mon.
    Qed.

    Lemma oblP_fuel_val_add k a0 a1 :
      oblP_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
    Proof.
      unfold_opreds. rewrite oblG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Lemma oblP_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, oblP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblP_fuel_val_add.
    Qed.
    Lemma oblP_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, oblP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblP_fuel_val_add.
    Qed.

    Lemma oblP_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → oblP_fuel_val k a2 ==∗ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(#Be& P)".
      iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma oblP_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, oblP_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oblP_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply oblP_fuel_val_add_list.
    Qed.
    Lemma oblP_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, oblP_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oblP_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply oblP_fuel_val_add_set.
    Qed.

    Lemma oblP_fuel_val_lt k a0 a1 :
      a0 < a1 →
      oblP_fuel_val k a1 ⊢ |==> oblP_fuel_val k a0 ∗ oblP_fuel_val k Ord.one.
    Proof.
      unfold_opreds. iIntros (Hlt) "(#Be& P)".
      iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma oblP_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ list] k ∈ K, oblP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_lt.
    Qed.
    Lemma oblP_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, oblP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k a0) ∗ ([∗ set] k ∈ K, oblP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_val_lt.
    Qed.

    Lemma oblP_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      oblP_fuel_val k (b × a1)%ord ⊢ |==> oblP_fuel_val k (b × a0) ∗ oblP_fuel_val k b.
    Proof.
      unfold_opreds. intros LT. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (oblG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Lemma oblP_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, oblP_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, oblP_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_val_mult. auto.
    Qed.
    Lemma oblP_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, oblP_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, oblP_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_val_mult. auto.
    Qed.

    Lemma oblP_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      oblP_fuel_val k (b ↑ a1)%ord ⊢ |==> oblP_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_opreds. intros LT Pos. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Lemma oblP_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, oblP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_val_expn; auto.
    Qed.
    Lemma oblP_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, oblP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_val_expn; auto.
    Qed.

    (** oblP_fuel rules *)
    Lemma oblP_fuel_unfold k ℓ μ :
      oblP_fuel k ℓ μ = oblP_fuel_val k (measure ℓ (▽ × μ)%M).
    Proof. rewrite oblP_fuel_unseal /oblP_fuel_def. auto. Qed.

    Lemma oblP_fuel_eq k ℓ μ1 μ2 :
      (measure ℓ (μ1)%M == measure ℓ (μ2)%M) →
      oblP_fuel k ℓ μ1 = oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. intros. rewrite !measure_mult.
      apply oblP_fuel_val_eq. rewrite H. done.
    Qed.
    Lemma oblP_fuel_eq_list K ℓ μ1 μ2 :
      (measure ℓ (μ1)%M == measure ℓ (μ2)%M) →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.
    Lemma oblP_fuel_eq_set K ℓ μ1 μ2 :
      (measure ℓ (μ1)%M == measure ℓ (μ2)%M) →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.

    Lemma oblP_fuel_mon k ℓ  μ1 μ2 :
      (measure ℓ (μ1)%M <= measure ℓ (μ2)%M)%ord →
      oblP_fuel k ℓ μ2 ==∗ oblP_fuel k ℓ μ1.
    Proof.
      unfold_oblP_fuel. intros. apply oblP_fuel_val_mon.
      rewrite !measure_mult. apply Jacobsthal.le_mult_r. auto.
    Qed.
    Lemma oblP_fuel_mon_list K ℓ μ1 μ2 :
      (measure ℓ (μ1)%M <= measure ℓ (μ2)%M)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon.
    Qed.
    Lemma oblP_fuel_mon_set K ℓ μ1 μ2 :
      (measure ℓ (μ1)%M <= measure ℓ (μ2)%M)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_mon.
    Qed.

    Lemma oblP_fuel_mon_split k ℓ μ1 μ2 μ3 :
      ((measure ℓ (μ1)%M ⊕ measure ℓ (μ2)%M) <= measure ℓ (μ3)%M)%ord →
      oblP_fuel k ℓ μ3 ==∗ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. intros. apply oblP_fuel_val_mon_split.
      rewrite !measure_mult. rewrite -ClassicJacobsthal.mult_dist. apply Jacobsthal.le_mult_r. auto.
    Qed.
    Lemma oblP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
      ((measure ℓ (μ1)%M ⊕ measure ℓ (μ2)%M) <= measure ℓ (μ3)%M)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply oblP_fuel_mon_split; auto.
    Qed.
    Lemma oblP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
      ((measure ℓ (μ1)%M ⊕ measure ℓ (μ2)%M) <= measure ℓ (μ3)%M)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply oblP_fuel_mon_split; auto.
    Qed.

    Lemma oblP_fuel_lt k ℓ μ1 μ2 :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      oblP_fuel k ℓ μ2 ⊢ |==> oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ (1)%M.
    Proof.
      unfold_oblP_fuel. intros. rewrite !measure_mult.
      iIntros "H". iMod (oblP_fuel_val_mult _ _ _ _ H with "H") as "[$ H]".
      iModIntro. iStopProof. erewrite oblP_fuel_val_eq. 1: eauto.
      rewrite measure_nat Jacobsthal.mult_1_r. done.
    Qed.
    Lemma oblP_fuel_lt_list K ℓ μ1 μ2 :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_lt.
    Qed.
    Lemma oblP_fuel_lt_set K ℓ μ1 μ2 :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oblP_fuel_lt.
    Qed.

    TODO

    (* measurable syntax rules. *)
    Lemma oblP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ oblP_fuel k 0 1.
    Proof.
      intros. apply oblP_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma oblP_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_embed. auto.
    Qed.
    Lemma oblP_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_embed. auto.
    Qed.

    Lemma oblP_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      oblP_fuel k ℓ (⫚)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ oblP_fuel k 0 1.
    Proof.
      intros. apply oblP_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma oblP_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, oblP_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_large.
    Qed.
    Lemma oblP_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, oblP_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_large.
    Qed.

    Lemma oblP_fuel_add k ℓ μ1 μ2 :
      oblP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
    Proof.
      unfold_oblP_fuel. rewrite measure_mult measure_add.
      etrans; last eapply oblP_fuel_val_add. erewrite oblP_fuel_val_eq. 1: reflexivity.      
      rewrite ClassicJacobsthal.mult_dist -!measure_mult. reflexivity.
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
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      oblP_fuel k ℓ (s × μ2)%M ⊢ |==> oblP_fuel k ℓ (s × μ1)%M ∗ oblP_fuel k ℓ s.
    Proof.
      unfold_oblP_fuel. intros LT. rewrite !measure_mult.
      oblP_fuel_val_lt
      apply oblP_fuel_val_mult. auto.
    Qed.
    Lemma oblP_fuel_mult_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_mult. auto.
    Qed.
    Lemma oblP_fuel_mult_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_mult. auto.
    Qed.

    Lemma oblP_fuel_expn k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      oblP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> oblP_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_oblP_fuel. intros LT Pos. rewrite !measure_mult !measure_expn. apply oblP_fuel_val_expn; auto.
    Qed.
    Lemma oblP_fuel_expn_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ list] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_expn; auto.
    Qed.
    Lemma oblP_fuel_expn_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ set] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_expn; auto.
    Qed.

    Lemma oblP_fuel_extend_val k ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      oblP_fuel k ℓ2 (▽)%M ⊢ |==> oblP_fuel_val k o.
    Proof.
      iIntros (LT Hl1) "H". unfold_oblP_fuel. iApply (oblP_fuel_val_mon with "H").      
      eapply measure_extend_alt; eauto.
    Qed.
    Lemma oblP_fuel_extend_val_list K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ list] k ∈ K, oblP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel_val k o).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply oblP_fuel_extend_val; eauto.
    Qed.
    Lemma oblP_fuel_extend_val_set K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ set] k ∈ K, oblP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel_val k o).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply oblP_fuel_extend_val; eauto.
    Qed.

    Lemma oblP_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      oblP_fuel k ℓ2 (▽)%M ⊢ |==> oblP_fuel k ℓ1 μ.
    Proof.
      iIntros (LT) "H". iMod (oblP_fuel_extend_val _ ℓ1 with "H") as "H"; last (unfold_oblP_fuel; by iFrame).
      1: auto.
      exists μ. apply η_mono.
    Qed.
    Lemma oblP_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, oblP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply oblP_fuel_extend; eauto.
    Qed.
    Lemma oblP_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, oblP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply oblP_fuel_extend; eauto.
    Qed.

    (** witP_bound rules *)
    Lemma witP_bound_mon k a0 a1 :
      (a0 <= a1)%ord → witP_bound k a0 ==∗ witP_bound k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_bound_mon.
    Qed.
    Lemma witP_bound_compare k a0 a1 :
      witP_bound k a0 -∗ witP_cred k a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_opreds. iIntros "(P& Be) (_& Cred)". iApply (witG_compare with "[$]").
    Qed.
    Lemma witP_bound_spend_gen k a0 a1 :
      witP_bound k a0 -∗ witP_cred k a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ witP_bound k a2.
    Proof.
      unfold_opreds. iIntros "($& Ow) (_& Oc)". iApply (witG_witness_spend_gen with "[$]").
    Qed.
    Lemma witP_bound_spend k a0 a1 :
      (Ord.O < a1)%ord →
      witP_bound k a0 -∗ witP_cred k a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ witP_bound k a2.
    Proof.
      unfold_opreds. iIntros (LT) "($& Ow) (_& Oc)". iApply (witG_witness_spend with "[$]"). done.
    Qed.
    Lemma witP_bound_spend_one k a :
      witP_bound k a -∗ witP_cred k Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ witP_bound k a0.
    Proof.
      iIntros "Ow Oc". iApply (witP_bound_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** witP_layer rules *)
    Lemma witP_layer_witP_bound k ℓ :
      witP_layer k ℓ -∗ ∃ μ, witP_bound k (η (measure ℓ μ)).
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

    (** thP_fuel_val rules *)
    Local Open Scope ord.

    Lemma thP_fuel_val_eq k a0 a1 :
      (a0 == a1) → thP_fuel_val k a0 = thP_fuel_val k a1.
    Proof.
      unfold_opreds. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
    Qed.
    Lemma thP_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, thP_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, thP_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite thP_fuel_val_eq; eauto. Qed.
    Lemma thP_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, thP_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, thP_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite thP_fuel_val_eq; eauto. Qed.

    Lemma thP_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → thP_fuel_val k a1 ==∗ thP_fuel_val k a0.
    Proof.
      unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
    Qed.
    Lemma thP_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, thP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_val_mon.
    Qed.
    Lemma thP_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, thP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_val_mon.
    Qed.

    Lemma thP_fuel_val_add k a0 a1 :
      thP_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ thP_fuel_val k a0 ∗ thP_fuel_val k a1.
    Proof.
      unfold_opreds. rewrite oblG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Lemma thP_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, thP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, thP_fuel_val k a0) ∗ ([∗ list] k ∈ K, thP_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply thP_fuel_val_add.
    Qed.
    Lemma thP_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, thP_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, thP_fuel_val k a0) ∗ ([∗ set] k ∈ K, thP_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply thP_fuel_val_add.
    Qed.

    Lemma thP_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → thP_fuel_val k a2 ==∗ thP_fuel_val k a0 ∗ thP_fuel_val k a1.
    Proof.
      unfold_opreds. iIntros (Hle) "(#Be& P)".
      iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma thP_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, thP_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k a0) ∗ ([∗ list] k ∈ K, thP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (thP_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply thP_fuel_val_add_list.
    Qed.
    Lemma thP_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, thP_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k a0) ∗ ([∗ set] k ∈ K, thP_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (thP_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply thP_fuel_val_add_set.
    Qed.

    Lemma thP_fuel_val_lt k a0 a1 :
      a0 < a1 →
      thP_fuel_val k a1 ⊢ |==> thP_fuel_val k a0 ∗ thP_fuel_val k Ord.one.
    Proof.
      unfold_opreds. iIntros (Hlt) "(#Be& P)".
      iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma thP_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, thP_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k a0) ∗ ([∗ list] k ∈ K, thP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_val_lt.
    Qed.
    Lemma thP_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, thP_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k a0) ∗ ([∗ set] k ∈ K, thP_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_val_lt.
    Qed.

    Lemma thP_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      thP_fuel_val k (b × a1)%ord ⊢ |==> thP_fuel_val k (b × a0) ∗ thP_fuel_val k b.
    Proof.
      unfold_opreds. intros LT. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (oblG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Lemma thP_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, thP_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, thP_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply thP_fuel_val_mult. auto.
    Qed.
    Lemma thP_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, thP_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, thP_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply thP_fuel_val_mult. auto.
    Qed.

    Lemma thP_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      thP_fuel_val k (b ↑ a1)%ord ⊢ |==> thP_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_opreds. intros LT Pos. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Lemma thP_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, thP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply thP_fuel_val_expn; auto.
    Qed.
    Lemma thP_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, thP_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply thP_fuel_val_expn; auto.
    Qed.

    (** thP_fuel rules *)
    Lemma thP_fuel_unfold k ℓ μ :
      thP_fuel k ℓ μ = thP_fuel_val k (measure ℓ μ).
    Proof. rewrite thP_fuel_unseal /thP_fuel_def. auto. Qed.

    Lemma thP_fuel_eq k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) → thP_fuel k ℓ1 μ1 = thP_fuel k ℓ2 μ2.
    Proof.
      unfold_thP_fuel. intros. rewrite (thP_fuel_val_eq k _ _ H); auto.
    Qed.
    Lemma thP_fuel_eq_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ list] k ∈ K, thP_fuel k ℓ1 μ1)%I ≡ ([∗ list] k ∈ K, thP_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite thP_fuel_eq; eauto. Qed.
    Lemma thP_fuel_eq_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ set] k ∈ K, thP_fuel k ℓ1 μ1)%I ≡ ([∗ set] k ∈ K, thP_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite thP_fuel_eq; eauto. Qed.

    Lemma thP_fuel_mon k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord → thP_fuel k ℓ2 μ2 ==∗ thP_fuel k ℓ1 μ1.
    Proof.
      unfold_thP_fuel. apply thP_fuel_val_mon.
    Qed.
    Lemma thP_fuel_mon_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, thP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_mon.
    Qed.
    Lemma thP_fuel_mon_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, thP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_mon.
    Qed.

    Lemma thP_fuel_mon_split k ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord → thP_fuel k ℓ3 μ3 ==∗ thP_fuel k ℓ1 μ1 ∗ thP_fuel k ℓ2 μ2.
    Proof.
      unfold_thP_fuel. apply thP_fuel_val_mon_split.
    Qed.
    Lemma thP_fuel_mon_split_list K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ list] k ∈ K, thP_fuel k ℓ3 μ3) ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, thP_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply thP_fuel_mon_split; auto.
    Qed.
    Lemma thP_fuel_mon_split_set K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ set] k ∈ K, thP_fuel k ℓ3 μ3) ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, thP_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply thP_fuel_mon_split; auto.
    Qed.

    Lemma thP_fuel_lt k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      thP_fuel k ℓ2 μ2 ⊢ |==> thP_fuel k ℓ1 μ1 ∗ thP_fuel k 0 1.
    Proof.
      unfold_thP_fuel. rewrite (thP_fuel_val_eq _ (measure (0 : layer) 1) Ord.one).
      1: apply thP_fuel_val_lt.
      rewrite measure_nat Ord.from_nat_1. done.
    Qed.
    Lemma thP_fuel_lt_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, thP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, thP_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_lt.
    Qed.
    Lemma thP_fuel_lt_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, thP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, thP_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply thP_fuel_lt.
    Qed.

    (* measurable syntax rules. *)
    Lemma thP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      thP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> thP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ thP_fuel k 0 1.
    Proof.
      intros. apply thP_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma thP_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, thP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply thP_fuel_embed. auto.
    Qed.
    Lemma thP_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, thP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply thP_fuel_embed. auto.
    Qed.

    Lemma thP_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      thP_fuel k ℓ (⫚)%M ⊢ |==> thP_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ thP_fuel k 0 1.
    Proof.
      intros. apply thP_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma thP_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, thP_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, thP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply thP_fuel_large.
    Qed.
    Lemma thP_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, thP_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, thP_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply thP_fuel_large.
    Qed.

    Lemma thP_fuel_add k ℓ μ1 μ2 :
      thP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ thP_fuel k ℓ μ1 ∗ thP_fuel k ℓ μ2.
    Proof.
      unfold_thP_fuel. rewrite measure_add. apply thP_fuel_val_add.
    Qed.
    Lemma thP_fuel_add_list K ℓ μ1 μ2 :
      ([∗ list] k ∈ K, thP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ list] k ∈ K, thP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, thP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply thP_fuel_add.
    Qed.
    Lemma thP_fuel_add_set K ℓ μ1 μ2 :
      ([∗ set] k ∈ K, thP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, thP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, thP_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply thP_fuel_add.
    Qed.

    Lemma thP_fuel_mult k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      thP_fuel k ℓ (s × μ2)%M ⊢ |==> thP_fuel k ℓ (s × μ1)%M ∗ thP_fuel k ℓ s.
    Proof.
      unfold_thP_fuel. intros LT. rewrite !measure_mult. apply thP_fuel_val_mult. auto.
    Qed.
    Lemma thP_fuel_mult_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ list] k ∈ K, thP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, thP_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply thP_fuel_mult. auto.
    Qed.
    Lemma thP_fuel_mult_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ set] k ∈ K, thP_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, thP_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply thP_fuel_mult. auto.
    Qed.

    Lemma thP_fuel_expn k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      thP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> thP_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_thP_fuel. intros LT Pos. rewrite !measure_mult !measure_expn. apply thP_fuel_val_expn; auto.
    Qed.
    Lemma thP_fuel_expn_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ list] k ∈ K, thP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply thP_fuel_expn; auto.
    Qed.
    Lemma thP_fuel_expn_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ set] k ∈ K, thP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply thP_fuel_expn; auto.
    Qed.

    Lemma thP_fuel_extend_val k ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      thP_fuel k ℓ2 (▽)%M ⊢ |==> thP_fuel_val k o.
    Proof.
      iIntros (LT Hl1) "H". unfold_thP_fuel. iApply (thP_fuel_val_mon with "H").      
      eapply measure_extend_alt; eauto.
    Qed.
    Lemma thP_fuel_extend_val_list K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ list] k ∈ K, thP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, thP_fuel_val k o).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply thP_fuel_extend_val; eauto.
    Qed.
    Lemma thP_fuel_extend_val_set K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ set] k ∈ K, thP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, thP_fuel_val k o).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply thP_fuel_extend_val; eauto.
    Qed.

    Lemma thP_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      thP_fuel k ℓ2 (▽)%M ⊢ |==> thP_fuel k ℓ1 μ.
    Proof.
      iIntros (LT) "H". iMod (thP_fuel_extend_val _ ℓ1 with "H") as "H"; last (unfold_thP_fuel; by iFrame).
      1: auto.
      exists μ. apply η_mono.
    Qed.
    Lemma thP_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, thP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, thP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply thP_fuel_extend; eauto.
    Qed.
    Lemma thP_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, thP_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, thP_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply thP_fuel_extend; eauto.
    Qed.

    (** thP_obls rules *)
    Lemma thP_obls_disj i G1 G2 q1 q2 :
      thP_obls i G1 q1 -∗ thP_obls i G2 q2 -∗ (⌜ G1 ## G2 ⌝).
    Proof.
      unfold_opreds. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H. auto.
    Qed.

    Lemma thP_obls_op_1 i G1 G2 q1 q2 :
      thP_obls i G1 q1 -∗ thP_obls i G2 q2 -∗ thP_obls i (G1 ∪ G2) (q1 + q2).
    Proof.
      unfold_opreds. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
      iPoseProof (othreadG_obls_op_1 with "[$T1 $T2]") as "T".
      iDestruct "Gx1" as "[Gx1 Gx1']". iDestruct "Gx2" as "[Gx2 Gx2']".
      iCombine "Gx1 Gx2" as "Gx". iCombine "Gx1' Gx2'" as "Gx'".
      iPoseProof (big_sepS_union with "[$Es1 $Es2]") as "$". 1: auto.
      iFrame "Ge1".
      rewrite -!Qp.div_add_distr. iCombine "Gx Gx'" as "Gx". rewrite -Qp.div_add_distr. iFrame "Gx".
      iFrame.
    Qed.
    Lemma thP_obls_op_2 i G1 G2 q1 q2 :
      G1 ## G2 →
      thP_obls i (G1 ∪ G2) (q1 + q2) -∗ (thP_obls i G1 q1 ∗ thP_obls i G2 q2).
    Proof.
      unfold_opreds. iIntros (Hd) "(#Ge& Gx& T& Es)".
      iPoseProof (othreadG_obls_op_2 with "T") as "[$ $]"; first auto.
      iDestruct "Gx" as "[Gx Gx']". rewrite !Qp.div_add_distr.
      iDestruct "Gx" as "[Gx1 Gx2]". iDestruct "Gx'" as "[Gx1' Gx2']".
      iCombine "Gx1 Gx1'" as "$". iCombine "Gx2 Gx2'" as "$".
      rewrite big_sepS_union. 2: auto.
      iFrame "Ge". iFrame.
    Qed.

    Lemma thP_term_obls_empty TP i :
      othread TP ∗ thP_term i ⊢ othreadG_obls i ∅ 1 ∗ (othreadG_obls i ∅ 1 -∗ othread TP).
    Proof. unfold_opreds. apply othread_term_open. Qed.

    Lemma thP_obls_alloc_threads Θ TP :
      Θ ## TP →
      othread TP ⊢ |==> othread (TP ∪ Θ) ∗ [∗ set] i ∈ Θ, thP_obls i ∅ 1.
    Proof.
      iIntros (Disj) "T". iMod (othread_alloc_threads with "T") as "[$ Ts]". 1: auto.
      unfold_opreds. iModIntro. iApply (big_sepS_impl with "Ts"). iIntros "!> %% ($& $& $)". done.
    Qed.


    (** obl_fuels rules *)
    Lemma obl_fuels_init α :
      ⊢ obl_fuels α ∅.
    Proof.
      unfold_opreds. rewrite big_sepM_empty. done.
    Qed.

    Lemma obl_fuels_add α F f ℓ ν μ :
      (α <= measure ℓ ν)%ord →
      obl_fuels α F -∗ oblP_fuel f ℓ (μ × ν)%M ==∗ obl_fuels α (<[f:=(ℓ, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite /obl_fuels.
      unfold_oblP_fuel. iMod (oblP_fuel_val_mon _ ((measure ℓ μ) × α)%ord with "Gf") as "Gf".
      { rewrite measure_mult. apply Jacobsthal.le_mult_r. auto. }
      iModIntro. iApply (big_sepM_insert_delete _ _ f).
      iFrame "Gf". destruct (F !! f) eqn:LUF.
      - iPoseProof (big_sepM_delete _ _ f with "Wfs") as "[_ $]". eauto.
      - rewrite delete_id; auto.
    Qed.

    Lemma obl_fuels_add_map α F (G : gmap oid (layer * measurable_syntax)) ν :
      obl_fuels α F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (α <= measure l ν)%ord ⌝ ∗ oblP_fuel g l (m × ν)%M) ==∗
      obl_fuels α (G ∪ F).
    Proof.
      revert α F. induction G using map_ind; intros; iIntros "Wfs Fs".
      { rewrite left_id_L. by iFrame. }
      rewrite big_sepM_insert; last auto.
      rename m into G. destruct x as (l& m). iDestruct "Fs" as "((%Lt& Gf)& Fs)".
      iMod (IHG with "Wfs Fs") as "Wfs".
      replace (<[i:=(l, m)]> G ∪ F) with (<[i:=(l, m)]> (G ∪ F)).
      { iApply (obl_fuels_add with "Wfs Gf"). auto. }
      by rewrite insert_union_l.
    Qed.

    Lemma obl_fuels_decr α α0 F :
      (α0 < α)%ord →
      obl_fuels α F ==∗
      (obl_fuels α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m)).
    Proof.
      rewrite /obl_fuels. iIntros (LT) "Fs".
      rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
      iIntros "!> % % % H". destruct x as (l& m).
      rewrite oblP_fuel_unseal /oblP_fuel_def. rewrite -oblP_fuel_val_add. iApply (oblP_fuel_val_mon with "H").
      rewrite Hessenberg.add_comm -Jacobsthal.mult_S.
      apply Jacobsthal.le_mult_r. apply Ord.S_supremum; auto.
    Qed.

    (** embed_fuels rules *)
    Lemma embed_fuels_init {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      ⊢ embed_fuels wf_ltA a ℓ ∅.
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def. apply obl_fuels_init.
    Qed.

    Lemma embed_fuels_add {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ1 F f ℓ2 μ :
      layer_leibniz_le ℓ1 ℓ2 →
      embed_fuels wf_ltA a ℓ1 F -∗ oblP_fuel f ℓ2 (μ × ⟪wf_ltA, a⟫)%M ==∗ embed_fuels wf_ltA a ℓ1 (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LE) "Wfs Gf". rewrite !embed_fuels_unseal /embed_fuels_def.
      iApply (obl_fuels_add with "Wfs Gf"). apply measure_layer_leibniz_le_proper. auto.
    Qed.

    Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
      a ℓ F (G : gmap oid (layer * measurable_syntax)) :
      embed_fuels wf_ltA a ℓ F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ layer_leibniz_le ℓ l ⌝ ∗ oblP_fuel g l (m × ⟪wf_ltA, a⟫)%M) ==∗
      embed_fuels wf_ltA a ℓ (G ∪ F).
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def.
      iIntros "Gfs Fs". iApply (obl_fuels_add_map with "Gfs [Fs]").
      iApply (big_sepM_impl with "Fs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. apply measure_layer_leibniz_le_proper. auto.
    Qed.

    Lemma embed_fuels_decr {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a a' ℓ F :
      ltA a' a →
      embed_fuels wf_ltA a ℓ F ==∗
      embed_fuels wf_ltA a' ℓ F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m).
    Proof.
      rewrite embed_fuels_unseal /embed_fuels_def.
      intros LT. apply (obl_fuels_decr). apply measure_embed_lt. auto.
    Qed.

    (** wit_fuels rules *)
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
      iExists μ. iApply witP_bound_mon; eauto.
    Qed.

    Lemma wit_fuels_add k ℓ1 α F f ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      wit_fuels k ℓ1 α F -∗ oblP_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wfs" as "(%& %& $& M)".
      iExists _. iSplitR; first eauto.
      iApply (obl_fuels_add with "M Gf").
      etrans; first eauto. apply measure_extend; auto.
    Qed.

    Lemma wit_fuels_add_map k ℓ α F (G : gmap oid (layer * measurable_syntax)) :
      wit_fuels k ℓ α F -∗
      ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (ℓ < l)%ordi ⌝ ∗ oblP_fuel g l (m × ▽)%M) ==∗
      wit_fuels k ℓ α (G ∪ F).
    Proof.
      rewrite !wit_fuels_unseal /wit_fuels_def.
      iIntros "(%& %& $& Fs) Gfs". iExists _. iSplitR; first eauto.
      iApply (obl_fuels_add_map _ _ _ (▽)%M with "Fs [Gfs]").
      iApply (big_sepM_impl with "Gfs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. etrans; first eauto. apply measure_extend. done.
    Qed.

    Lemma wit_fuels_decr k ℓ α F :
      wit_fuels k ℓ α F -∗ witP_cred k Ord.one ==∗
      ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗
            ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m).
    Proof.
      rewrite wit_fuels_unseal /wit_fuels_def. iIntros "(%& %& #Wbk& Fs) Wk".
      iMod (witP_bound_spend_one with "Wbk Wk") as "(%& %& #Wbk2)".
      iExists a0. iSplitR; first done. iFrame "Wbk2". assert (a0 <= η (measure ℓ μ)).
      { etransitivity; last eauto. apply WFOCM.lt_le. auto. }
      iFrame (H1).
      iApply (obl_fuels_decr with "Fs"). auto.
    Qed.

  End liveness_preds.

  Section fmupd.

    Lemma obl_alloc_assigned_mupd n Θ i G q b ℓ μ :
      thP_obls i G q -∗
      |=[n,Θ]=>m ∃ k, (⌜ k ∉ G ⌝) ∗
                     thP_obls i ({[k]} ∪ G) q ∗
                     oblP_assigned k b (1/2)%Qp ∗
                     oblP_layer k ℓ ∗
                     oblP_id k ∗
                     oblP_fuel k ℓ μ ∗
                     witP_layer k ℓ ∗
                     (∀ E N (P Q R : iProp Σ), (▷ (if b then Q else P)) ={E}=∗ oblP_inv N k P Q R).
    Proof.
      unfold_opreds. iIntros "(#Oe& Ox& Ob& OS)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (osat_alloc_obl_assigned _ k b ℓ μ i with "S") as "(S& #Gwf& #Ge& Gl& Gf& Go& %OStep)".
      1: auto.
      iDestruct "Gl" as "[Gl0 Gl1]".
      iMod (othread_alloc_obl with "[$S $O $Ob $Ge $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iMod (owit_alloc_witness_assigned _ k (η (measure ℓ μ)) with "W") as "(W& #Ww)".
      { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo0 [Oo1 Oo']]".
      iPoseProof (oassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. auto. }
      iDestruct "Gl0" as "[Gl0 Gl0']". iDestruct "Gl1" as "[Gl1 Gl1']".
      iCombine "Gl0 Gl1" as "Gl". iCombine "Gl0' Gl1'" as "Gl'".
      set (Ω2:=(<[k:=(obl_assigned (OC:=ord_obl_class) (measure ℓ μ) i)]> Ω1)).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
      iModIntro. iExists Ω2. iSplitR.
      { subst Ω2. iPureIntro. econstructor 2. econstructor 2. eauto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (owit_inv_alloc_assigned Ω1 k W1 NinOk1 GWI _ _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O W". iSplitL "A".
      { subst Ω2. rewrite dom_insert_L. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Oe Gwf Ge Ww Gf Ox Gl'". iSplitR. 1: auto.
      iSplitL "Ob OS Go Oo0 Oo1".
      { iFrame "Ob". iApply big_sepS_union. 1: set_solver.
        rewrite big_sepS_singleton. iFrame "OS Ge Go". iCombine "Oo0 Oo1" as "$". }
      iIntros (E N P Q R) "HP". destruct b.
      - iMod (oblG_inv_alloc_assigned_true _ N _ _ P Q R with "[$Gl $HP]") as "#GVar". by iModIntro.
      - iMod (oblG_inv_alloc_assigned_false _ N _ _ P Q R with "[$Gl $HP]") as "#GVar". by iModIntro.
    Qed.

    Lemma obl_alloc_fulfilled_mupd n Θ ℓ μ :
      ⊢ |=[n,Θ]=>m ∃ k, oblP_fulfilled k ∗ oblP_layer k ℓ ∗ oblP_id k ∗ oblP_fuel k ℓ μ ∗
                       witP_layer k ℓ ∗
                       (∀ E N (P Q R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P Q R).
    Proof.
      unfold_opreds.
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (osat_alloc_obl_fulfilled _ k ℓ μ with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)".
      { auto. }
      iMod (owit_alloc_witness_fulfilled _ k (η (measure ℓ μ)) with "[$W $Gu]") as "(W& #Ww)".
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
      rewrite /model_interp. iFrame "HI S O W". iSplitL "A".
      { subst Ω2. rewrite dom_insert_L. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Gwf Ge Ww Gf Gu".
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
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI1)".
      iMod (osat_assigned_to_true with "[$S $Ge $Ga]") as "(S& Ga)".
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI1 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O W A". iSplitR; eauto.
      iDestruct "Ga" as "[[Ga1 Ga2] [Ga1' Ga2']]". iCombine "Ga1 Ga1'" as "Ga1". iCombine "Ga2 Ga2'" as "Ga2".
      iFrame "Ge Ga1". iIntros "!> !> HQR". iApply "ACC". iNext. iRight. iLeft. iFrame.
    Qed.

    Lemma obl_fulfill_mupd E N k P Q R :
      ↑N ⊆ E →
      oblP_inv N k P Q R -∗
      |={E,E ∖ ↑N}=> ∀ i G q1 q2,
      (⌜k ∈ G⌝) → thP_obls i G q1 -∗ oblP_assigned k true q2 -∗
      ((▷ (thP_obls i G q1 ∗ oblP_assigned k true q2 ∗ oblP_assigned k true (1/2) ∗ Q)) ∗
       (thP_obls i G q1 -∗
        oblP_assigned k true 1 -∗
        ∀ n Θ, |=[n,Θ]=>m (thP_obls i (G ∖ {[k]}) q1 ∗ oblP_fulfilled k) ∗
                       ((▷ (R)) ={E ∖ ↑N,E}=∗ True))).
    Proof.
      unfold_opreds. iIntros (MASK) "(#Ge& #Gvar)".
      iMod (oblG_inv_acc_assigned with "Gvar") as "H". 1: auto.
      iIntros "!> %%%% %LUGk (#Oe& Ox& Ob& OS) (_& Ga)". iPoseProof ("H" with "Ga") as "[H ACC]".
      iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
      iSplitL "Ox Ob Go Oo OS H".
      { iNext. iFrame "Oe Ox Ob". iDestruct "H" as "(Gl& $& $)".
        rewrite (big_sepS_delete _ _ _ LUGk). iFrame. iFrame "Ge". }
      iIntros "(_& Ox& Ob& OS) (_& Gl) %%".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
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
      iMod (othread_delete_obl_frac with "[$O $Ob $Oo]") as "(O& Ob& Go2)".
      { auto. }
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
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
      rewrite /model_interp. iFrame "HI S O W". iSplitL "A".
      { iModIntro. subst Ω2. rewrite dom_insert_L.
        replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)).
        { iFrame. eauto. }
        apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
      iApply fupd_intro. iIntros "!>". iFrame "Oe Ge Gu Ox".
      iSplitR "ACC".
      { iFrame. }
      iIntros "HQ". iMod ("ACC" with "[HQ]") as "_".
      { iNext. iRight. iFrame. eauto. }
      done.
    Qed.

    Lemma obl_change_owner_mupd n Θ i1 i2 G1 G2 q1 q2 k ℓ0 :
      k ∈ G1 →
      thP_obls i1 G1 q1 -∗
      thP_obls i2 G2 q2 -∗
      oblP_fuel k ℓ0 1 -∗
      |=[n,Θ]=>m thP_obls i1 (G1 ∖ {[k]}) q1 ∗ thP_obls i2 ({[k]} ∪ G2) q2 ∗ ⌜ k ∉ G2 ⌝.
    Proof.
      unfold_opreds. iIntros (LUGk) "(#Oe1& Ox1& Ob1& OS1) (#Oe2& Ox2& Ob2& OS2) (#Ge& Gf)".
      rewrite (oblG_fuel_eq _ _ Ord.one); cycle 1.
      { rewrite measure_nat Ord.from_nat_1. done. }
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
      iPoseProof (big_sepS_delete _ _ _ LUGk with "OS1") as "[(_& Go& Oo) OS1]".
      iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1o as (?&LUO1o). rename x into a.
      iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
      { apply elem_of_dom. eauto. }
      2:{ iExFalso. iPoseProof (osat_lookup_fulfilled with "[$S $Ge $Gu]") as "%". rewrite H in LUO1o; done. }
      iPoseProof (oblG_owner_agree _ i0 i1 with "[$Go $Go1]") as "%". destruct H as [-> _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (othread_delete_obl_frac with "[$O $Ob1 $Oo]") as "(O& Ob1& Go2)".
      { auto. }
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
      iMod (osat_progress_one_owner _ _ _ _ i2 with "[$S $Go $Gf]") as "(%& S& Go& %Gstep)".
      1: eauto.
      1: apply Ord.S_lt.
      iMod (othread_alloc_obl with "[$S $O $Ob2 $Ge $Go]") as "(S& O& %NinkG2& Ob2& Oo& Go)".
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
      iPoseProof (oassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. auto. }
      set (Ω2:=(<[k:=(obl_assigned a' i2)]> Ω1)).
      assert (Gstep' : obl_step (obl_assigned a i1) (obl_assigned a' i2)) by (by econstructor 1).
      iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
      { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }            
      iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_progress_owner _ k _ _ _ LUO1o GWI _ _ Gstep' W2 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O W". iSplitL "A".
      { iModIntro. subst Ω2. rewrite dom_insert_L.
        replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)).
        { iFrame. eauto. }
        apply elem_of_dom_2 in LUO1o. rewrite -union_difference_L; set_solver. }
      iIntros "!> !>". iFrame "Oe1 Oe2 Ox1 Ox2 OS1".
      iFrame "Ob1 Ob2". iSplitL; last auto.
      iApply big_sepS_union. 1: set_solver. rewrite big_sepS_singleton. iFrame. iCombine "Oo Oo1" as "Oo". eauto.
    Qed.

    Lemma obl_terminate_mupd n Θ i :
      thP_obls i ∅ 1 -∗ |=[n,Θ]=>m thP_term i.
    Proof.
      unfold_opreds. iIntros "(#Oe& Ox& Ob& OS)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
      iMod (othread_exec_to_term with "[$O $Ox $Ob]") as "[O #Ot]".
      iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
      iModIntro. iExists Ω1. iSplitR; first done.
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "HI S O W A". iSplitR; eauto.
      iIntros "!> !>". auto.
    Qed.

    Lemma obl_check_witnesses_mupd n Θ (R : oids) :
      ([∗ set] r ∈ R, oblP_id r) -∗
      |=[n,Θ]=>m ([∗ set] r ∈ R, witP_cred r Ord.O ∨ oblP_fulfilled r).
    Proof.
      unfold_opreds. iIntros "#REs".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI1)".
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
      rewrite /model_interp. iFrame "HI S O W A". iSplitR; eauto.
      iIntros "!> !>". iApply (big_sepS_impl with "Rs"). iIntros "!> %% (#Ge& [Ww | Gf])".
      - iLeft. eauto.
      - iRight. eauto.
    Qed.

    (** Variant access rules *)
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
