From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.algebra Require Import ordinal_wfocm.
From liris.base_logic Require Export mupd oinv.

(** Obligation predicates. *)
(** All Local Definitions are only for internal uses and users should not need them. *)
Local Definition obl_layer_def `{SI : indexT} `{@mupdGS SI Σ}
  k ℓ : iProp Σ :=
  oblG_layer k ℓ.
Local Definition obl_layer_aux : seal (@obl_layer_def). Proof. by eexists. Qed.
Definition obl_layer := obl_layer_aux.(unseal).
Local Definition obl_layer_unseal :
  @obl_layer = @obl_layer_def := obl_layer_aux.(seal_eq).
Global Arguments obl_layer {SI Σ _}.

Local Definition obl_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  oblG_elem k.
Local Definition obl_aux : seal (@obl_def). Proof. by eexists. Qed.
Definition obl := obl_aux.(unseal).
Local Definition obl_unseal :
  @obl = @obl_def := obl_aux.(seal_eq).
Global Arguments obl {SI Σ _}.

Local Definition obl_assigned_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  obl k ∗ oblG_assigned k (1 / 2 / 2 / 2 / 2).
Local Definition obl_assigned_aux : seal (@obl_assigned_def). Proof. by eexists. Qed.
Definition obl_assigned := obl_assigned_aux.(unseal).
Local Definition obl_assigned_unseal :
  @obl_assigned = @obl_assigned_def := obl_assigned_aux.(seal_eq).
Global Arguments obl_assigned {SI Σ _}.

Local Definition obl_fulfilled_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  obl k ∗ oblG_fulfilled k.
Local Definition obl_fulfilled_aux : seal (@obl_fulfilled_def). Proof. by eexists. Qed.
Definition obl_fulfilled := obl_fulfilled_aux.(unseal).
Local Definition obl_fulfilled_unseal :
  @obl_fulfilled = @obl_fulfilled_def := obl_fulfilled_aux.(seal_eq).
Global Arguments obl_fulfilled {SI Σ _}.

Local Definition obl_alive_def `{SI : indexT} `{@mupdGS SI Σ}
  k q : iProp Σ :=
  obl k ∗ oblG_alive k (q/2 + q/2/2)%Qp.
Local Definition obl_alive_aux : seal (@obl_alive_def). Proof. by eexists. Qed.
Definition obl_alive := obl_alive_aux.(unseal).
Local Definition obl_alive_unseal :
  @obl_alive = @obl_alive_def := obl_alive_aux.(seal_eq).
Global Arguments obl_alive {SI Σ _}.

Local Definition obl_expired_def `{SI : indexT} `{@mupdGS SI Σ}
  k : iProp Σ :=
  obl_fulfilled k ∗ oblG_expired k.
Local Definition obl_expired_aux : seal (@obl_expired_def). Proof. by eexists. Qed.
Definition obl_expired := obl_expired_aux.(unseal).
Local Definition obl_expired_unseal :
  @obl_expired = @obl_expired_def := obl_expired_aux.(seal_eq).
Global Arguments obl_expired {SI Σ _}.

Local Definition obl_fuel_val `{SI : indexT} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  obl k ∗ oblG_fuel k α.

Local Definition obl_fuel_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ μ : iProp Σ :=
  obl_fuel_val k (measure ℓ μ).
Local Definition obl_fuel_aux : seal (@obl_fuel_def). Proof. by eexists. Qed.
Definition obl_fuel := obl_fuel_aux.(unseal).
Local Definition obl_fuel_unseal :
  @obl_fuel = @obl_fuel_def := obl_fuel_aux.(seal_eq).
Global Arguments obl_fuel {SI Σ _ _}.

Local Definition obl_inv_def `{SI : indexT} `{@mupdGS SI Σ}
  N k (P Q R : iProp Σ) : iProp Σ :=
  obl k ∗ oblG_inv N k (1/2/2/2/2)%Qp P Q R.
Local Definition obl_inv_aux : seal (@obl_inv_def). Proof. by eexists. Qed.
Definition obl_inv := obl_inv_aux.(unseal).
Local Definition obl_inv_unseal :
  @obl_inv = @obl_inv_def := obl_inv_aux.(seal_eq).
Global Arguments obl_inv {SI Σ _}.

Local Definition obl_variant_def `{SI : indexT} `{@mupdGS SI Σ}
  k (P Q R : iProp Σ) : iProp Σ :=
  ((obl_assigned k ∗ P) ∨ (obl_fulfilled k ∗ (Q ∨ obl_expired k) ∗ R))%I.
Local Definition obl_variant_aux : seal (@obl_variant_def). Proof. by eexists. Qed.
Definition obl_variant := obl_variant_aux.(unseal).
Local Definition obl_variant_unseal :
  @obl_variant = @obl_variant_def := obl_variant_aux.(seal_eq).
Global Arguments obl_variant {SI Σ _}.

(* Thread obligations *)
Local Definition th_obls_def `{SI : indexT} `{@mupdGS SI Σ}
  i (G : oids) q : iProp Σ :=
  othreadG_elem i ∗ othreadG_exec i (q/2 + q/2/2)%Qp ∗ othreadG_obls i G q ∗
  ([∗ set] k ∈ G,
     obl k ∗ oblG_assigned k (1/2 + 1/2/2/2/2)%Qp ∗ obl_alive k (1/2)%Qp ∗
     oblG_owner k i (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns i k (1/2 + 1/2/2)%Qp).
Local Definition th_obls_aux : seal (@th_obls_def). Proof. by eexists. Qed.
Definition th_obls := th_obls_aux.(unseal).
Local Definition th_obls_unseal :
  @th_obls = @th_obls_def := th_obls_aux.(seal_eq).
Global Arguments th_obls {SI Σ _}.

Local Definition th_term_def `{SI : indexT} `{@mupdGS SI Σ}
  i : iProp Σ :=
  othreadG_elem i ∗ othreadG_term i.
Local Definition th_term_aux : seal (@th_term_def). Proof. by eexists. Qed.
Definition th_term := th_term_aux.(unseal).
Local Definition th_term_unseal :
  @th_term = @th_term_def := th_term_aux.(seal_eq).
Global Arguments th_term {SI Σ _}.

(* Obligation witnesses *)
Local Definition wit_bound_def `{SI : indexT} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  obl k ∗ witG_bound k α.
Local Definition wit_bound_aux : seal (@wit_bound_def). Proof. by eexists. Qed.
Local Definition wit_bound := wit_bound_aux.(unseal).
Local Definition wit_bound_unseal :
  @wit_bound = @wit_bound_def := wit_bound_aux.(seal_eq).
Global Arguments wit_bound {SI Σ _}.

Local Definition wit_layer_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ : iProp Σ :=
  ∃ μ, wit_bound k (η (measure ℓ μ)).
Local Definition wit_layer_aux : seal (@wit_layer_def). Proof. by eexists. Qed.
Definition wit_layer := wit_layer_aux.(unseal).
Local Definition wit_layer_unseal :
  @wit_layer = @wit_layer_def := wit_layer_aux.(seal_eq).
Global Arguments wit_layer {SI Σ _ _}.

Local Definition wit_def `{SI : indexT} `{@mupdGS SI Σ}
  k a : iProp Σ :=
  obl k ∗ witG_witness k a.
Local Definition wit_aux : seal (@wit_def). Proof. by eexists. Qed.
Definition wit := wit_aux.(unseal).
Local Definition wit_unseal :
  @wit = @wit_def := wit_aux.(seal_eq).
Global Arguments wit {SI Σ _}.

(* Collection of fuels to support induction rules *)
Local Definition obl_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  α (F : gmap oid (layer * measurable_syntax)) : iProp Σ :=
  ([∗ map] f ↦ '(l, m) ∈ F, obl_fuel_val f ((measure l m) × α)%ord).
Local Definition obl_fuels_aux : seal (@obl_fuels_def). Proof. by eexists. Qed.
Definition obl_fuels := obl_fuels_aux.(unseal).
Local Definition obl_fuels_unseal :
  @obl_fuels = @obl_fuels_def := obl_fuels_aux.(seal_eq).
Global Arguments obl_fuels {SI Σ _ _}.

Local Definition embed_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (a : A) ℓ (F : gmap oid (layer * measurable_syntax)) : iProp Σ :=
  obl_fuels (measure ℓ (⟪wf_ltA, a⟫)%M) F.
Local Definition embed_fuels_aux : seal (@embed_fuels_def). Proof. by eexists. Qed.
Definition embed_fuels := embed_fuels_aux.(unseal).
Local Definition embed_fuels_unseal :
  @embed_fuels = @embed_fuels_def := embed_fuels_aux.(seal_eq).
Global Arguments embed_fuels {SI Σ _ _ A ltA}.

Local Definition wit_fuels_def `{SI : indexT} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ α (F : gmap oid (layer * measurable_syntax)) : iProp Σ :=
  ∃ μ, ⌜ (α <= η (measure ℓ μ))%ord ⌝ ∗ wit_bound k α ∗
       obl_fuels α F.
Local Definition wit_fuels_aux : seal (@wit_fuels_def). Proof. by eexists. Qed.
Definition wit_fuels := wit_fuels_aux.(unseal).
Local Definition wit_fuels_unseal :
  @wit_fuels = @wit_fuels_def := wit_fuels_aux.(seal_eq).
Global Arguments wit_fuels {SI Σ _ _}.

Section preds.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Local Ltac unfold_defs :=
    try rewrite !wit_fuels_unseal /wit_fuels_def;
    try rewrite !embed_fuels_unseal /embed_fuels_def;
    try rewrite !obl_fuels_unseal /obl_fuels_def;
    try rewrite !wit_unseal /wit_def;
    try rewrite !wit_layer_unseal /wit_layer_def;
    try rewrite !wit_bound_unseal /wit_bound_def;
    try rewrite !th_term_unseal /th_term_def;
    try rewrite !th_obls_unseal /th_obls_def;
    try rewrite !obl_variant_unseal /obl_variant_def;
    try rewrite !obl_inv_unseal /obl_inv_def;
    try rewrite !obl_fuel_unseal /obl_fuel_def;
    (* try rewrite !obl_fuel_val_unseal /obl_fuel_val_def; *)
    try rewrite /obl_fuel_val;
    try rewrite !obl_expired_unseal /obl_expired_def;
    try rewrite !obl_alive_unseal /obl_alive_def;
    try rewrite !obl_fulfilled_unseal /obl_fulfilled_def;
    try rewrite !obl_assigned_unseal /obl_assigned_def;
    try rewrite !obl_layer_unseal /obl_layer_def;
    try rewrite !obl_unseal /obl_def.

  Local Ltac unfold_obl_fuel :=
    try rewrite !obl_fuel_unseal /obl_fuel_def.

  Section liveness_preds.

    (** Instances *)
    Global Instance obl_persistent k : Persistent (obl k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_layer_persistent k ℓ : Persistent (obl_layer k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fulfilled_persistent k : Persistent (obl_fulfilled k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_expired_persistent k : Persistent (obl_expired k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_inv_persistent N k P Q R : Persistent (obl_inv N k P Q R).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_persistent i : Persistent (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_bound_persistent k α : Persistent (wit_bound k α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_layer_persistent k ℓ : Persistent (wit_layer k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fuels_empty_persistent α : Persistent (obl_fuels α ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance embed_fuels_empty_persistent {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Persistent (embed_fuels wf_ltA a ℓ ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_fuels_empty_persistent k ℓ α : Persistent (wit_fuels k ℓ α ∅).
    Proof. unfold_defs. apply _. Qed.

    Global Instance obl_timeless k : Timeless (obl k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_layer_timeless k ℓ : Timeless (obl_layer k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_assigned_timeless k : Timeless (obl_assigned k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fulfilled_timeless k : Timeless (obl_fulfilled k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_alive_timeless k q : Timeless (obl_alive k q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_expired_timeless k : Timeless (obl_expired k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fuel_val_timeless k α : Timeless (obl_fuel_val k α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fuel_timeless k ℓ μ : Timeless (obl_fuel k ℓ μ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_variant_timeless k P Q R :
      Timeless P → Timeless Q → Timeless R →
      Timeless (obl_variant k P Q R).
    Proof. intros. unfold_defs. apply _. Qed.
    Global Instance th_obls_timeless i G q : Timeless (th_obls i G q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_timeless i : Timeless (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_bound_timeless k α : Timeless (wit_bound k α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_layer_timeless k ℓ : Timeless (wit_layer k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_timeless k a : Timeless (wit k a).
    Proof. unfold_defs. apply _. Qed.
    Global Instance obl_fuels_timeless α F : Timeless (obl_fuels α F).
    Proof. unfold_defs. apply _. Qed.
    Global Instance embed_fuels_empty_timeless {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Timeless (embed_fuels wf_ltA a ℓ ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_fuels_timeless k ℓ α F : Timeless (wit_fuels k ℓ α F).
    Proof. unfold_defs. apply _. Qed.

    Global Instance obl_inv_contractive_1 N k Q R : Contractive (λ P, obl_inv N k P Q R).
    Proof.
      unfold_defs. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.
    Global Instance obl_inv_contractive_2 N k P R : Contractive (λ Q, obl_inv N k P Q R).
    Proof.
      unfold_defs. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.
    Global Instance obl_inv_contractive_3 N k P Q : Contractive (λ R, obl_inv N k P Q R).
    Proof.
      unfold_defs. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
    Qed.

    Global Instance obl_inv_ne_1 N k Q R : NonExpansive (λ P, obl_inv N k P Q R).
    Proof. apply _. Qed.
    Global Instance obl_inv_ne_2 N k P R : NonExpansive (λ Q, obl_inv N k P Q R).
    Proof. apply _. Qed.
    Global Instance obl_inv_ne_3 N k P Q : NonExpansive (λ R, obl_inv N k P Q R).
    Proof. apply _. Qed.

    Global Instance obl_inv_proper_1 N k Q R : Proper (equiv ==> equiv) (λ P, obl_inv N k P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.
    Global Instance obl_inv_proper_2 N k P R : Proper (equiv ==> equiv) (λ Q, obl_inv N k P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.
    Global Instance obl_inv_proper_3 N k P Q : Proper (equiv ==> equiv) (λ R, obl_inv N k P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
    Qed.

    Global Instance obl_alive_fractional k : Fractional (obl_alive k).
    Proof.
      rewrite !obl_alive_unseal /obl_alive_def. intros p q. iSplit.
      - iIntros "(#$& [Gv1 Gv2])". rewrite !Qp.div_add_distr.
        iDestruct "Gv1" as "[Gv1 Gv1']". iDestruct "Gv2" as "[Gv2 Gv2']".
        iCombine "Gv1 Gv2" as "$". iCombine "Gv1' Gv2'" as "$".
      - iIntros "((#$& [Gv1 Gv2])& _& [Gv3 Gv4])". rewrite !Qp.div_add_distr.
        iCombine "Gv1 Gv3" as "Gv1". iSplitL "Gv1"; iFrame. iSplitR "Gv4"; iFrame.
    Qed.
    Global Instance obl_alive_as_fractional k q : AsFractional (obl_alive k q) (obl_alive k) q.
    Proof. split; [auto|apply _]. Qed.

    (** obl_assigned and obl_fulfilled rules *)
    Lemma obl_assigned_fulfilled_false k :
      obl_assigned k -∗ obl_fulfilled k -∗ False.
    Proof.
      unfold_defs. iIntros "(#Ge& Gl) (_& #Gu)".
      iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    Qed.

    (** obl_alive and obl_expired rules *)
    Lemma obl_alive_expired_false k q :
      obl_alive k q -∗ obl_expired k -∗ False.
    Proof.
      unfold_defs. iIntros "(#Ge& Gv) (_& #Gve)".
      iPoseProof (oblG_alive_expired_false with "[$]") as "%". done.
    Qed.

    Local Open Scope ord.

    (** obl_fuel_val rules *)
    Lemma obl_fuel_val_eq k a0 a1 :
      (a0 == a1) → obl_fuel_val k a0 = obl_fuel_val k a1.
    Proof.
      unfold_defs. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
    Qed.
    Lemma obl_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, obl_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, obl_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite obl_fuel_val_eq; eauto. Qed.
    Lemma obl_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, obl_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, obl_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite obl_fuel_val_eq; eauto. Qed.

    Lemma obl_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → obl_fuel_val k a1 ==∗ obl_fuel_val k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
    Qed.
    Lemma obl_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, obl_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_val_mon.
    Qed.
    Lemma obl_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, obl_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_val_mon.
    Qed.

    Lemma obl_fuel_val_add k a0 a1 :
      obl_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ obl_fuel_val k a0 ∗ obl_fuel_val k a1.
    Proof.
      unfold_defs. rewrite oblG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Lemma obl_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, obl_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, obl_fuel_val k a0) ∗ ([∗ list] k ∈ K, obl_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply obl_fuel_val_add.
    Qed.
    Lemma obl_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, obl_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, obl_fuel_val k a0) ∗ ([∗ set] k ∈ K, obl_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply obl_fuel_val_add.
    Qed.

    Lemma obl_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → obl_fuel_val k a2 ==∗ obl_fuel_val k a0 ∗ obl_fuel_val k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma obl_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, obl_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k a0) ∗ ([∗ list] k ∈ K, obl_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (obl_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply obl_fuel_val_add_list.
    Qed.
    Lemma obl_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, obl_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k a0) ∗ ([∗ set] k ∈ K, obl_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (obl_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply obl_fuel_val_add_set.
    Qed.

    Lemma obl_fuel_val_lt k a0 a1 :
      a0 < a1 →
      obl_fuel_val k a1 ⊢ |==> obl_fuel_val k a0 ∗ obl_fuel_val k Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)".
      iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma obl_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, obl_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k a0) ∗ ([∗ list] k ∈ K, obl_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_val_lt.
    Qed.
    Lemma obl_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, obl_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k a0) ∗ ([∗ set] k ∈ K, obl_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_val_lt.
    Qed.

    Lemma obl_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      obl_fuel_val k (b × a1)%ord ⊢ |==> obl_fuel_val k (b × a0) ∗ obl_fuel_val k b.
    Proof.
      unfold_defs. intros LT. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (oblG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Lemma obl_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, obl_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, obl_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply obl_fuel_val_mult. auto.
    Qed.
    Lemma obl_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, obl_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, obl_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply obl_fuel_val_mult. auto.
    Qed.

    Lemma obl_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      obl_fuel_val k (b ↑ a1)%ord ⊢ |==> obl_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_defs. intros LT Pos. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (oblG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Lemma obl_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, obl_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply obl_fuel_val_expn; auto.
    Qed.
    Lemma obl_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, obl_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply obl_fuel_val_expn; auto.
    Qed.

    (** obl_fuel rules *)
    Lemma obl_fuel_unfold k ℓ μ :
      obl_fuel k ℓ μ = obl_fuel_val k (measure ℓ μ).
    Proof. rewrite obl_fuel_unseal /obl_fuel_def. auto. Qed.

    Lemma obl_fuel_eq k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) → obl_fuel k ℓ1 μ1 = obl_fuel k ℓ2 μ2.
    Proof.
      unfold_obl_fuel. intros. rewrite (obl_fuel_val_eq k _ _ H); auto.
    Qed.
    Lemma obl_fuel_eq_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ list] k ∈ K, obl_fuel k ℓ1 μ1)%I ≡ ([∗ list] k ∈ K, obl_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite obl_fuel_eq; eauto. Qed.
    Lemma obl_fuel_eq_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ set] k ∈ K, obl_fuel k ℓ1 μ1)%I ≡ ([∗ set] k ∈ K, obl_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite obl_fuel_eq; eauto. Qed.

    Lemma obl_fuel_mon k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord → obl_fuel k ℓ2 μ2 ==∗ obl_fuel k ℓ1 μ1.
    Proof.
      unfold_obl_fuel. apply obl_fuel_val_mon.
    Qed.
    Lemma obl_fuel_mon_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, obl_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_mon.
    Qed.
    Lemma obl_fuel_mon_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, obl_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_mon.
    Qed.

    Lemma obl_fuel_mon_split k ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord → obl_fuel k ℓ3 μ3 ==∗ obl_fuel k ℓ1 μ1 ∗ obl_fuel k ℓ2 μ2.
    Proof.
      unfold_obl_fuel. apply obl_fuel_val_mon_split.
    Qed.
    Lemma obl_fuel_mon_split_list K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ list] k ∈ K, obl_fuel k ℓ3 μ3) ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, obl_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply obl_fuel_mon_split; auto.
    Qed.
    Lemma obl_fuel_mon_split_set K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ set] k ∈ K, obl_fuel k ℓ3 μ3) ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, obl_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply obl_fuel_mon_split; auto.
    Qed.

    Lemma obl_fuel_lt k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      obl_fuel k ℓ2 μ2 ⊢ |==> obl_fuel k ℓ1 μ1 ∗ obl_fuel k 0 1.
    Proof.
      unfold_obl_fuel. rewrite (obl_fuel_val_eq _ (measure (0 : layer) 1) Ord.one).
      1: apply obl_fuel_val_lt.
      rewrite measure_nat Ord.from_nat_1. done.
    Qed.
    Lemma obl_fuel_lt_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, obl_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, obl_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_lt.
    Qed.
    Lemma obl_fuel_lt_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, obl_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, obl_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply obl_fuel_lt.
    Qed.

    (* measurable syntax rules. *)
    Lemma obl_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      obl_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> obl_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ obl_fuel k 0 1.
    Proof.
      intros. apply obl_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma obl_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, obl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply obl_fuel_embed. auto.
    Qed.
    Lemma obl_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, obl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply obl_fuel_embed. auto.
    Qed.

    Lemma obl_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      obl_fuel k ℓ (⫚)%M ⊢ |==> obl_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ obl_fuel k 0 1.
    Proof.
      intros. apply obl_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma obl_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, obl_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, obl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply obl_fuel_large.
    Qed.
    Lemma obl_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, obl_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, obl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply obl_fuel_large.
    Qed.

    Lemma obl_fuel_add k ℓ μ1 μ2 :
      obl_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ obl_fuel k ℓ μ1 ∗ obl_fuel k ℓ μ2.
    Proof.
      unfold_obl_fuel. rewrite measure_add. apply obl_fuel_val_add.
    Qed.
    Lemma obl_fuel_add_list K ℓ μ1 μ2 :
      ([∗ list] k ∈ K, obl_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ list] k ∈ K, obl_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, obl_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply obl_fuel_add.
    Qed.
    Lemma obl_fuel_add_set K ℓ μ1 μ2 :
      ([∗ set] k ∈ K, obl_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, obl_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, obl_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply obl_fuel_add.
    Qed.

    Lemma obl_fuel_mult k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      obl_fuel k ℓ (s × μ2)%M ⊢ |==> obl_fuel k ℓ (s × μ1)%M ∗ obl_fuel k ℓ s.
    Proof.
      unfold_obl_fuel. intros LT. rewrite !measure_mult. apply obl_fuel_val_mult. auto.
    Qed.
    Lemma obl_fuel_mult_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ list] k ∈ K, obl_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, obl_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply obl_fuel_mult. auto.
    Qed.
    Lemma obl_fuel_mult_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ set] k ∈ K, obl_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, obl_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply obl_fuel_mult. auto.
    Qed.

    Lemma obl_fuel_expn k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      obl_fuel k ℓ (s ↑ μ2)%M ⊢ |==> obl_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_obl_fuel. intros LT Pos. rewrite !measure_mult !measure_expn. apply obl_fuel_val_expn; auto.
    Qed.
    Lemma obl_fuel_expn_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ list] k ∈ K, obl_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply obl_fuel_expn; auto.
    Qed.
    Lemma obl_fuel_expn_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ set] k ∈ K, obl_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply obl_fuel_expn; auto.
    Qed.

    Lemma obl_fuel_extend_val k ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      obl_fuel k ℓ2 (▽)%M ⊢ |==> obl_fuel_val k o.
    Proof.
      iIntros (LT Hl1) "H". unfold_obl_fuel. iApply (obl_fuel_val_mon with "H").      
      eapply measure_extend_alt; eauto.
    Qed.
    Lemma obl_fuel_extend_val_list K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ list] k ∈ K, obl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, obl_fuel_val k o).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply obl_fuel_extend_val; eauto.
    Qed.
    Lemma obl_fuel_extend_val_set K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ set] k ∈ K, obl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, obl_fuel_val k o).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply obl_fuel_extend_val; eauto.
    Qed.

    Lemma obl_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      obl_fuel k ℓ2 (▽)%M ⊢ |==> obl_fuel k ℓ1 μ.
    Proof.
      iIntros (LT) "H". iMod (obl_fuel_extend_val _ ℓ1 with "H") as "H"; last (unfold_obl_fuel; by iFrame).
      1: auto.
      exists μ. apply η_mono.
    Qed.
    Lemma obl_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, obl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, obl_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply obl_fuel_extend; eauto.
    Qed.
    Lemma obl_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, obl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, obl_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply obl_fuel_extend; eauto.
    Qed.

    (** wit_bound rules *)
    Lemma wit_bound_mon k a0 a1 :
      (a0 <= a1)%ord → wit_bound k a0 ==∗ wit_bound k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_bound_mon.
    Qed.
    Lemma wit_bound_compare k a0 a1 :
      wit_bound k a0 -∗ wit k a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_defs. iIntros "(P& Be) (_& Cred)". iApply (witG_compare with "[$]").
    Qed.
    Lemma wit_bound_spend_gen k a0 a1 :
      wit_bound k a0 -∗ wit k a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ wit_bound k a2.
    Proof.
      unfold_defs. iIntros "($& Ow) (_& Oc)". iApply (witG_witness_spend_gen with "[$]").
    Qed.
    Lemma wit_bound_spend k a0 a1 :
      (Ord.O < a1)%ord →
      wit_bound k a0 -∗ wit k a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ wit_bound k a2.
    Proof.
      unfold_defs. iIntros (LT) "($& Ow) (_& Oc)". iApply (witG_witness_spend with "[$]"). done.
    Qed.
    Lemma wit_bound_spend_one k a :
      wit_bound k a -∗ wit k Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ wit_bound k a0.
    Proof.
      iIntros "Ow Oc". iApply (wit_bound_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** wit_layer rules *)
    Lemma wit_layer_wit_bound k ℓ :
      wit_layer k ℓ -∗ ∃ μ, wit_bound k (η (measure ℓ μ)).
    Proof. unfold_defs. eauto. Qed.

    (** wit rules *)
    Lemma wit_eq k a0 a1 :
      (a0 == a1) → wit k a1 = wit k a0.
    Proof.
      unfold_defs. intros. rewrite (witG_witness_eq k a0 a1); auto.
    Qed.
    Lemma wit_mon k a0 a1 :
      (a0 <= a1) → wit k a1 ==∗ wit k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_witness_mon.
    Qed.
    Lemma wit_split k a0 a1 :
      wit k (a0 ⊕ a1)%ord ⊣⊢ wit k a0 ∗ wit k a1.
    Proof.
      unfold_defs. rewrite witG_witness_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma wit_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord →
      wit k a2 ==∗ wit k a0 ∗ wit k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (witG_witness_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma wit_lt k a0 a1 :
      (a0 < a1) → wit k a1 ==∗ wit k a0 ∗ wit k Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)". iFrame "Be".
      iMod (witG_witness_lt with "P") as "[$ (%& %& C)]"; first done. 
      apply ord_lt_one in H. iMod (witG_witness_mon_split with "C") as "[_ $]"; done.
    Qed.

    (** obl_fuels rules *)
    Lemma obl_fuels_init α :
      ⊢ obl_fuels α ∅.
    Proof.
      unfold_defs. rewrite big_sepM_empty. done.
    Qed.

    Lemma obl_fuels_add α F f ℓ ν μ :
      (α <= measure ℓ ν)%ord →
      obl_fuels α F -∗ obl_fuel f ℓ (μ × ν)%M ==∗ obl_fuels α (<[f:=(ℓ, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !obl_fuels_unseal /obl_fuels_def.
      unfold_obl_fuel. iMod (obl_fuel_val_mon _ ((measure ℓ μ) × α)%ord with "Gf") as "Gf".
      { rewrite measure_mult. apply Jacobsthal.le_mult_r. auto. }
      iModIntro. iApply (big_sepM_insert_delete _ _ f).
      iFrame "Gf". destruct (F !! f) eqn:LUF.
      - iPoseProof (big_sepM_delete _ _ f with "Wfs") as "[_ $]". eauto.
      - rewrite delete_id; auto.
    Qed.

    Lemma obl_fuels_add_map α F (G : gmap oid (layer * measurable_syntax)) ν :
      obl_fuels α F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ (α <= measure l ν)%ord ⌝ ∗ obl_fuel g l (m × ν)%M) ==∗
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
      (obl_fuels α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, obl_fuel f l m)).
    Proof.
      rewrite obl_fuels_unseal /obl_fuels_def. iIntros (LT) "Fs".
      rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
      iIntros "!> % % % H". destruct x as (l& m).
      rewrite obl_fuel_unseal /obl_fuel_def. rewrite -obl_fuel_val_add. iApply (obl_fuel_val_mon with "H").
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
      embed_fuels wf_ltA a ℓ1 F -∗ obl_fuel f ℓ2 (μ × ⟪wf_ltA, a⟫)%M ==∗ embed_fuels wf_ltA a ℓ1 (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LE) "Wfs Gf". rewrite !embed_fuels_unseal /embed_fuels_def.
      iApply (obl_fuels_add with "Wfs Gf"). apply measure_layer_leibniz_le_proper. auto.
    Qed.

    Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
      a ℓ F (G : gmap oid (layer * measurable_syntax)) :
      embed_fuels wf_ltA a ℓ F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ layer_leibniz_le ℓ l ⌝ ∗ obl_fuel g l (m × ⟪wf_ltA, a⟫)%M) ==∗
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
      embed_fuels wf_ltA a' ℓ F ∗ ([∗ map] f ↦ '(l, m) ∈ F, obl_fuel f l m).
    Proof.
      rewrite embed_fuels_unseal /embed_fuels_def.
      intros LT. apply (obl_fuels_decr). apply measure_embed_lt. auto.
    Qed.

    (** wit_fuels rules *)
    Lemma wit_fuels_init k ℓ :
      wit_layer k ℓ -∗ ∃ α, wit_fuels k ℓ α ∅.
    Proof.
      unfold_defs. iIntros "(%& $& $)". iExists μ. iSplitR; done.
    Qed.

    Lemma wit_fuels_wit_layer k ℓ α F :
      wit_fuels k ℓ α F ==∗ wit_layer k ℓ.
    Proof.
      iIntros "Wl". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wl" as "(%& %& #Wb& _)".
      rewrite !wit_layer_unseal /wit_layer_def.
      iExists μ. iApply wit_bound_mon; eauto.
    Qed.

    Lemma wit_fuels_add k ℓ1 α F f ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      wit_fuels k ℓ1 α F -∗ obl_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wfs" as "(%& %& $& M)".
      iExists _. iSplitR; first eauto.
      iApply (obl_fuels_add with "M Gf").
      etrans; first eauto. apply measure_extend; auto.
    Qed.

    Lemma wit_fuels_add_map k ℓ α F (G : gmap oid (layer * measurable_syntax)) :
      wit_fuels k ℓ α F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ (ℓ < l)%ordi ⌝ ∗ obl_fuel g l (m × ▽)%M) ==∗
      wit_fuels k ℓ α (G ∪ F).
    Proof.
      rewrite !wit_fuels_unseal /wit_fuels_def.
      iIntros "(%& %& $& Fs) Gfs". iExists _. iSplitR; first eauto.
      iApply (obl_fuels_add_map _ _ _ (▽)%M with "Fs [Gfs]").
      iApply (big_sepM_impl with "Gfs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. etrans; first eauto. apply measure_extend. done.
    Qed.

    Lemma wit_fuels_decr k ℓ α F :
      wit_fuels k ℓ α F -∗ wit k Ord.one ==∗
      ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗
            ([∗ map] f ↦ '(l, m) ∈ F, obl_fuel f l m).
    Proof.
      rewrite wit_fuels_unseal /wit_fuels_def. iIntros "(%& %& #Wbk& Fs) Wk".
      iMod (wit_bound_spend_one with "Wbk Wk") as "(%& %& #Wbk2)".
      iExists a0. iSplitR; first done. iFrame "Wbk2". assert (a0 <= η (measure ℓ μ)).
      { etransitivity; last eauto. apply WFOCM.lt_le. auto. }
      iFrame (H1).
      iApply (obl_fuels_decr with "Fs"). auto.
    Qed.

    (** th_obls rules *)
    Lemma th_obls_disj i G1 G2 q1 q2 :
      th_obls i G1 q1 -∗ th_obls i G2 q2 -∗ (⌜ G1 ## G2 ⌝).
    Proof.
      unfold_defs. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H. auto.
    Qed.

    Lemma th_obls_op_1 i G1 G2 q1 q2 :
      th_obls i G1 q1 -∗ th_obls i G2 q2 -∗ th_obls i (G1 ∪ G2) (q1 + q2).
    Proof.
      unfold_defs. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
      iPoseProof (othreadG_obls_op_1 with "[$T1 $T2]") as "T".
      iDestruct "Gx1" as "[Gx1 Gx1']". iDestruct "Gx2" as "[Gx2 Gx2']".
      iCombine "Gx1 Gx2" as "Gx". iCombine "Gx1' Gx2'" as "Gx'".
      iPoseProof (big_sepS_union with "[$Es1 $Es2]") as "$". 1: auto.
      iFrame "Ge1".
      rewrite -!Qp.div_add_distr. iCombine "Gx Gx'" as "Gx". rewrite -Qp.div_add_distr. iFrame "Gx".
      iFrame.
    Qed.
    Lemma th_obls_op_2 i G1 G2 q1 q2 :
      G1 ## G2 →
      th_obls i (G1 ∪ G2) (q1 + q2) -∗ (th_obls i G1 q1 ∗ th_obls i G2 q2).
    Proof.
      unfold_defs. iIntros (Hd) "(#Ge& Gx& T& Es)".
      iPoseProof (othreadG_obls_op_2 with "T") as "[$ $]"; first auto.
      iDestruct "Gx" as "[Gx Gx']". rewrite !Qp.div_add_distr.
      iDestruct "Gx" as "[Gx1 Gx2]". iDestruct "Gx'" as "[Gx1' Gx2']".
      iCombine "Gx1 Gx1'" as "$". iCombine "Gx2 Gx2'" as "$".
      rewrite big_sepS_union. 2: auto.
      iFrame "Ge". iFrame.
    Qed.

  End liveness_preds.

  Section fmupd.

    Lemma obl_alloc_assigned_mupd n Θ i G q ℓ μ :
      th_obls i G q -∗
      |=[n,Θ]=>m ∃ k, (⌜ k ∉ G ⌝) ∗
                     th_obls i ({[k]} ∪ G) q ∗
                     obl_alive k (1/2)%Qp ∗
                     obl_layer k ℓ ∗
                     obl k ∗
                     obl_fuel k ℓ μ ∗
                     wit_layer k ℓ ∗
                     (∀ E N (P Q R : iProp Σ), (▷ P) ={E}=∗ obl_inv N k P Q R).
    Proof.
      unfold_defs. iIntros "(#Oe& Ox& Ob& OS)".
      iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).

      TODO
      iMod (osat _alloc_assigned _ k v ℓ μ i with "S") as "(S& #Gwf& #Ge& Gl& Gv& Gf& Go& #Gseq& %OStep)".
      1: auto.
      iDestruct "Gl" as "[Gl0 [Gl1 Gl']]".
      iMod (othread_alloc_obl with "[$S $O $Ob $Ge $Gl' $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iPoseProof (oblG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηℓ := (λ x, η (measure (ℓ v) μ)) : ghost_lock_version → _).
      iMod (owit_alloc_witness_locked _ k v ηℓ with "[$W $Gseq $Gvl]") as "(W& #Wseq)".
      { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_bound k (η (measure (ℓ v) μ)))%I with "[Wseq]" as "#Ww".
      { rewrite set_seq_S_end_union_L. rewrite big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton.
        subst ηℓ. simpl. eauto. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo0 [Oo1 Oo']]".
      iPoseProof (glassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iDestruct "Gl1" as "[Gl1 Gl']".
      iModIntro. iExists (<[k:=(v, ghost_lock_locked (GL:=ord_ghost_lock_class) (measure (ℓ v) μ) i)]> Ω1).
      iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (owit_inv_alloc_locked Ω1 k W1 NinOk1 GWI _ _ _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iDestruct "Gv" as "[[Gv1 Gv1'] [Gv2 Gv2']]". iCombine "Gv1 Gv2" as "Gv". iCombine "Gv1' Gv2'" as "Gv'".
      iModIntro. iExists k. iFrame "Oe Gwf Ge Gvl Ww Gf Ox Gseq Gv'". iSplitR.
      { iPureIntro. apply not_elem_of_dom. auto. }
      iSplitL "Ob OS Gv Go Gl0 Gl1 Oo0 Oo1".
      { rewrite dom_insert_L. iFrame "Ob". iApply big_sepM_insert. 1: apply not_elem_of_dom; auto.
        iFrame "OS Ge Gv Go". iCombine "Gl0 Gl1" as "$". iCombine "Oo0 Oo1" as "$". eauto. }
      iSplitR.
      { iApply (big_sepS_impl with "Gseq"). iIntros "!> %% ($& $)". iFrame "Ge".
        iApply (obl_history_mon with "Gseq"). apply elem_of_set_seq in H. lia. }
      iIntros (E N P Q R) "HP".
      iMod (oblG_variant_alloc_locked _ N _ _ _ P Q R with "[$Gl' $HP]") as "#GVar".
      iModIntro. eauto.
    Qed.
    Lemma obl_alloc_obl_1 E n Θ i G q ℓ μ N v (P Q R : iProp Σ) :
      Proper (le ==> layer_leibniz_le) ℓ →
      th_obls i G q -∗
      (▷ P) -∗
      |={E:Θ}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                     th_obls i (<[k:=v]>G) q ∗
                     obl_alive k (1/2)%Qp ∗
                     obl_layer k ℓ ∗ obl k ∗
                     obl_fuel k (ℓ v) μ ∗
                     obl_inv N k P Q R ∗
                     wit_layer k (ℓ v) ∗
                     ([∗ set] u ∈ set_seq 0 v, obl_fulfilled k u).
    Proof.
      iIntros (MONO) "TG HP".
      iMod (obl_alloc_obl_0 with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
      iMod ("H" $! E N P Q R with "HP") as "H". by iModIntro.
    Qed.

    Lemma obl_alloc_fulfilled_0 n Θ ℓ μ v :
      Proper (le ==> layer_leibniz_le) ℓ →
      ⊢ |=[n,Θ]=>m ∃ k, obl_layer k ℓ ∗ obl k ∗ obl_alive k 1 ∗ obl_fulfilled k ∗ obl_fuel k (ℓ v) μ ∗
                     wit_layer k (ℓ v) ∗
                     ([∗ set] u ∈ set_seq 0 (S v), obl_fulfilled k u) ∗
                     (∀ E N (P Q R : iProp Σ), (▷ Q) ={E}=∗ obl_inv N k P Q R).
    Proof.
      unfold_defs. iIntros (MONO).
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (osat_alloc_ghost_lock_unlocked _ k v ℓ μ with "S") as "(S& #Gwf& #Ge& #Gu& Gv& Gf& #Gseq& %OStep)".
      { auto. }
      iPoseProof (oblG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηℓ := (λ x, η (measure (ℓ v) μ)) : ghost_lock_version → _).
      iAssert ([∗ set] u ∈ set_seq 0 (S v), oblG_version_lb k u ∗ oblG_unlocked k u)%I as "Gseq2".
      { rewrite set_seq_S_end_union_L big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. eauto. }
      iMod (owit_alloc_witness_unlocked _ k v ηℓ with "[$W $Gseq2]") as "(W& #Wseq)".
      { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_bound k (η (measure (ℓ v) μ)))%I with "[Wseq]" as "#Ww".
      { iClear "Gseq2". rewrite !set_seq_S_end_union_L !big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton.
        subst ηℓ. simpl. eauto. }
      iPoseProof (glassigned_add_obl with "[$A $Ge Gu]") as "A".
      { iRight. iFrame "Gu". }
      iModIntro. iExists (<[k:=(v, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (owit_inv_alloc_unlocked Ω1 k W1 NinOk1 GWI _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Gwf Ge Gvl Ww Gf Gv Gu Gseq".
      iSplitR.
      { iApply (big_sepS_impl with "Gseq2"). iIntros "!> %% ($& $)". iFrame "Ge".
        iApply (obl_history_mon with "Gseq"). apply elem_of_set_seq in H. lia. }
      iIntros (E N P Q R) "HQ".
      iMod (oblG_variant_alloc_unlocked _ N _ _ _ P Q R with "[$Gu $HQ]") as "#GVar".
      iModIntro. eauto.
    Qed.
    Lemma obl_alloc_fulfilled_1 E n Θ ℓ μ N v P Q R :
      Proper (le ==> layer_leibniz_le) ℓ →
      (▷ Q) -∗
      |={E:Θ}=>g ∃ k, obl_layer k ℓ ∗ obl k ∗ obl_alive k 1 ∗ obl_fulfilled k ∗ obl_fuel k (ℓ v) μ ∗
                     obl_inv N k P Q R ∗
                     wit_layer k (ℓ v) ∗
                     ([∗ set] u ∈ set_seq 0 (S v), obl_fulfilled k u).
    Proof.
      iIntros (MONO) "HQ".
      iMod (obl_alloc_fulfilled_0) as "(%& $& $& $& $& $& $& $& H)".
      iMod ("H" $! E N P Q R with "HQ") as "H". by iModIntro.
    Qed.

    Lemma obl_lock_0 E qc k N v1 (P1 Q1 R1 : iProp Σ) :
      ↑N ⊆ E →
      obl_alive k1 qc -∗
      obl_fulfilled k1 -∗
      obl_inv N k1 P1 Q1 R1 -∗
      |={E,E ∖ ↑N}=> (▷ (obl_alive k1 qc ∗ Q1)) ∗
                    (∀ i G q ℓ,
                       th_obls i G q -∗
                       obl_alive k1 1 -∗
                       obl_layer k ℓ -∗
                       ∀ v2 μ, (⌜v1 < v2⌝) →
                               ∀ n Θ, |=[n,Θ]=>m (th_obls i (<[k:=v2]>G) q ∗ ⌜ G !! k = None ⌝ ∗
                                             obl_alive k2 (1/2)%Qp ∗
                                             obl k2 ∗ obl_fuel k (ℓ v2) μ ∗
                                             wit_layer k2 (ℓ v2) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit_layer k u (ℓ u)) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), obl_fulfilled k u)) ∗
                                          (∀ E0 (P2 Q2 R2 : iProp Σ), (▷ P2) ={E0}=∗ obl_inv N k2 P2 Q2 R2) ∗
                                          ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl1)& Gv1) (_& #Gu1) (_& #Gvar1)".
      iMod (oblG_variant_acc_version_unlocked with "Gvar1 Gv1 Gu1") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "($& _& _& $)". eauto. }
      iIntros (i G q ℓ) "(#Oe& Ox& Ob& OS) (_& Gv1) #Gwf % % %Ltv %".
      iPoseProof (oblG_layer_mono with "Gwf") as "%MONO".
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (osat_lookup_unlocked with "[$S $Ge $Gu1]") as "%LUO1u".
      iPoseProof (osat_lookup_version with "[$S $Ge $Gv1]") as "%LUO1v".
      destruct LUO1v as (?&LUO1v). destruct LUO1u as [LUO1u | (?&?&?&LUO1u)]; cycle 1.
      { exfalso. rewrite LUO1u in LUO1v. inv LUO1v. lia. }
      rewrite LUO1u in LUO1v. inv LUO1v.
      iMod (osat_lock _ _ v1 v2 ℓ μ i with "[$S $Gwf $Gu1 $Gv1]") as "(%& S& Gl& Gv& Gf& Go& #Gseq& %Gstep)".
      1: auto.
      iDestruct "Gl" as "[Gl1 [Gl2 Gl']]".
      iMod (othread_alloc_obl with "[$S $O $Ob $Ge $Gl' $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iPoseProof (oblG_version_get_lb _ v2 v2 with "Gv") as "#Gvl2". 1: done.
      set (ηℓ := (λ v, η (measure (ℓ v) (μ')%M)) : ghost_lock_version → _).
      iMod (owit_lock _ _ v1 v2 ηℓ with "[$W $Gseq $Gvl2]") as "(W& #Ww& #Wseq)".
      1: auto.
      { specialize (GWI k). rewrite LUO1u in GWI. inv GWI.
        destruct y. destruct H1. subst. by destruct w. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo1 [Oo2 Oo']]".
      iPoseProof (glassigned_add_obl _ k v2 with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iDestruct "Gv" as "[[Gv1 Gv1'] [Gv2 Gv2']]". iCombine "Gv1 Gv2" as "Gv". iCombine "Gv1' Gv2'" as "Gv'".
      iModIntro. iExists (<[k:=(v2, ghost_lock_locked (GL:=ord_ghost_lock_class) (measure (ℓ v2) (μ')%M) i)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_lock _ _ v1 v2 _ _ _ LUO1u GWI Gstep W2 WStep GWI2) as [LUW1 WMon].
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite fmap_insert. iFrame. eauto. }
      (* FIXME: iModIntro introduces too many modalities. *)
      iApply fupd_intro. iModIntro.
      iDestruct "Gl2" as "[Gl2 Gl']".
      rewrite dom_insert_L. iFrame "Oe Ge Gvl2 Ox Ob Gf Ww Gv'".
      iDestruct "Gvl1" as "[Gvl1' His1]".
      iPoseProof (obl_history_add _ v1 v2 with "[His1] Gseq") as "#His2".
      1: auto.
      { rewrite set_seq_S_end_union_L. iApply big_sepS_union.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. auto. }
      iFrame "His2". iSplitR "ACC Gl'".
      { iSplitL.
        { iApply big_sepM_insert.
          { apply not_elem_of_dom; auto. }
          iFrame. iCombine "Gl1 Gl2" as "$". iCombine "Oo1 Oo2" as "$". auto. }
        iSplitR.
        { iPureIntro. apply not_elem_of_dom. auto. }
        iSplitL.
        { iApply (big_sepS_impl with "Wseq"). iIntros "!> %% $".
          iPoseProof (big_sepS_delete _ _ _ H with "Gseq") as "[[$ _] _]".
          iFrame "Ge". iApply (obl_history_mon with "His2"). apply elem_of_set_seq in H. lia. }
        { iApply (big_sepS_impl with "Gseq"). iIntros "!> %% [$ $]".
          iFrame "Ge". iApply (obl_history_mon with "His2"). apply elem_of_set_seq in H. lia. }
      }
      iSplitR "ACC".
      { iIntros (? P2 Q2 R2) "HP2". iMod (oblG_variant_alloc_locked _ N k v2 _ P2 Q2 R2 with "[$Gl' $HP2]") as "#Gvar2". done. }
      iIntros "HR1". iMod ("ACC" with "[HR1]") as "_".
      { iNext. iRight. iFrame. iFrame "Gu1". iApply (oblG_version_get_expired _ v2 v1); auto. }
      done.
    Qed.

    Lemma obl_unlock_0 E i G q N k v P Q R :
      ↑N ⊆ E →
      G !! k = Some v →
      th_obls i G q -∗
      obl_inv N k P Q R -∗
      |={E,E ∖ ↑N}=> (▷ (th_obls i G q ∗ obl_assigned k ∗ P)) ∗
                    (th_obls i G q -∗
                     obl_assigned k -∗
                     ∀ n Θ, |=[n,Θ]=>m (th_obls i (delete k G) q ∗ obl_alive k (1/2)%Qp ∗ obl_fulfilled k) ∗
                                ((▷ Q) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK LUGk) "(#Oe& Ox& Ob& OS) ((#Ge& #Gvl)& #Gvar)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& [_ Gv]& Go& Oo) OS]".
      iMod (oblG_variant_acc_version_locked with "Gvar Gv Gl") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "Ox Ob Go Oo OS H".
      { iNext. iFrame "Oe Ox Ob". iDestruct "H" as "(Gv& Gl& $& $)".
        rewrite (big_sepM_delete _ _ _ _ LUGk). iFrame. iFrame "Ge Gvl". }
      iIntros "(_& Ox& Ob& OS) (_& Gl1) %".
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& Gv& Go& Oo) OS]".
      iPoseProof (osat_lookup_locked with "[$S $Ge $Gl]") as "%LUO1l".
      iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&?&LUO1o).
      rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into v, x2 into a.
      iPoseProof (glassigned_delete_obl _ k v with "A") as "(A& _& [(%& Go1& Oo1) | #Gu])".
      { rewrite lookup_fmap LUO1l. done. }
      2:{ iExFalso. iPoseProof (oblG_locked_unlocked_false with "[$Gl $Gu]") as "%". done. }
      iPoseProof (oblG_owner_agree _ i i0 with "[$Go $Go1]") as "%". destruct H as [<- _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (othread_delete_obl_frac with "[$O $Ob $Oo]") as "(O& Ob& Gl2& Go2)".
      { apply elem_of_dom. eauto. }
      iDestruct "Gl" as "[Gl Gl']". iCombine "Gl' Gl1" as "Gl'". iCombine "Gl' Gl2" as "Gl'".
      iCombine "Gl Gl'" as "Gl".
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
      iMod (osat_unlock with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
      assert (LUW : ∃ b, W1 !! k = Some (v, witness_locked b) ∧ (b <= η a)%ord).
      { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y. destruct H1. subst.
        destruct w; eauto. done. }
      destruct LUW as (b&LUW1& LEab).
      iPoseProof (owit_unlock with "[$W $Gu]") as "W". 1: eauto.
      iPoseProof (glassigned_add_obl _ k v with "[$A $Ge]") as "A".
      { iRight. eauto. }
      iModIntro. iExists (<[k:=(v, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]). specialize (Gstep a).
      pose proof (owit_inv_unlock _ _ v _ _ _ LUO1l GWI Gstep W2 WStep GWI2) as (?& LUW& WMon).
      rewrite LUW1 in LUW. inv LUW.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite insert_delete_eq. rewrite fmap_insert. iFrame. eauto. }
      iApply fupd_intro. iIntros "!>". iDestruct "Gv" as "[_ Gv]". iFrame "Oe Ge Gvl Gu Ox Gv".
      iSplitR "ACC".
      { iSplitL "Ob".
        - rewrite dom_delete_L. iFrame.
        - iFrame. }
      iIntros "HQ". iMod ("ACC" with "[HQ]") as "_".
      { iNext. iLeft. iRight. iFrame. eauto. }
      done.
    Qed.

    Lemma obl_new_version_0 E k qc v1 N (P1 Q1 R1 : iProp Σ) :
      ↑N ⊆ E →
      obl_alive k1 qc -∗
      obl_fulfilled k1 -∗
      obl_inv N k1 P1 Q1 R1 -∗
      |={E,E ∖ ↑N}=> (▷ (obl_alive k1 qc ∗ Q1)) ∗
                    (obl_alive k1 1 -∗
                     ∀ v2, (⌜ v1 < v2 ⌝) →
                           ∀ n Θ, |=[n,Θ]=>m (obl k2 ∗ obl_fulfilled k2 ∗ obl_alive k2 1 ∗
                                         ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), obl_fulfilled k u)) ∗
                                      (∀ E0 (P2 Q2 R2 : iProp Σ), (▷ Q2) ={E0}=∗ obl_inv N k2 P2 Q2 R2) ∗
                                      ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl1)& Gv1) (_& #Gu1) (_& #Gvar1)".
      iMod (oblG_variant_acc_version_unlocked with "Gvar1 Gv1 Gu1") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "($& _& _& $)". eauto. }
      iIntros "(_& Gv1) % %LTv %".
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (osat_lookup_unlocked with "[$S $Ge $Gu1]") as "%LUO1u".
      iPoseProof (osat_lookup_version with "[$S $Ge $Gv1]") as "%LUO1v".
      destruct LUO1v as (?&LUO1v). destruct LUO1u as [LUO1u | (?&?&?&LUO1u)]; cycle 1.
      { exfalso. rewrite LUO1u in LUO1v. inv LUO1v. lia. }
      rewrite LUO1u in LUO1v. inv LUO1v.
      iMod (osat_new_version _ _ v1 v2 with "[$S $Ge $Gu1 $Gv1]") as "(S& #Gu2& Gv2& #Gseq& %Gstep)".
      1: auto.
      iPoseProof (oblG_version_get_lb _ v2 v2 with "Gv2") as "#Gvl2". 1: done.
      set (ηℓ := (λ v, η (Ord.O)) : ghost_lock_version → _).
      iMod (owit_new_version _ _ v1 v2 ηℓ with "[$W $Gseq $Gvl2]") as "(W& #Ww& #Wseq)".
      1: auto.
      { specialize (GWI k). rewrite LUO1u in GWI. inv GWI.
        destruct y, H1. subst. destruct w; done. }
      iPoseProof (glassigned_add_obl _ k v2 with "[$A $Ge]") as "A".
      { iRight. eauto. }
      iModIntro. iExists (<[k:=(v2, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_new_version _ _ v1 v2 _ LUO1u GWI Gstep W2 WStep GWI2) as [LUW1 WMon].
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite fmap_insert. iFrame. eauto. }
      (* FIXME: iModIntro introduces too many modalities. *)
      iApply fupd_intro. iModIntro.
      iFrame "Ge Gvl2 Gu2 Gv2".
      iAssert ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), oblG_version_lb k u ∗ oblG_unlocked k u)%I with "[]" as "#Gseq'".
      { replace (v2 - v1) with (S (v2 - v1 - 1)) by lia. rewrite (set_seq_S_end_union_L _ (v2 - v1 - 1)).
        iPoseProof (big_sepS_union with "Gseq") as "[_ Gseq']".
        { apply set_seq_S_end_disjoint. }
        replace (S (v2 - v1 - 1) - 1) with (v2 - v1 - 1) by lia. eauto. }
      iDestruct "Gvl1" as "[Gvl1' His1]".
      iPoseProof (obl_history_add _ v1 v2 with "[His1] Gseq'") as "#His2".
      1: auto.
      { rewrite set_seq_S_end_union_L. iApply big_sepS_union.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. auto. }
      iFrame "His2". iSplitR "ACC".
      { iApply (big_sepS_impl with "Gseq'"). iIntros "!> %% [$ $]".
        iFrame "Ge". iApply (obl_history_mon with "His2"). apply elem_of_set_seq in H. lia.
      }
      iSplitR "ACC".
      { iIntros (? P2 Q2 R2) "HQ2". iMod (oblG_variant_alloc_unlocked _ N k v2 _ P2 Q2 R2 with "[$Gu2 $HQ2]") as "#Gvar2". done. }
      iIntros "HR1". iMod ("ACC" with "[HR1]") as "_".
      { iNext. iRight. iFrame. iFrame "Gu1". iApply (oblG_version_get_expired _ v2 v1); auto. }
      done.
    Qed.

    Lemma obl_change_owner_0 n Θ i1 i2 G1 G2 q1 q2 k v ℓ0 :
      G1 !! k = Some v →
      th_obls i1 G1 q1 -∗
      th_obls i2 G2 q2 -∗
      obl_fuel k ℓ0 1 -∗
      |=[n,Θ]=>m th_obls i1 (delete k G1) q1 ∗ th_obls i2 (<[k:=v]>G2) q2 ∗ ⌜ G2 !! k = None ⌝.
    Proof.
      unfold_defs. iIntros (LUGk) "(#Oe1& Ox1& Ob1& OS1) (#Oe2& Ox2& Ob2& OS2) (#Ge& Gf)".
      rewrite (oblG_fuel_eq _ _ Ord.one); cycle 1.
      { rewrite measure_nat Ord.from_nat_1. done. }
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS1") as "[(_& Gl& [#Gseq Gv]& Go& Oo) OS1]".
      iPoseProof (osat_lookup_locked with "[$S $Ge $Gl]") as "%LUO1l".
      iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&?&LUO1o).
      rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into v, x2 into a.
      iPoseProof (glassigned_delete_obl _ k v with "A") as "(A& _& [(%& Go1& Oo1) | #Gu])".
      { rewrite lookup_fmap LUO1l. done. }
      2:{ iExFalso. iPoseProof (oblG_locked_unlocked_false with "[$Gl $Gu]") as "%". done. }
      iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [-> _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (othread_delete_obl_frac with "[$O $Ob1 $Oo]") as "(O& Ob1& Gl2& Go2)".
      { apply elem_of_dom. eauto. }
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
      iMod (osat_progress_one_owner _ _ _ _ _ i2 with "[$S $Go $Gf]") as "(%& S& Go& %Gstep)".
      1: eauto.
      1: apply Ord.S_lt.
      iMod (othread_alloc_obl with "[$S $O $Ob2 $Ge $Gl2 $Go]") as "(S& O& %NinkG2& Ob2& Oo& Go)".
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
      iPoseProof (glassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iModIntro. iExists (<[k:=(v, ghost_lock_locked a' i2)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_progress_owner _ k v _ _ _ LUO1l GWI _ _ Gstep W2 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite insert_delete_eq. rewrite fmap_insert. iFrame. eauto. }
      iIntros "!> !>". iFrame "Oe1 Oe2 Ox1 Ox2 OS1". rewrite dom_delete_L dom_insert_L.
      iFrame "Ob1 Ob2". assert (LUkG2 : G2 !! k = None) by (apply not_elem_of_dom; auto).
      iSplitL; last auto.
      iApply big_sepM_insert. 1: auto. iFrame. iCombine "Oo Oo1" as "Oo". eauto.
    Qed.

    Lemma obl_terminate_0 n Θ i :
      th_obls i ∅ 1 -∗ |=[n,Θ]=>m th_term i.
    Proof.
      unfold_defs. iIntros "(#Oe& Ox& Ob& OS)".
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iMod (othread_exec_to_term with "[$O $Ox $Ob]") as "[O #Ot]".
      iModIntro. iExists Ω1. iSplitR; first done.
      iIntros (? [WStep GWI2]).
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W A". iSplitR.
      { eauto. }
      iIntros "!> !>". auto.
    Qed.

    Lemma obl_check_witnesses_0 n Θ R :
      ([∗ map] r ↦ v ∈ R, gl r v) -∗
      |=[n,Θ]=>m ([∗ map] r ↦ v ∈ R, wit r v Ord.O ∨ obl_fulfilled r v).
    Proof.
      unfold_defs. iIntros "#REs".
      iApply mupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI1)".
      iPoseProof (owit_get_credit_zero with "W") as "[W Ws]".
      assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
      iAssert (⌜ dom R ⊆ dom W1 ⌝)%I as "%RWSub".
      { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
        pose proof INRx. apply elem_of_dom in H. destruct H.
        iPoseProof (big_sepM_delete _ _ _ _ H with "REs") as "[[#Beg _] _]".
        iPoseProof (osat_elem with "[$S $Beg]") as "%". done.
      }
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ dom R = dom WR).
      { clear GWI1 DomOW WStep.
        revert R RWSub. induction W1 using map_ind; intros.
        { assert (dom R = ∅) by (set_solver). apply dom_empty_inv_L in H. subst. exists ∅, ∅. done. }
        rename i into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ dom R)).
        - set (R2 := delete r R). assert (dom R2 ⊆ dom m).
          { subst R2. rewrite dom_delete_L. set_solver + RWSub. }
          apply elem_of_dom in e. destruct e. rename H1 into LUR.
          destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
          exists (<[r:=x]>WR), WR'. subst R2.
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. split_and !.
          + apply map_disjoint_insert_l. split; auto.
          + subst. rewrite insert_union_l. done.
          + replace R with (<[r:=x0]> (delete r R)).
            * rewrite !dom_insert_L H3. auto.
            * rewrite insert_delete_id; auto.
        - assert (dom R ⊆ dom m).
          { set_solver + RWSub n. }
          pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. exists WR, (<[r:=x]>WR'). split_and !; auto.
          + apply map_disjoint_insert_r. split; auto.
          + subst. rewrite insert_union_r; done.
      }
      destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
      assert (EQfst : fst <$> Ω1 = fst <$> W1).
      { apply map_eq. intros j. specialize (GWI1 j). rewrite !lookup_fmap. destruct (W1 !! j) eqn:LUW1.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. destruct x. destruct w. destruct H1. by subst.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. done.
      }
      iAssert (⌜ ∀ k v, R !! k = Some v → ∃ w, WR !! k = Some w ∧ v ≤ w.1 ⌝)%I as "%Rver".
      { iIntros (k v LUR). iPoseProof (big_sepM_delete _ _ _ _ LUR with "REs") as "[(#Ge& #Gvl& #His) _]".
        iPoseProof (osat_lookup_version_lb with "[$S $Ge $Gvl]")as "(%&%&%&%)".
        rewrite map_eq_iff in EQfst. specialize (EQfst k). rewrite !lookup_fmap H in EQfst.
        assert (is_Some (WR !! k)).
        { apply elem_of_dom. rewrite -DomWR. apply elem_of_dom; eauto. }
        destruct H1 as (?& LUWRk).
        assert (WR' !! k = None).
        { eapply map_disjoint_Some_l; eauto.  }
        destruct (W1 !! k) eqn:LUW1.
        - rewrite LUW1 in EQfst. inv EQfst. apply lookup_union_Some_inv_l in LUW1; eauto.
        - rewrite LUW1 in EQfst. inv EQfst.
      }
      iAssert (|==> [∗ map] r↦v ∈ R, (witG_witness r v Ord.O) ∨ (oblG_unlocked r v))%I
        with "[Ws]" as ">Rs".
      { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto.
        iApply big_sepM_bupd. iClear "REs". clear dependent WR'.
        iStopProof. revert R DomWR Rver. induction WR using map_ind; iIntros (R DomWR Rver) "M".
        { apply dom_empty_inv_L in DomWR. subst. done. }
        rename i into r. rewrite dom_insert_L in DomWR. destruct (R !! r) eqn:LUR; cycle 1.
        { exfalso. apply not_elem_of_dom in LUR. set_solver + DomWR LUR. }
        remember (delete r R) as R0.
        assert (dom R0 = dom m).
        { subst. rewrite dom_delete_L. apply not_elem_of_dom in H. rewrite DomWR. set_solver + H. }
        assert (R0 !! r = None).
        { subst. apply lookup_delete_eq. }
        assert (R = <[r:=g]>R0).
        { subst. rewrite insert_delete_id; auto. }
        rewrite H2.
        assert (∀ k v, R0 !! k = Some v → ∃ w, m !! k = Some w ∧ v ≤ w.1).
        { intros. specialize (Rver k v). subst. destruct (decide (k = r)).
          { subst. rewrite lookup_delete_eq in H3. inv H3. }
          rewrite lookup_delete_ne in H3; auto. apply Rver in H3. destruct H3 as (?&?&?).
          rewrite lookup_insert_ne in H3; eauto.
        }
        destruct (Rver _ _ LUR) as (w& LUmk& LEv). rewrite lookup_insert_eq in LUmk.
        clear dependent R. inv LUmk. rewrite !big_sepM_insert; auto.
        destruct w. iDestruct "M" as "[H M]". iPoseProof (IHWR _ H0 H3 with "M") as "$".
        iDestruct "H" as "(#H1& #H2& H)". simpl in LEv. destruct w.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. by iFrame.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. iRight. auto.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
      }
      iAssert ([∗ map] r↦v ∈ R,
                 ((oblG_elem r ∗ oblG_version_lb r v ∗
                   ([∗ set] u ∈ set_seq 0 v, oblG_version_lb r u ∗ oblG_unlocked r u)) ∗ witG_witness r v Ord.O) ∨
                   ((oblG_elem r ∗ oblG_version_lb r v ∗
                     ([∗ set] u ∈ set_seq 0 v, oblG_version_lb r u ∗ oblG_unlocked r u)) ∗ oblG_unlocked r v))%I
        with "[Rs]" as "Rs".
      { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
        iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl& #His)".
        - iLeft. iFrame. auto.
        - iRight. auto.
      }
      pose proof (owit_inv_rc_step_same_gls _ _ _ GWI1 WStep GWI2) as WMon.
      iPoseProof (owit_mon _ _ WMon with "W") as "W".
      rewrite /model_interp. iFrame "S O W A". iSplitR.
      { eauto. }
      iIntros "!> !>". auto.
    Qed.

    (** Variant access rules *)
    Lemma obl_variant_unfold k v P Q R :
      obl_variant k P Q R
      ⊣⊢ ((obl_assigned k ∗ P) ∨ (obl_fulfilled k ∗ Q)) ∨ (obl_expired k ∗ R).
    Proof.
      rewrite !obl_variant_unseal /obl_variant_def. auto.
    Qed.

    Local Lemma obl_variant_internal k v P Q R :
      obl_variant k P Q R -∗
      oblG_variant_internal k v (1 / 2 / 2 / 2 / 2) P Q R.
    Proof.
      unfold_defs. iIntros "[[H | H] | H]".
      - iLeft. iLeft. iDestruct "H" as "((_& $)& $)".
      - iLeft. iRight. iDestruct "H" as "((_& $)& $)".
      - iRight. iDestruct "H" as "((((_& _)& $)& $)& $)".
    Qed.

    Lemma obl_inv_acc_cases E N k v P Q R :
      ↑N ⊆ E →
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ obl_variant k P Q R) ∗ (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl)& #Gvar)".
      iMod (oblG_variant_acc with "Gvar") as "[[[H | H] | H] ACC]". 1: auto.
      - iModIntro. iSplitL "H".
        + iNext. iLeft. iLeft. iDestruct "H" as "($& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply obl_variant_internal. unfold_defs. done.
      - iModIntro. iSplitL "H".
        + iNext. iLeft. iRight. iDestruct "H" as "($& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply obl_variant_internal. unfold_defs. done.
      - iModIntro. iSplitL "H".
        + iNext. iRight. iDestruct "H" as "($& $& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply obl_variant_internal. unfold_defs. done.
    Qed.

    Lemma obl_inv_acc E N k v P Q R :
      ↑N ⊆ E →
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ (((obl_assigned k ∗ P) ∨ (obl_fulfilled k ∗ Q)) ∨ (obl_expired k ∗ R))) ∗
      (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (H) "Gv". iMod (obl_inv_acc_cases with "Gv") as "[H $]". 1: auto.
      iModIntro. iNext. by iApply obl_variant_unfold.
    Qed.

    Lemma obl_inv_acc_own E i G q N k v P Q R :
      ↑N ⊆ E →
      G !! k = Some v →
      th_obls i G q -∗
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ (th_obls i G q ∗ obl_assigned k ∗ P)) ∗
      (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK LUGk) "(#Oe& Ox& Ob& OS) ((#Ge& #Gvl)& #Gvar)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& [#Gseq Gv]& Go& Oo) OS]".
      iMod (oblG_variant_acc_version_locked with "Gvar Gv Gl") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "Ox Ob Go Oo OS H".
      { iNext. iFrame "Oe Ox Ob". iDestruct "H" as "(Gv& Gl& $& $)".
        rewrite (big_sepM_delete _ _ _ _ LUGk). iFrame. eauto. }
      iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
      iNext. iApply obl_variant_internal. unfold_defs. done.
    Qed.

    Lemma obl_inv_acc_fulfilled E N k v P Q R :
      ↑N ⊆ E →
      obl_fulfilled k -∗
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ (Q ∨ (obl_expired k ∗ R))) ∗
      (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl)& #Gu) (_& #Gvar)".
      iMod (oblG_variant_acc_unlocked with "Gvar Gu") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "[$ | (_& #Gxp& HR)]". iRight. iFrame. auto. }
      iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
      iNext. iApply obl_variant_internal. unfold_defs. done.
    Qed.

    Lemma obl_inv_acc_current_timeless E N k v q P Q R :
      Timeless R →
      ↑N ⊆ E →
      obl_alive k q -∗
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ (obl_alive k q ∗ (obl_assigned k ∗ P ∨ obl_fulfilled k ∗ Q))) ∗
      (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (TR MASK) "Gc #GV".
      iMod (obl_inv_acc with "GV") as "[H ACC]". 1: auto.
      iDestruct "H" as "[$ | H]".
      - iFrame "Gc". eauto.
      - iDestruct "H" as ">[#Gx _]". iPoseProof (obl_alive_expired_false with "Gc Gx") as "%". done.
    Qed.

    Lemma obl_inv_acc_current_fulfilled_timeless E N k v q P Q R :
      Timeless R →
      ↑N ⊆ E →
      obl_alive k q -∗
      obl_fulfilled k -∗
      obl_inv N k P Q R ={E,E ∖ ↑N}=∗
      (▷ (obl_alive k q ∗ Q)) ∗
      (▷ obl_variant k P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (TR MASK) "Gc #Gd #GV".
      iMod (obl_inv_acc_fulfilled with "Gd GV") as "[[$ | >[Gx _]] ACC]". 1: auto.
      - iFrame "Gc". eauto.
      - iPoseProof (obl_alive_expired_false with "Gc Gx") as "%". done.
    Qed.

  End fmupd.

End preds.
