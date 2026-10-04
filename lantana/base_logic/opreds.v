(** * Obligation predicates and their rules

    Obligations form a forest ([oforest.v]): a parent is a thread or an obligation, and
    every live obligation is a child of exactly one parent ([parP_kids p K]: the children of
    [p] are [K]). A step of a thread burns one unit of fuel of each of its children; the
    model keeps the fuel of every obligation above the fuel of its parent, so all other
    obligations below the thread burn a unit automatically.

    The rules below are model updates [|=[n,Θ]=>m]; the non-discharging ones are proved
    through [mupd_nd_step]. An obligation invariant [oblP_inv N k P R] holds [P] while [k] is
    live and [R] once it is discharged. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.base_logic Require Export oinv mupd.

(** All Local Definitions are only for internal uses and users should not need them. *)
(** ** Obl predicates. *)
Local Definition oblP_id `{SI : sidx} `{@mupdGS SI Σ} k : iProp Σ :=
  oblG_elem k.

Local Definition oblP_assigned_def `{SI : sidx} `{@mupdGS SI Σ}
  k q : iProp Σ :=
  oblP_id k ∗ oblG_assigned k false (q/2 + q/2/2)%Qp.
Local Definition oblP_assigned_aux : seal (@oblP_assigned_def). Proof. by eexists. Qed.
Definition oblP_assigned := oblP_assigned_aux.(unseal).
Local Definition oblP_assigned_unseal :
  @oblP_assigned = @oblP_assigned_def := oblP_assigned_aux.(seal_eq).
Global Arguments oblP_assigned {SI Σ _}.

Local Definition oblP_discharged_def `{SI : sidx} `{@mupdGS SI Σ}
  k : iProp Σ :=
  oblP_id k ∗ oblG_discharged k.
Local Definition oblP_discharged_aux : seal (@oblP_discharged_def). Proof. by eexists. Qed.
Definition oblP_discharged := oblP_discharged_aux.(unseal).
Local Definition oblP_discharged_unseal :
  @oblP_discharged = @oblP_discharged_def := oblP_discharged_aux.(seal_eq).
Global Arguments oblP_discharged {SI Σ _}.

Local Definition oblP_fuel_val `{SI : sidx} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  oblP_id k ∗ oblG_fuel k α.

Local Definition oblP_fuel_def `{SI : sidx} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ μ : iProp Σ :=
  oblP_fuel_val k (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M).
Local Definition oblP_fuel_aux : seal (@oblP_fuel_def). Proof. by eexists. Qed.
Definition oblP_fuel := oblP_fuel_aux.(unseal).
Local Definition oblP_fuel_unseal :
  @oblP_fuel = @oblP_fuel_def := oblP_fuel_aux.(seal_eq).
Global Arguments oblP_fuel {SI Σ _ _}.

(** The two states of an obligation invariant: [P] while the obligation is live, [R] once it
    is discharged. (The ghost protocol of [oinv.v] has a third, intermediate state; it is not
    used: its content is [False].) *)
Local Definition oblP_variant_def `{SI : sidx} `{@mupdGS SI Σ}
  k (P R : iProp Σ) : iProp Σ :=
  ((oblP_assigned k (1/2)%Qp ∗ P) ∨ (oblP_discharged k ∗ R))%I.
Local Definition oblP_variant_aux : seal (@oblP_variant_def). Proof. by eexists. Qed.
Definition oblP_variant := oblP_variant_aux.(unseal).
Local Definition oblP_variant_unseal :
  @oblP_variant = @oblP_variant_def := oblP_variant_aux.(seal_eq).
Global Arguments oblP_variant {SI Σ _}.

Local Definition oblP_inv_def `{SI : sidx} `{@mupdGS SI Σ}
  N k (P R : iProp Σ) : iProp Σ :=
  oblP_id k ∗ oblG_inv N k ((1/2)/2 + (1/2)/2/2)%Qp P False R.
Local Definition oblP_inv_aux : seal (@oblP_inv_def). Proof. by eexists. Qed.
Definition oblP_inv := oblP_inv_aux.(unseal).
Local Definition oblP_inv_unseal :
  @oblP_inv = @oblP_inv_def := oblP_inv_aux.(seal_eq).
Global Arguments oblP_inv {SI Σ _}.

(** ** Witness predicates *)
Local Definition witP_bound_val `{SI : sidx} `{@mupdGS SI Σ}
  k α : iProp Σ :=
  oblP_id k ∗ witG_bound k α.

Local Definition witP_cred_def `{SI : sidx} `{@mupdGS SI Σ}
  k a : iProp Σ :=
  oblP_id k ∗ witG_witness k a.
Local Definition witP_cred_aux : seal (@witP_cred_def). Proof. by eexists. Qed.
Definition witP_cred := witP_cred_aux.(unseal).
Local Definition witP_cred_unseal :
  @witP_cred = @witP_cred_def := witP_cred_aux.(seal_eq).
Global Arguments witP_cred {SI Σ _}.

Local Definition thP_done_def `{SI : sidx} `{@mupdGS SI Σ}
  i : iProp Σ :=
  othreadG_elem i ∗ othreadG_done i.
Local Definition thP_done_aux : seal (@thP_done_def). Proof. by eexists. Qed.
Definition thP_done := thP_done_aux.(unseal).
Local Definition thP_done_unseal :
  @thP_done = @thP_done_def := thP_done_aux.(seal_eq).
Global Arguments thP_done {SI Σ _}.

(** ** Witness layer: the witness bound and the initial fuel of the obligation at layer [ℓ] *)
Local Definition witP_layer_def `{SI : sidx} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ : iProp Σ :=
  (∃ μ, witP_bound_val k (η (measure_rep (ℓ, 1) μ))) ∗
  (∃ μ, oblG_bound k (measure_rep (ℓ, 1) μ)).
Local Definition witP_layer_aux : seal (@witP_layer_def). Proof. by eexists. Qed.
Definition witP_layer := witP_layer_aux.(unseal).
Local Definition witP_layer_unseal :
  @witP_layer = @witP_layer_def := witP_layer_aux.(seal_eq).
Global Arguments witP_layer {SI Σ _ _}.

(** ** Collections of fuels for the witness induction *)
Local Definition collect_fuels `{SI : sidx} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  α (F : gmap oid (ord.t * measure)) : iProp Σ :=
  ([∗ map] s ↦ '(l, m) ∈ F, oblP_fuel_val s ((measure_rep (l, 1) ((1 ⊕ ▽) × m)%M) × α)%ord).

Local Definition wit_fuels_def `{SI : sidx} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  k ℓ α (F : gmap oid (ord.t * measure)) : iProp Σ :=
  ∃ μ, ⌜ (α <= η (measure_rep (ℓ, 1) μ))%ord ⌝ ∗ witP_bound_val k α ∗ collect_fuels α F ∗
       (∃ μ, oblG_bound k (measure_rep (ℓ, 1) μ)).
Local Definition wit_fuels_aux : seal (@wit_fuels_def). Proof. by eexists. Qed.
Definition wit_fuels := wit_fuels_aux.(unseal).
Local Definition wit_fuels_unseal :
  @wit_fuels = @wit_fuels_def := wit_fuels_aux.(seal_eq).
Global Arguments wit_fuels {SI Σ _ _}.

(** Fuels for an induction on a well-founded order [ltA], embedded in the measures. *)
Local Definition embed_fuels_def `{SI : sidx} `{@mupdGS SI Σ} `{!ord_mono_fun_class}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (a : A) (F : gmap oid (ord.t * measure)) : iProp Σ :=
  collect_fuels (measure_rep (0 : ord.t, 1) (⟪wf_ltA, a⟫)%M) F.
Local Definition embed_fuels_aux : seal (@embed_fuels_def). Proof. by eexists. Qed.
Definition embed_fuels := embed_fuels_aux.(unseal).
Local Definition embed_fuels_unseal :
  @embed_fuels = @embed_fuels_def := embed_fuels_aux.(seal_eq).
Global Arguments embed_fuels {SI Σ _ _ A ltA}.

(** ** Children of a parent *)
Local Definition parP_kids_def `{SI : sidx} `{@mupdGS SI Σ}
  (p : parent) (K : gset oid) : iProp Σ :=
  match p with
  | PThread i => othreadG_elem i ∗ othreadG_exec i (1/2)%Qp ∗ oforestG_kids (PThread i) K
  | PObl k => oforestG_kids (PObl k) K
  end.
Local Definition parP_kids_aux : seal (@parP_kids_def). Proof. by eexists. Qed.
Definition parP_kids := parP_kids_aux.(unseal).
Local Definition parP_kids_unseal :
  @parP_kids = @parP_kids_def := parP_kids_aux.(seal_eq).
Global Arguments parP_kids {SI Σ _}.

(** Children of a thread and of an obligation. *)
Notation thP_kids i K := (parP_kids (PThread i) K).
Notation oblP_kids k K := (parP_kids (PObl k) K).
(** [n] units of fuel of each obligation of a set, at any layers. *)
Notation oblP_fuels K n := ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ n)%I.

(** One unit of fuel at layer [ℓ] is enough to hang below [p]: always below a thread; below an
    obligation [q], [ℓ] must be above a witness layer of [q] (given by [wl], instantiated with
    [witP_layer]). *)
Definition parent_below `{SI : sidx} {Σ : gFunctors} (wl : oid → ord.t → iProp Σ)
    (p : parent) (ℓ : ord.t) : iProp Σ :=
  match p with
  | PThread _ => True
  | PObl q => ∃ ℓq, ⌜ (ℓq < ℓ)%ordi ⌝ ∗ wl q ℓq
  end%I.
Notation parP_below p ℓ := (parent_below witP_layer p ℓ).

(** A new obligation at layer [ℓ] may be created below [p]: always below a thread; below an
    obligation [q], [ℓ] must be at least a witness layer of [q]. (A move needs a strictly larger
    layer, [parent_below]: moving an existing obligation below one of the same layer is
    unsound.) *)
Definition parent_le `{SI : sidx} {Σ : gFunctors} (wl : oid → ord.t → iProp Σ)
    (p : parent) (ℓ : ord.t) : iProp Σ :=
  match p with
  | PThread _ => True
  | PObl q => ∃ ℓq, ⌜ (ℓq <= ℓ)%ordi ⌝ ∗ wl q ℓq
  end%I.
Notation parP_le p ℓ := (parent_le witP_layer p ℓ).

Ltac unfold_opreds :=
  try rewrite !wit_fuels_unseal /wit_fuels_def;
  try rewrite /collect_fuels;
  try rewrite !thP_done_unseal /thP_done_def;
  try rewrite !parP_kids_unseal /parP_kids_def;
  try rewrite !witP_cred_unseal /witP_cred_def;
  try rewrite !witP_layer_unseal /witP_layer_def;
  try rewrite /witP_bound_val;
  try rewrite !oblP_variant_unseal /oblP_variant_def;
  try rewrite !oblP_inv_unseal /oblP_inv_def;
  try rewrite !oblP_fuel_unseal /oblP_fuel_def;
  try rewrite /oblP_fuel_val;
  try rewrite !oblP_discharged_unseal /oblP_discharged_def;
  try rewrite !oblP_assigned_unseal /oblP_assigned_def;
  try rewrite /oblP_id.

Ltac unfold_oblP_fuel :=
  try rewrite !oblP_fuel_unseal /oblP_fuel_def.


(** * Rules of the predicates (ghost updates without model change) *)
Section pred_rules.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  (** ** Instances *)
  Local Instance oblP_id_persistent k : Persistent (oblP_id k).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_discharged_persistent k : Persistent (oblP_discharged k).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_inv_persistent N k P R : Persistent (oblP_inv N k P R).
  Proof. unfold_opreds. apply _. Qed.

  Local Instance witP_bound_val_persistent k α : Persistent (witP_bound_val k α).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance witP_layer_persistent k ℓ : Persistent (witP_layer k ℓ).
  Proof. unfold_opreds. apply _. Qed.

  Global Instance thP_done_persistent i : Persistent (thP_done i).
  Proof. unfold_opreds. apply _. Qed.

  Local Instance oblP_id_timeless k : Timeless (oblP_id k).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_assigned_timeless k q : Timeless (oblP_assigned k q).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_discharged_timeless k : Timeless (oblP_discharged k).
  Proof. unfold_opreds. apply _. Qed.
  Local Instance oblP_fuel_val_timeless k α : Timeless (oblP_fuel_val k α).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_fuel_timeless k ℓ μ : Timeless (oblP_fuel k ℓ μ).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance oblP_variant_timeless k P R :
    Timeless P → Timeless R → Timeless (oblP_variant k P R).
  Proof. intros. unfold_opreds. apply _. Qed.

  Local Instance witP_bound_val_timeless k α : Timeless (witP_bound_val k α).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance witP_layer_timeless k ℓ : Timeless (witP_layer k ℓ).
  Proof. unfold_opreds. apply _. Qed.
  Global Instance witP_cred_timeless k a : Timeless (witP_cred k a).
  Proof. unfold_opreds. apply _. Qed.

  Global Instance oblP_inv_contractive_1 N k R : Contractive (λ P, oblP_inv N k P R).
  Proof.
    unfold_opreds. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
  Qed.
  Global Instance oblP_inv_contractive_2 N k P : Contractive (λ R, oblP_inv N k P R).
  Proof.
    unfold_opreds. rewrite /oblG_elem /oblG_inv /oblG_variant. solve_contractive.
  Qed.

  Global Instance oblP_inv_ne_1 N k R : NonExpansive (λ P, oblP_inv N k P R).
  Proof. apply _. Qed.
  Global Instance oblP_inv_ne_2 N k P : NonExpansive (λ R, oblP_inv N k P R).
  Proof. apply _. Qed.

  Global Instance oblP_inv_proper_1 N k R : Proper (equiv ==> equiv) (λ P, oblP_inv N k P R).
  Proof.
    unfold_opreds. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
  Qed.
  Global Instance oblP_inv_proper_2 N k P : Proper (equiv ==> equiv) (λ R, oblP_inv N k P R).
  Proof.
    unfold_opreds. repeat intro. rewrite /oblG_inv /oblG_variant H. done.
  Qed.

  Global Instance oblP_assigned_fractional k : Fractional (oblP_assigned k).
  Proof.
    rewrite !oblP_assigned_unseal /oblP_assigned_def. intros p q. iSplit.
    - iIntros "(#$& [Gv1 Gv2])". rewrite !Qp.div_add_distr.
      iDestruct "Gv1" as "[Gv1 Gv1']". iDestruct "Gv2" as "[Gv2 Gv2']".
      iCombine "Gv1 Gv2" as "$". iCombine "Gv1' Gv2'" as "$".
    - iIntros "((#$& [Gv1 Gv2])& _& [Gv3 Gv4])". rewrite !Qp.div_add_distr.
      iCombine "Gv1 Gv3" as "Gv1". iSplitL "Gv1"; iFrame. iSplitR "Gv4"; iFrame.
  Qed.
  Global Instance oblP_assigned_as_fractional k q : AsFractional (oblP_assigned k q) (oblP_assigned k) q.
  Proof. split; [auto|apply _]. Qed.

  (** ** oblP_assigned and oblP_discharged rules *)
  Lemma oblP_assigned_discharged_false k q :
    oblP_assigned k q -∗ oblP_discharged k -∗ False.
  Proof.
    unfold_opreds. iIntros "(#Ge& Gl) (_& #Gu)".
    iPoseProof (oblG_assigned_discharged_false with "[$]") as "%". done.
  Qed.

  (** ** Fuel values (internal) *)
  Local Open Scope ord.

  Local Lemma oblP_fuel_val_eq k a0 a1 :
    (a0 == a1) → oblP_fuel_val k a0 = oblP_fuel_val k a1.
  Proof.
    unfold_opreds. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
  Qed.

  Local Lemma oblP_fuel_val_mon k a0 a1 :
    (a0 <= a1)%ord → oblP_fuel_val k a1 ==∗ oblP_fuel_val k a0.
  Proof.
    unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
  Qed.

  Local Lemma oblP_fuel_val_add k a0 a1 :
    oblP_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
  Proof.
    unfold_opreds. rewrite oblG_fuel_split. iSplit.
    - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
    - iIntros "((B1& P1)& (B2& P2))"; iFrame.
  Qed.

  Local Lemma oblP_fuel_val_mon_split k a0 a1 a2 :
    ((a0 ⊕ a1) <= a2)%ord → oblP_fuel_val k a2 ==∗ oblP_fuel_val k a0 ∗ oblP_fuel_val k a1.
  Proof.
    unfold_opreds. iIntros (Hle) "(#Be& P)".
    iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
    iFrame; eauto.
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

  (** ** oblP_fuel rules *)
  Lemma oblP_fuel_layer_eq k ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    oblP_fuel k ℓ1 μ = oblP_fuel k ℓ2 μ.
  Proof.
    unfold_oblP_fuel. intros.
    apply oblP_fuel_val_eq. apply measure_rep_layer_eq. split; auto.
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
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    oblP_fuel k ℓ μ1 = oblP_fuel k ℓ μ2.
  Proof.
    unfold_oblP_fuel. intros. rewrite !measure_rep_mult.
    apply oblP_fuel_val_eq. rewrite !H. done.
  Qed.
  Lemma oblP_fuel_eq_list K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.
  Lemma oblP_fuel_eq_set K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite oblP_fuel_eq; eauto. Qed.

  Lemma oblP_fuel_mon_gen k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep (ℓ1, 1) (μ1)%M <= measure_rep (ℓ2, 1) (μ2)%M)%ord →
    oblP_fuel k ℓ2 μ2 ==∗ oblP_fuel k ℓ1 μ1.
  Proof.
    unfold_oblP_fuel. intros. apply oblP_fuel_val_mon.
    rewrite !measure_rep_mult. etrans; first eapply Jacobsthal.le_mult_r; eauto.
    eapply Jacobsthal.le_mult_l. apply measure_rep_layer_le_proper.
    apply classicOrd.le_eq_or_lt in H. destruct H.
    - right. econstructor 1. auto.
    - left. split; auto.
  Qed.
  Lemma oblP_fuel_mon_gen_list K ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep (ℓ1, 1) (μ1)%M <= measure_rep (ℓ2, 1) (μ2)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ1).
  Proof.
    iIntros (LL LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
  Qed.
  Lemma oblP_fuel_mon_gen_set K ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep (ℓ1, 1) (μ1)%M <= measure_rep (ℓ2, 1) (μ2)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ1).
  Proof.
    iIntros (LL LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
  Qed.

  Lemma oblP_fuel_mon k ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M <= measure_rep (ℓ, 1) (μ2)%M)%ord →
    oblP_fuel k ℓ μ2 ==∗ oblP_fuel k ℓ μ1.
  Proof. intros. apply oblP_fuel_mon_gen; auto. done. Qed.
  Lemma oblP_fuel_mon_list K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M <= measure_rep (ℓ, 1) (μ2)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon.
  Qed.
  Lemma oblP_fuel_mon_set K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M <= measure_rep (ℓ, 1) (μ2)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon.
  Qed.

  Lemma oblP_fuel_layer_mon k ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    oblP_fuel k ℓ2 μ ==∗ oblP_fuel k ℓ1 μ.
  Proof.
    iIntros (LE) "H". iApply (oblP_fuel_mon_gen with "H"). 1: auto.
    apply measure_rep_layer_le_proper.
    apply classicOrd.le_eq_or_lt in LE. destruct LE.
    - right. econstructor; auto.
    - left. econstructor; auto.
  Qed.
  Lemma oblP_fuel_layer_mon_list K ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_layer_mon.
  Qed.
  Lemma oblP_fuel_layer_mon_set K ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_layer_mon.
  Qed.

  Lemma oblP_fuel_mon_split k ℓ μ1 μ2 μ3 :
    ((measure_rep (ℓ, 1) (μ1)%M ⊕ measure_rep (ℓ, 1) (μ2)%M) <= measure_rep (ℓ, 1) (μ3)%M)%ord →
    oblP_fuel k ℓ μ3 ==∗ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
  Proof.
    unfold_oblP_fuel. intros. apply oblP_fuel_val_mon_split.
    rewrite !measure_rep_mult. rewrite -ClassicJacobsthal.mult_dist.
    apply Jacobsthal.le_mult_r. auto.
  Qed.
  Lemma oblP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
    ((measure_rep (ℓ, 1) (μ1)%M ⊕ measure_rep (ℓ, 1) (μ2)%M) <= measure_rep (ℓ, 1) (μ3)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ3)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!> % % %". iApply oblP_fuel_mon_split; auto.
  Qed.
  Lemma oblP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
    ((measure_rep (ℓ, 1) (μ1)%M ⊕ measure_rep (ℓ, 1) (μ2)%M) <= measure_rep (ℓ, 1) (μ3)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ3)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
    iIntros "!> % %". iApply oblP_fuel_mon_split; auto.
  Qed.

  Lemma oblP_fuel_lt k ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    oblP_fuel k ℓ μ2 ⊢ |==> oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ (1)%M.
  Proof.
    unfold_oblP_fuel. intros. rewrite -oblP_fuel_val_add.
    iIntros "H". iApply oblP_fuel_val_mon. 2: iFrame.
    rewrite !measure_rep_mult. rewrite -ClassicJacobsthal.mult_dist.
    apply Jacobsthal.le_mult_r. rewrite measure_rep_nat. rewrite Hessenberg.add_comm -ord_S_add.
    apply Ord.S_supremum; auto.
  Qed.
  Lemma oblP_fuel_lt_list K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_lt.
  Qed.
  Lemma oblP_fuel_lt_set K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_lt.
  Qed.

  (** Rules for the measure syntax *)
  Lemma oblP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
    ltA a1 a2 →
    oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ oblP_fuel k ℓ 1.
  Proof.
    intros. apply oblP_fuel_lt. apply measure_rep_embed_lt. auto.
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
    intros. apply oblP_fuel_lt. apply measure_rep_large_lt.
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
    unfold_oblP_fuel. rewrite (measure_rep_mult _ _ (μ1 ⊕ μ2)%M) (measure_rep_add _ μ1 μ2).
    etrans.
    { erewrite oblP_fuel_val_eq. 2: apply ClassicJacobsthal.mult_dist. reflexivity. }
    rewrite -!measure_rep_mult. apply oblP_fuel_val_add.
  Qed.
  Lemma oblP_fuel_add_list K ℓ μ1 μ2 :
    ([∗ list] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M)
    ⊣⊢ ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblP_fuel_add.
  Qed.
  Lemma oblP_fuel_add_set K ℓ μ1 μ2 :
    ([∗ set] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M)
    ⊣⊢ ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblP_fuel_add.
  Qed.

  Lemma oblP_fuel_mult k ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    oblP_fuel k ℓ (s × μ2)%M ⊢ |==> oblP_fuel k ℓ (s × μ1)%M ∗ oblP_fuel k ℓ s.
  Proof.
    unfold_oblP_fuel. intros. iIntros "H".
    rewrite (oblP_fuel_val_eq _ (measure_rep (ℓ, 1) ((1 ⊕ ▽) × s × μ2)%M) (measure_rep (ℓ, 1) (((1 ⊕ ▽) × s) × μ2)%M)); cycle 1.
    { rewrite !measure_rep_mult. rewrite -ClassicJacobsthal.mult_assoc. done. }
    rewrite !measure_rep_mult. iMod (oblP_fuel_val_mult with "H") as "[H $]". 1: eauto.
    erewrite oblP_fuel_val_eq. 1: by iFrame.
    rewrite -ClassicJacobsthal.mult_assoc. done.
  Qed.
  Lemma oblP_fuel_mult_list K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ s).
  Proof.
    rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_mult. auto.
  Qed.
  Lemma oblP_fuel_mult_set K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ s).
  Proof.
    rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_mult. auto.
  Qed.

  Lemma oblP_fuel_expn k ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    (Ord.O < measure_rep (ℓ, 1) s)%ord →
    oblP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> oblP_fuel k ℓ ((s ↑ μ1) × s)%M.
  Proof.
    unfold_oblP_fuel. intros LT Pos. rewrite !measure_rep_mult !measure_rep_expn.
    iIntros "H". iPoseProof (oblP_fuel_val_mon with "H") as "$".
    apply Jacobsthal.le_mult_r. rewrite -Jacobsthal.expn_S. 2: auto.
    eapply Jacobsthal.le_expn_r. apply Ord.S_supremum; auto.
  Qed.
  Lemma oblP_fuel_expn_list K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    (Ord.O < measure_rep (ℓ, 1) s)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_expn; auto.
  Qed.
  Lemma oblP_fuel_expn_set K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    (Ord.O < measure_rep (ℓ, 1) s)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_expn; auto.
  Qed.

  Lemma oblP_fuel_extend k ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    oblP_fuel k ℓ2 1 ⊢ |==> oblP_fuel k ℓ1 μ.
  Proof.
    unfold_oblP_fuel. iIntros (LT) "H".
    iPoseProof (oblP_fuel_val_mon with "H") as "$".
    rewrite (measure_rep_mult (ℓ2, 1)) measure_rep_nat Jacobsthal.mult_1_r.
    etrans; first eapply η_mono. etrans; first eapply (measure_rep_extend _ (ℓ2, 1)).
    { econstructor 1. auto. }
    rewrite measure_rep_add measure_rep_nat. apply Hessenberg.add_base_r.
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

  (** ** Fuel of sets of obligations *)
  Lemma oblP_fuel_add_nat m1 m2 n k ℓ :
    (n = m1 + m2)%nat →
    oblP_fuel k ℓ n ⊣⊢ (oblP_fuel k ℓ m1 ∗ oblP_fuel k ℓ m2)%I.
  Proof.
    intros ->. rewrite -oblP_fuel_add. erewrite oblP_fuel_eq. 1: reflexivity.
    rewrite measure_rep_add !measure_rep_nat. rewrite -Hessenberg.add_from_nat. done.
  Qed.

  Lemma oblP_fuels_add_gen m1 m2 K :
    oblP_fuels K (m1 ⊕ m2)%M ⊢ oblP_fuels K m1 ∗ oblP_fuels K m2.
  Proof.
    rewrite -big_sepS_sep. iIntros "H"; iApply (big_sepS_impl with "H"); iIntros "!> %% H".
    iDestruct "H" as "(%& H)". iPoseProof (oblP_fuel_add with "H") as "[$ $]".
  Qed.

  Lemma oblP_fuels_add (n m : nat) K :
    oblP_fuels K (n + m)%nat ⊢ oblP_fuels K n ∗ oblP_fuels K m.
  Proof.
    rewrite -big_sepS_sep. iIntros "H"; iApply (big_sepS_impl with "H"); iIntros "!> %% H".
    iDestruct "H" as "(%& H)". iPoseProof (oblP_fuel_add_nat with "H") as "[H F]". 1: eauto. iFrame.
  Qed.

  Lemma oblP_fuels_add_nat (m1 m2 n : nat) K :
    (n = m1 + m2)%nat →
    oblP_fuels K n ⊢ oblP_fuels K m1 ∗ oblP_fuels K m2.
  Proof. intros ->. apply oblP_fuels_add. Qed.

  Lemma oblP_fuels_init K m ℓ :
    ([∗ set] k ∈ K, oblP_fuel k ℓ m)%I ⊢ oblP_fuels K m.
  Proof. iIntros "H". iApply (big_sepS_impl with "H"). iIntros "!> %% $". Qed.

  Lemma oblP_fuels_add_obl K k ℓ n :
    oblP_fuel k ℓ n -∗ oblP_fuels K n -∗ oblP_fuels ({[k]} ∪ K) n.
  Proof.
    iIntros "H2 H1". iApply (big_sepS_union_2 with "[H2] H1"). iApply big_sepS_singleton. iFrame.
  Qed.

  Lemma oblP_fuels_add_obls K1 K2 n :
    oblP_fuels K1 n -∗ oblP_fuels K2 n -∗ oblP_fuels (K1 ∪ K2) n.
  Proof. iIntros "H1 H2". iApply (big_sepS_union_2 with "H1 H2"). Qed.

  Lemma oblP_fuels_remove_obl k K n :
    oblP_fuels K n -∗ oblP_fuels (K ∖ {[k]}) n.
  Proof.
    iIntros "H". destruct (decide (k ∈ K)); cycle 1.
    { replace (K ∖ {[k]}) with K by set_solver. auto. }
    iPoseProof (big_sepS_delete _ _ k with "H") as "[_ $]". auto.
  Qed.

  Lemma oblP_fuels_remove_obls K2 K1 n :
    oblP_fuels K1 n -∗ oblP_fuels (K1 ∖ K2) n.
  Proof.
    rewrite -(difference_union_intersection_L K1 K2).
    iIntros "H". iPoseProof (big_sepS_union with "H") as "[H1 H2]". 1: set_solver.
    rewrite (difference_union_intersection_L K1 K2). iFrame.
  Qed.

  (** ** Witness bounds (internal) *)
  Local Lemma witP_bound_val_mon k a0 a1 :
    (a0 <= a1)%ord → witP_bound_val k a0 ==∗ witP_bound_val k a1.
  Proof.
    unfold_opreds. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_bound_mon.
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

  (** ** witP_cred rules *)
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

End pred_rules.

(** * Collections of fuels for the witness induction *)
Section witness_fuels.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  (** ** Instances *)
  Global Instance wit_fuels_empty_persistent k ℓ α : Persistent (wit_fuels k ℓ α ∅).
  Proof. unfold_opreds. apply _. Qed.

  Global Instance wit_fuels_timeless k ℓ α F : Timeless (wit_fuels k ℓ α F).
  Proof. unfold_opreds. apply _. Qed.

  Global Instance parP_kids_timeless p K : Timeless (parP_kids p K).
  Proof. unfold_opreds. destruct p; apply _. Qed.

  (** ** witP_layer *)
  Lemma witP_layer_oblG_bound k ℓ :
    witP_layer k ℓ -∗ ∃ μ, oblG_bound k (measure_rep (ℓ, 1) μ).
  Proof. rewrite witP_layer_unseal /witP_layer_def. iIntros "[_ $]". Qed.

  (** ** collect_fuels rules *)
  Local Lemma collect_fuels_add α F f ℓ ν μ :
    (α <= measure_rep (ℓ, 1) ν)%ord →
    collect_fuels α F -∗ oblP_fuel f ℓ (μ × ν)%M ==∗ collect_fuels α (<[f:=(ℓ, μ)]>F).
  Proof.
    iIntros (LT) "Wfs Gf". rewrite /collect_fuels.
    unfold_oblP_fuel.
    iMod (oblP_fuel_val_mon _ ((measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M) × α)%ord with "Gf") as "F".
    { rewrite !measure_rep_mult. rewrite -ClassicJacobsthal.mult_assoc. apply Jacobsthal.le_mult_r. auto. }
    iApply (big_sepM_insert_delete _ _ f). destruct (F !! f) eqn:LUF.
    - iPoseProof (big_sepM_delete _ _ f with "Wfs") as "[_ $]"; eauto.
    - rewrite delete_id; auto. by iFrame.
  Qed.

  Local Lemma collect_fuels_decr α α0 F :
    (α0 < α)%ord →
    collect_fuels α F ==∗
    (collect_fuels α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m)).
  Proof.
    rewrite /collect_fuels. iIntros (LT) "Fs".
    rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
    iIntros "!> % % % H". destruct x as (l& m).
    rewrite oblP_fuel_unseal /oblP_fuel_def. rewrite -oblP_fuel_val_add. iApply (oblP_fuel_val_mon with "H").
    rewrite Hessenberg.add_comm -Jacobsthal.mult_S.
    apply Jacobsthal.le_mult_r. apply Ord.S_supremum; auto.
  Qed.

  (** ** wit_fuels rules *)
  Lemma wit_fuels_init k ℓ :
    witP_layer k ℓ -∗ ∃ α, wit_fuels k ℓ α ∅.
  Proof.
    rewrite witP_layer_unseal /witP_layer_def wit_fuels_unseal /wit_fuels_def /collect_fuels.
    iIntros "[(%μ& $) $]". iExists μ. rewrite big_sepM_empty. by iSplit.
  Qed.

  Lemma wit_fuels_witP_layer k ℓ α F :
    wit_fuels k ℓ α F ==∗ witP_layer k ℓ.
  Proof.
    iIntros "Wl". rewrite !wit_fuels_unseal /wit_fuels_def !witP_layer_unseal /witP_layer_def.
    iDestruct "Wl" as "(%& %& #Wb& _& $)".
    iExists μ. iApply witP_bound_val_mon; eauto.
  Qed.

  Lemma wit_fuels_add k ℓ1 α F f ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    wit_fuels k ℓ1 α F -∗ oblP_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F).
  Proof.
    iIntros (LT) "Wfs Gf". rewrite !wit_fuels_unseal /wit_fuels_def.
    iDestruct "Wfs" as "(%& %& $& M& $)".
    iExists _. iSplitR; first eauto.
    iApply (collect_fuels_add with "M Gf").
    etrans; first eauto. apply measure_rep_extend. econstructor 1; eauto.
  Qed.

  Lemma wit_fuels_decr k ℓ α F :
    wit_fuels k ℓ α F -∗ witP_cred k Ord.one ==∗
    ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗
          ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m).
  Proof.
    rewrite wit_fuels_unseal /wit_fuels_def. iIntros "(%& %& #Wbk& Fs& #B) Wk".
    iMod (witP_bound_val_spend_one with "Wbk Wk") as "(%& %& #Wbk2)".
    iExists a0. iSplitR; first done. iFrame "Wbk2 B". assert (a0 <= η (measure_rep (ℓ, 1) μ))%ord.
    { etransitivity; last eauto. apply WFOCM.lt_le. auto. }
    iFrame (H1). iApply (collect_fuels_decr with "Fs"). auto.
  Qed.

  (** ** embed_fuels rules *)
  Lemma embed_fuels_init {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a :
    ⊢ embed_fuels wf_ltA a ∅.
  Proof. rewrite !embed_fuels_unseal /embed_fuels_def /collect_fuels big_sepM_empty. done. Qed.

  Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
    a F G l m :
    embed_fuels wf_ltA a F -∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ℵ)%M) ==∗
    embed_fuels wf_ltA a ((gset_to_gmap (l, m) G) ∪ F).
  Proof.
    rewrite !embed_fuels_unseal /embed_fuels_def.
    revert F. induction G as [|g G Hg IH] using set_ind_L; intros F; iIntros "Gfs Fs".
    { rewrite gset_to_gmap_empty left_id_L. by iFrame. }
    rewrite big_sepS_insert; last done. iDestruct "Fs" as "[Fg Fs]".
    iMod (IH with "Gfs Fs") as "Gfs".
    rewrite gset_to_gmap_union_singleton -insert_union_l.
    iApply (collect_fuels_add with "Gfs Fg").
    rewrite measure_rep_embed measure_rep_large. apply Ord.lt_le, Ord.large_lt_from_wf.
  Qed.

  Lemma embed_fuels_decr {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a a' F :
    ltA a' a →
    embed_fuels wf_ltA a F ==∗
    embed_fuels wf_ltA a' F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m).
  Proof.
    rewrite embed_fuels_unseal /embed_fuels_def.
    intros LT. apply (collect_fuels_decr). apply measure_rep_embed_lt. auto.
  Qed.

  (** ** Witness induction over obligation fuel *)
  Lemma wit_fuels_add_map_gen k ℓ α F (G : gmap oid (ord.t * measure)) :
    wit_fuels k ℓ α F -∗
    ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (ℓ < l)%ordi ⌝ ∗ oblP_fuel g l (m × ▽)%M) ==∗
    wit_fuels k ℓ α (G ∪ F).
  Proof.
    revert F. induction G as [|f x G Hf IH] using map_ind; iIntros (F) "W Fs".
    { rewrite left_id_L. by iFrame. }
    destruct x as [l m]. rewrite big_sepM_insert; last done.
    iDestruct "Fs" as "((%Hl& Ff)& Fs)".
    iMod (IH with "W Fs") as "W". rewrite -insert_union_l.
    iApply (wit_fuels_add with "W Ff"). done.
  Qed.

  Lemma wit_fuels_add_map k ℓ α F G l m :
    (ℓ < l)%ordi →
    wit_fuels k ℓ α F -∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ▽)%M) ==∗
    wit_fuels k ℓ α ((gset_to_gmap (l, m) G) ∪ F).
  Proof.
    iIntros (Hl) "W Fs". iApply (wit_fuels_add_map_gen with "W").
    rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Fs"). iIntros "!> %% $". done.
  Qed.

  Lemma wit_fuels_ind k ℓ α F (P : iProp Σ) :
    □ ((witP_cred k Ord.one ==∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m) ∗ P) ==∗ P) ∗
    wit_fuels k ℓ α F
    ⊢ |==> P.
  Proof.
    iIntros "[#H WF]". iInduction α as [α IH] using (well_founded_ind WFOCM.lt_wf).
    iApply "H". iIntros "Wc". iMod (wit_fuels_decr with "WF Wc") as "(%&%& WF& Fs)".
    iFrame "Fs". iApply ("IH" with "[//] WF").
  Qed.

  Lemma wit_layer_ind k ℓ G l m (P : iProp Σ) :
    (ℓ < l)%ordi →
    □ ((witP_cred k Ord.one ==∗ ([∗ set] g ∈ G, oblP_fuel g l m) ∗ P) ==∗ P) ∗
    witP_layer k ℓ ∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ▽)%M)
    ⊢ |==> P.
  Proof.
    iIntros (LT) "(#IND& #Wl& FG)". iPoseProof (wit_fuels_init with "Wl") as "[% Wf0]".
    iMod (wit_fuels_add_map with "Wf0 FG") as "WF". 1: auto.
    iApply (wit_fuels_ind with "[IND $WF]").
    iIntros "!> H". rewrite map_union_empty big_sepM_gset_to_gmap.
    iApply ("IND" with "H").
  Qed.

End witness_fuels.

(** * Rules with model updates *)
Section mupd_rules.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  (** ** Measures *)
  (** A unit at a higher layer dominates any fuel of a lower layer. *)
  Lemma layer_dominates ℓq ℓ μq :
    (ℓq < ℓ)%ordi → (measure_rep (ℓq, 1) μq < measure_rep (ℓ, 1) (▽)%M)%ord.
  Proof.
    intros Hl.
    assert (H1 : (η (measure_rep (ℓq, 1) μq) <= measure_rep (ℓ, 0) ▽%M)%ord).
    { apply measure_rep_extend. by econstructor 1. }
    assert (H2 : (η (measure_rep (ℓ, 0) (▽ ⊕ 1)%M) <= measure_rep (ℓ, 1) ▽%M)%ord).
    { apply measure_rep_extend. econstructor 2.
      - left. reflexivity.
      - lia. }
    eapply Ord.le_lt_lt; first apply η_mono.
    eapply Ord.le_lt_lt; first exact H1.
    eapply Ord.lt_le_lt; last exact H2.
    eapply Ord.lt_le_lt; last apply η_mono.
    rewrite measure_rep_add measure_rep_nat.
    apply Hessenberg.add_lt_l. rewrite Ord.from_nat_1. apply Ord.S_pos.
  Qed.

  (** The bound of a parent at a layer [ℓq ≤ ℓ] is below [μq ⊕ 1] at [ℓ]. *)
  Lemma layer_le_bound ℓq ℓ μq :
    (ℓq <= ℓ)%ordi → (measure_rep (ℓq, 1) μq < measure_rep (ℓ, 1) (μq ⊕ 1)%M)%ord.
  Proof.
    intros Hl.
    assert (H1 : (measure_rep (ℓq, 1) μq <= measure_rep (ℓ, 1) μq)%ord).
    { apply measure_rep_layer_le_proper. apply classicOrd.le_eq_or_lt in Hl. destruct Hl as [Hl|Hl].
      - right. econstructor; auto.
      - left. econstructor; auto. }
    eapply Ord.le_lt_lt; first exact H1.
    rewrite measure_rep_add measure_rep_nat.
    apply Hessenberg.add_lt_l. rewrite Ord.from_nat_1. apply Ord.S_pos.
  Qed.

  (** ** Children predicates *)
  Lemma parP_kids_frag p K :
    parP_kids p K ⊣⊢
    (match p with
     | PThread i => othreadG_elem i ∗ othreadG_exec i (1/2)%Qp
     | PObl _ => True
     end) ∗ oforestG_kids p K.
  Proof.
    unfold_opreds. destruct p.
    - by rewrite assoc.
    - by rewrite left_id.
  Qed.

  (** ** Unfolding the predicates (for the model-level proofs) *)
  Lemma oblP_assigned_unfold k q :
    oblP_assigned k q ⊣⊢ oblG_elem k ∗ oblG_assigned k false (q/2 + q/2/2)%Qp.
  Proof. by unfold_opreds. Qed.
  Lemma oblP_discharged_unfold k : oblP_discharged k ⊣⊢ oblG_elem k ∗ oblG_discharged k.
  Proof. by unfold_opreds. Qed.
  Lemma oblP_fuel_unfold k ℓ μ :
    oblP_fuel k ℓ μ ⊣⊢ oblG_elem k ∗ oblG_fuel k (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M).
  Proof. by unfold_opreds. Qed.
  Lemma witP_layer_unfold k ℓ :
    witP_layer k ℓ ⊣⊢
    (∃ μ, oblG_elem k ∗ witG_bound k (η (measure_rep (ℓ, 1) μ))) ∗
    (∃ μ, oblG_bound k (measure_rep (ℓ, 1) μ)).
  Proof. by unfold_opreds. Qed.
  Lemma witP_cred_unfold k a : witP_cred k a ⊣⊢ oblG_elem k ∗ witG_witness k a.
  Proof. by unfold_opreds. Qed.
  Lemma thP_done_unfold i : thP_done i ⊣⊢ othreadG_elem i ∗ othreadG_done i.
  Proof. by unfold_opreds. Qed.

  (** ** A round without change of the obligations *)
  Lemma mupd_ghost_round n Θ P :
    (∀ Ω, osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ oforest Ω Θ ==∗
          osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ oforest Ω Θ ∗ P) -∗
    |=[n,Θ]=>m P.
  Proof.
    iIntros "H". iApply mupd_nd_step. iIntros (????) "(HI& S& T& A& F& W& %GWI)".
    iMod ("H" with "[$S $T $A $F]") as "(S& T& A& F& P)".
    iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
    iModIntro. iExists Ω1. iSplitR; first (iPureIntro; apply obls_ndf_refl).
    iIntros (? [WStep GWI2]).
    pose proof (wits_lef_same_wits_mon _ _ _ GWI (wits_ndf_wits_lef _ _ WStep) GWI2) as WMon.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    rewrite /model_interp. iFrame "HI S T A F W". iSplitR; eauto.
  Qed.

  (** ** A round in which obligations may make progress (e.g. change owners) *)
  Lemma mupd_model_round n Θ P :
    (∀ Ω, osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ oforest Ω Θ ==∗
          ∃ Ω', ⌜ obls_ndf Ω Ω' ∧ dom Ω' = dom Ω ⌝ ∗
                osat Ω' ∗ othread Θ ∗ oassigned (dom Ω') ∗ oforest Ω' Θ ∗ P) -∗
    |=[n,Θ]=>m P.
  Proof.
    iIntros "H". iApply mupd_nd_step. iIntros (????) "(HI& S& T& A& F& W& %GWI)".
    iMod ("H" with "[$S $T $A $F]") as "(%Ω2& [%Hndf %Hdom]& S& T& A& F& P)".
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI"; first done.
    { by apply obls_lef_obls_le, obls_ndf_obls_lef. }
    iModIntro. iExists Ω2. iSplitR; first done.
    iIntros (W2 [WStep GWI2]).
    assert (WMon : wits_mon W1 W2).
    { apply wits_ndf_wits_mon; first done.
      apply owit_inv_dom in GWI, GWI2. by rewrite -GWI2 Hdom GWI. }
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    rewrite /model_interp. iFrame "HI S T A F W". iSplitR; eauto.
  Qed.

  (** ** Thread termination *)
  Lemma thread_terminate_mupd n Θ i :
    parP_kids (PThread i) ∅ -∗ |=[n,Θ]=>m thP_done i.
  Proof.
    rewrite parP_kids_frag. unfold_opreds.
    iIntros "((#Te& Tx)& Kd)". iApply mupd_ghost_round. iIntros (Ω) "(S& T& A& F)".
    iPoseProof (othread_elem with "[$T $Te]") as "%Ini".
    iMod (oforest_exec_to_done with "[$T $F $Tx $Kd]") as "(T& F& #Td)"; first done.
    iModIntro. by iFrame "S T A F Te Td".
  Qed.

  (** ** A new live obligation below [p]
      Below an obligation [q] the new obligation may sit at [q]'s own layer: its model fuel is
      chosen here, so its piece above [q] is paid by [q]'s fuel bound. *)
  Lemma obl_new_mupd n Θ p K ℓ μ :
    (match p with
     | PThread _ => True
     | PObl q => ∃ ℓq, ⌜ (ℓq <= ℓ)%ordi ⌝ ∗ witP_layer q ℓq
     end) -∗
    parP_kids p K -∗
    |=[n,Θ]=>m ∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ parP_kids (PObl k) ∅ ∗
                   oblP_assigned k 1 ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "Bp Kp". iDestruct (parP_kids_frag with "Kp") as "[Kx Kp]".
    iApply mupd_nd_step. iIntros (????) "(HI& S& T& A& F& W& %GWI)".
    (* The owner of the new obligation, and the bound on the parent's fuel. *)
    (* The piece of the new obligation above its parent: [ν] at layer [ℓ], above the
       parent's fuel bound [μq] at layer [ℓq ≤ ℓ]. *)
    iAssert (⌜ ∃ t ν, match p with
                      | PThread j => j = t
                      | PObl q => obl_owner_of Ω1 q = Some t ∧
                                  (obl_fuel_of Ω1 q < measure_rep (ℓ, 1) ν)%ord
                      end ⌝)%I as %[t [ν Hpi]].
    { destruct p as [j|q].
      - iPureIntro. exists j, (▽)%M. done.
      - iDestruct "Bp" as "(%ℓq& %Hl& Wq)".
        iPoseProof (witP_layer_oblG_bound with "Wq") as "(%μq& Bq)".
        iDestruct (oforest_obl_fuel_bound with "F Kp Bq") as %[Hle (aq& iq& Hq)].
        iPureIntro. exists iq, (μq ⊕ 1)%M. split.
        + by rewrite /obl_owner_of Hq.
        + eapply Ord.le_lt_lt; first done. by apply layer_le_bound. }
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& Hk).
    iMod (osat_alloc_obl_assigned _ k false
            (measure_rep (ℓ, 1) ((((1 ⊕ ▽) × μ) ⊕ ▽) ⊕ ν)%M) t with "S")
      as "(S& #Gwf& #Ge& Gl& Gf& Go& %OStep)".
    { by apply not_elem_of_dom. }
    iEval (rewrite measure_rep_add) in "Gf". iPoseProof (oblG_fuel_split with "Gf") as "[Gf Gπ]".
    iEval (rewrite measure_rep_add) in "Gf". iPoseProof (oblG_fuel_split with "Gf") as "[Gu _]".
    iMod (oforest_alloc_obl _ _ p K k _ t _ with "[$S $T $F $Kp $Ge $Go $Gwf Gπ]")
      as "(S& T& F& %Nk& Kp& Kk& #Ei& Oo& Ok)".
    { done. }
    { destruct p as [j|q]; first done. destruct Hpi as [Hq Hlt]. split; first done.
      eapply Ord.lt_le_lt; first done. rewrite !measure_rep_add. apply Hessenberg.add_base_r. }
    { reflexivity. }
    { destruct p as [j|q]; first done. iExists _. iFrame "Gπ". iPureIntro. apply Hpi. }
    iMod (owit_alloc_witness_assigned _ k
            (η (measure_rep (ℓ, 1) ((((1 ⊕ ▽) × μ) ⊕ ▽) ⊕ ν)%M)) with "W") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Ok Oo]") as "A".
    { iLeft. iExists t. iFrame "Ok Oo Ei". }
    iMod (model_history_interp_step _ _ n n _
            (<[k:=obl_assigned (OC:=ord_obl_class) (measure_rep (ℓ, 1) ((((1 ⊕ ▽) × μ) ⊕ ▽) ⊕ ν)%M) t]> Ω1)
           with "HI") as "HI".
    { done. }
    { apply obls_lef_obls_le, obls_ndf_obls_lef. by apply obls_ndf_insert_fresh. }
    iModIntro.
    iExists (<[k:=obl_assigned (OC:=ord_obl_class)
                    (measure_rep (ℓ, 1) ((((1 ⊕ ▽) × μ) ⊕ ▽) ⊕ ν)%M) t]> Ω1).
    iSplitR.
    { iPureIntro. by apply obls_ndf_insert_fresh. }
    iIntros (W2 [WStep GWI2]) "!>".
    iPoseProof (owit_mon _ W2 with "W") as "W".
    { eapply wits_ndf_insert_wits_mon; [exact GWI|exact Hk|exact WStep|exact GWI2|].
      intros w2 Hw2. specialize (GWI2 k). rewrite lookup_insert_eq Hw2 in GWI2.
      inversion GWI2; subst. by destruct w2. }
    rewrite /model_interp. iFrame "HI S T F W". iSplitL "A".
    { rewrite dom_insert_L. by iFrame. }
    iModIntro. iExists k. iSplitR; first done.
    iSplitL "Kx Kp".
    { iApply parP_kids_frag. iFrame. }
    iSplitL "Kk".
    { iApply parP_kids_frag. by iFrame. }
    unfold_opreds. iFrame "Ge Gl Gu". iSplit.
    - iExists _. iFrame "Ww".
    - iExists _. iFrame "Gwf".
  Qed.

  (** ** A discharged obligation *)
  Lemma obl_new_discharged_mupd n Θ ℓ :
    ⊢ |=[n,Θ]=>m ∃ k, oblP_discharged k ∗ witP_layer k ℓ.
  Proof.
    iApply mupd_nd_step. iIntros (????) "(HI& S& T& A& F& W& %GWI)".
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& Hk).
    iMod (osat_alloc_obl_discharged _ k (measure_rep (ℓ, 1) 1%M) with "S")
      as "(S& #Gwf& #Ge& #Gu& _& %OStep)".
    { by apply not_elem_of_dom. }
    iMod (owit_alloc_witness_discharged _ k (η (measure_rep (ℓ, 1) 1%M)) with "[$W $Gu]")
      as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge]") as "A".
    { iRight. iFrame "Gu". }
    iPoseProof (oforest_alloc_discharged _ _ k with "F") as "F"; first done.
    iMod (model_history_interp_step _ _ n n _ (<[k:=obl_discharged]> Ω1) with "HI") as "HI".
    { done. }
    { apply obls_lef_obls_le, obls_ndf_obls_lef. by apply obls_ndf_insert_fresh. }
    iModIntro. iExists (<[k:=obl_discharged]> Ω1). iSplitR.
    { iPureIntro. by apply obls_ndf_insert_fresh. }
    iIntros (W2 [WStep GWI2]) "!>".
    iPoseProof (owit_mon _ W2 with "W") as "W".
    { eapply wits_ndf_insert_wits_mon; [exact GWI|exact Hk|exact WStep|exact GWI2|].
      intros w2 Hw2. specialize (GWI2 k). rewrite lookup_insert_eq Hw2 in GWI2.
      inversion GWI2; subst. by destruct w2. }
    rewrite /model_interp. iFrame "HI S T F W". iSplitL "A".
    { rewrite dom_insert_L. by iFrame. }
    iModIntro. iExists k. unfold_opreds. iFrame "Ge Gu". iSplit.
    - iExists _. iFrame "Ww".
    - iExists _. iFrame "Gwf".
  Qed.

  (** ** Liveness of children *)
  Lemma oblP_kids_discharged_false_mupd n Θ k K :
    parP_kids (PObl k) K -∗ oblP_discharged k -∗ |=[n,Θ]=>m False.
  Proof.
    rewrite parP_kids_frag. iIntros "[_ Kk]". unfold_opreds. iIntros "(#Ge& #Gu)".
    iApply mupd_ghost_round. iIntros (Ω) "(S& T& A& F)".
    iDestruct (oforest_kids_live with "F Kk") as %[_ Hl].
    destruct (Hl k eq_refl) as (a& t& Hka).
    iPoseProof (osat_lookup_discharged with "[$S $Ge $Gu]") as "%Hd".
    by rewrite Hka in Hd.
  Qed.

  Lemma parP_kids_discharged_mupd n Θ k p K :
    parP_kids p K -∗ oblP_discharged k -∗ |=[n,Θ]=>m ⌜ k ∉ K ⌝ ∗ parP_kids p K.
  Proof.
    iIntros "Kp Gd". iApply mupd_ghost_round. iIntros (Ω) "(S& T& A& F)".
    iAssert (⌜ k ∉ K ⌝)%I as %Hk.
    { iDestruct (parP_kids_frag with "Kp") as "[_ Kf]".
      iDestruct (oforest_kids_live with "F Kf") as %[Hl _].
      destruct (decide (k ∈ K)) as [Hin|]; last done. destruct (Hl k Hin) as (a& t& Hka).
      unfold_opreds. iDestruct "Gd" as "(#Ge& #Gu)".
      iPoseProof (osat_lookup_discharged with "[$S $Ge $Gu]") as "%Hd". by rewrite Hka in Hd. }
    iModIntro. by iFrame.
  Qed.

  (** ** Moving an obligation with its subtree *)
  (** [k] moves from [p1] to [p2], burning one unit at a layer [ℓ] that dominates [p2]. The
      unit splits into a part that [k] burns when it changes owner, and a part that is the
      new piece of [k] below an obligation. *)
  Lemma obl_move_mupd n Θ p1 p2 K1 K2 k ℓ :
    k ∈ K1 →
    (match p2 with
     | PThread _ => True
     | PObl q => ∃ ℓq, ⌜ (ℓq < ℓ)%ordi ⌝ ∗ witP_layer q ℓq
     end) -∗
    parP_kids p1 K1 -∗ parP_kids p2 K2 -∗ oblP_fuel k ℓ 1 -∗
    |=[n,Θ]=>m ⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ parP_kids p2 ({[k]} ∪ K2).
  Proof.
    iIntros (Hk) "Bp K1 K2 Fk".
    iDestruct (parP_kids_frag with "K1") as "[Kx1 K1]".
    iDestruct (parP_kids_frag with "K2") as "[Kx2 K2]".
    iDestruct (oblP_fuel_unfold with "Fk") as "[#Ek Fk]".
    set (u := measure_rep (ℓ, 1) 1%M). set (π := measure_rep (ℓ, 1) (▽)%M).
    assert (Hu : (Ord.O < u)%ord).
    { rewrite /u measure_rep_nat Ord.from_nat_1. apply Ord.S_pos. }
    iApply mupd_model_round. iIntros (Ω) "(S& T& A& F)".
    iMod (oblG_fuel_mon _ (u ⊕ π)%ord with "Fk") as "Fk".
    { rewrite /u /π measure_rep_mult measure_rep_add. rewrite (measure_rep_nat _ 1).
      rewrite Jacobsthal.mult_1_r. reflexivity. }
    iPoseProof (oblG_fuel_split with "Fk") as "[Fu Fπ]".
    iDestruct (oforest_kids_live with "F K1") as %[Hlive1 _].
    destruct (Hlive1 k Hk) as (a& t& Hka).
    (* The owner [j] of [p2], and the bound of its fuel below an obligation. *)
    iAssert (⌜ ∃ j, match p2 with
                    | PThread j' => j' = j
                    | PObl q => obl_owner_of Ω q = Some j ∧ (obl_fuel_of Ω q < π)%ord
                    end ⌝)%I as %[j Hpj].
    { destruct p2 as [j|q].
      - iPureIntro. by exists j.
      - iDestruct "Bp" as "(%ℓq& %Hl& Wq)".
        iPoseProof (witP_layer_oblG_bound with "Wq") as "(%μq& Bq)".
        iDestruct (oforest_obl_fuel_bound with "F K2 Bq") as %[Hle (aq& iq& Hq)].
        iPureIntro. exists iq. split.
        + by rewrite /obl_owner_of Hq.
        + eapply Ord.le_lt_lt; first done. by apply layer_dominates. }
    destruct (decide (t = j)) as [<-|Htj].
    - (* Same owner: no model change. *)
      iAssert (⌜ (π <= obl_fuel_of Ω k)%ord ⌝)%I as %Hπk.
      { iDestruct (osat_fuel_le with "S Fπ") as %Hle. iPureIntro.
        rewrite /obl_fuel_of Hka. by eapply Hle. }
      iMod (oforest_move_same _ _ p1 p2 K1 K2 k π with "[$F $K1 $K2 Fπ]")
        as "(%HkK2& F& K1& K2)".
      { done. }
      { destruct p2 as [j|q].
        - subst j. by rewrite /obl_owner_of Hka.
        - destruct Hpj as [Hq Hlt]. rewrite /obl_owner_of Hka. rewrite /obl_owner_of in Hq.
          rewrite Hq. split_and!; done. }
      { destruct p2; [done|iFrame]. }
      iModIntro. iExists Ω. iFrame "S T A F". iSplit.
      { iPureIntro. split; [apply obls_ndf_refl|done]. }
      iSplit; first done. iSplitL "Kx1 K1"; iApply parP_kids_frag; iFrame.
    - (* Owner change: the whole subtree of [k] moves to [j]. *)
      iMod (oforest_move_cross _ _ p1 p2 K1 K2 k t j u π with "[$S $T $A $F $K1 $K2 $Fu Fπ]")
        as "(%Ω'& (%Hndf& %Hdom& %HkK2)& S& T& A& F& K1& K2)".
      { done. }
      { by rewrite /obl_owner_of Hka. }
      { done. }
      { done. }
      { done. }
      { destruct p2; [done|iFrame]. }
      iModIntro. iExists Ω'. iFrame "S T A F". iSplit; first done.
      iSplit; first done. iSplitL "Kx1 K1"; iApply parP_kids_frag; iFrame.
  Qed.

  (** [x], a child of [k], moves up to the parent [p] of [k]: a ghost round without model
      change and without fuel. *)
  Lemma obl_move_up_mupd n Θ p K k Kk x :
    k ∈ K → x ∈ Kk →
    parP_kids p K -∗ parP_kids (PObl k) Kk -∗
    |=[n,Θ]=>m ⌜ x ∉ K ⌝ ∗ parP_kids p ({[x]} ∪ K) ∗ parP_kids (PObl k) (Kk ∖ {[x]}).
  Proof.
    iIntros (Hk Hx) "Kp Kk".
    iDestruct (parP_kids_frag with "Kp") as "[Kx Kp]".
    iDestruct (parP_kids_frag with "Kk") as "[_ Kk]".
    iApply mupd_ghost_round. iIntros (Ω) "(S& T& A& F)".
    iMod (oforest_move_up _ _ p K k Kk x with "[$F $Kp $Kk]") as "(%HxK& F& Kp& Kk)";
      [done|done|].
    iModIntro. iFrame "S T A F". iSplit; first done.
    iSplitL "Kx Kp"; iApply parP_kids_frag; by iFrame.
  Qed.

  (** ** Checking witnesses *)
  Lemma obl_check_witnesses_mupd n Θ (R : oids) :
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    |=[n,Θ]=>m ([∗ set] r ∈ R, (witP_cred r Ord.O) ∨ oblP_discharged r).
  Proof.
    unfold_opreds. iIntros "#REs".
    iApply mupd_nd_step. iIntros (????) "(HI& S& O& A& G& W& %GWI1)".
    iPoseProof (owit_get_credit_zero with "W") as "[W Ws]".
    assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
    iAssert (⌜ R ⊆ dom W1 ⌝)%I as "%RWSub".
    { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
      iPoseProof (big_sepS_delete _ _ _ INRx with "REs") as "[#Beg _]".
      iDestruct "Beg" as "(%& (%& Beg& _)& _)".
      iPoseProof (osat_elem with "[$S $Beg]") as "%". done. }
    iMod (model_history_interp_step _ _ n n _ Ω1 with "HI") as "HI". 1,2: done.
    iModIntro. iExists Ω1. iSplitR; first (iPureIntro; apply obls_ndf_refl).
    iIntros (? [WStep GWI2]).
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
    iAssert (|==> [∗ set] r ∈ R, (witG_witness r Ord.O) ∨ (oblG_discharged r))%I with "[Ws]" as ">Rs".
    { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto. iClear "REs".
      subst R. rewrite -big_sepS_bupd -big_sepM_dom. iApply (big_sepM_impl with "Ws1").
      iIntros "!> %%% H".  destruct x; eauto. }
    iCombine "REs Rs" as "Rs". iPoseProof (big_sepS_sep with "Rs") as "Rs".
    pose proof (wits_lef_same_wits_mon _ _ _ GWI1 (wits_ndf_wits_lef _ _ WStep) GWI2) as WMon.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    rewrite /model_interp. iFrame "HI S O W G A". iSplitR; eauto.
    iIntros "!> !>". iApply (big_sepS_impl with "Rs"). iIntros "!> %% (#Ge& [Ww | Gf])".
    - iLeft. iDestruct "Ge" as "(%& (%& $& _)& _)". eauto.
    - iRight. iDestruct "Ge" as "(%& (%& $& _)& _)". eauto.
  Qed.

  Lemma obl_discharge_mupd n Θ p K k :
    k ∈ K →
    parP_kids p K -∗ parP_kids (PObl k) ∅ -∗ oblP_assigned k 1 -∗
    |=[n,Θ]=>m parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hk) "Kp Kk Ga".
    iDestruct (parP_kids_frag with "Kp") as "[Kx Kp]".
    iDestruct (parP_kids_frag with "Kk") as "[_ Kk]".
    iDestruct (oblP_assigned_unfold with "Ga") as "(#Ge& Gl)".
    iApply mupd_unfold. iRight. iIntros (????) "(HI& S& T& A& F& W& %GWI)".
    iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
    destruct LUO1l as (a& t& LUO1l).
    iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%t'& Go1& Oo1& _) | #Gu])".
    { apply elem_of_dom. eauto. }
    2:{ iExFalso. iPoseProof (oblG_assigned_discharged_false with "[$Gl $Gu]") as "%". done. }
    iPoseProof (osat_lookup_owner with "[$S $Ge $Go1]") as "%Ht'". destruct Ht' as (a'& Ht').
    rewrite LUO1l in Ht'. injection Ht' as <- <-.
    iMod (oforest_discharge_obl _ _ p K k t with "[$T $F $Kp $Kk $Oo1]") as "(T& F& Kp& Go& Go2)".
    { done. }
    { by rewrite /obl_owner_of LUO1l. }
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
    iCombine "Go Go'" as "Go".
    iMod (osat_discharge with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
    assert (LUW : ∃ b', W1 !! k = Some (witness_assigned b')).
    { specialize (GWI k). rewrite LUO1l in GWI. inversion GWI as [? w Hm|]; subst.
      destruct w; [eauto|done]. }
    destruct LUW as (b'& LUW1).
    iPoseProof (owit_discharge with "[$W $Gu]") as "W"; first done.
    iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
    { iRight. eauto. }
    assert (Gstep' : obl_step (obl_assigned a t) obl_discharged) by (by econstructor 2).
    iMod (model_history_interp_step _ _ n n _ (<[k:=obl_discharged]> Ω1) with "HI") as "HI".
    { done. }
    { apply obls_lef_obls_le. by eapply obls_lef_insert_step. }
    iModIntro. iExists (<[k:=obl_discharged]> Ω1). iSplitR.
    { iPureIntro. by eapply obls_lef_insert_step. }
    iIntros (W2 [WStep GWI2]).
    pose proof (wits_lef_discharge_wits_mon _ _ _ k _ _ GWI LUO1l WStep GWI2) as WMon.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    rewrite /model_interp. iFrame "HI S T F W". iSplitL "A".
    { iModIntro. rewrite dom_insert_L.
      replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)).
      { iFrame. eauto. }
      apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
    iIntros "!> !>". iSplitL "Kx Kp".
    { iApply parP_kids_frag. iFrame. }
    iApply oblP_discharged_unfold. iFrame "Ge Gu".
  Qed.

  (** The children predicates of the initial threads (for adequacy). *)
  Lemma thP_kids_alloc_threads Ω π TP :
    π ## TP →
    othread TP ∗ oforest Ω TP
    ⊢ |==> othread (TP ∪ π) ∗ oforest Ω (TP ∪ π) ∗ [∗ set] i ∈ π, parP_kids (PThread i) ∅.
  Proof.
    iIntros (Disj) "[O F]".
    iMod (othread_alloc_threads π with "O") as "[$ Efs]"; first done.
    iAssert (([∗ set] i ∈ π, othreadG_elem i ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅) ∗
             ([∗ set] i ∈ π, othreadG_elem i ∗ othreadG_exec i (1/2)))%I
      with "[Efs]" as "[TGs Efs]".
    { iApply big_sepS_sep. iApply (big_sepS_impl with "Efs").
      iIntros "!> %% (#E& Ob& [X1 X2])". iFrame "E Ob X1 X2". }
    iMod (oforest_alloc_threads _ π with "[$F $TGs]") as "[$ Ks]"; first done.
    iModIntro. iPoseProof (big_sepS_sep with "[$Efs $Ks]") as "Efs".
    iApply (big_sepS_impl with "Efs"). iIntros "!> %j _ [E K]".
    iApply parP_kids_frag. iFrame.
  Qed.

  (** ** Invariants of obligations *)
  Lemma oblP_variant_unfold k P R :
    oblP_variant k P R ⊣⊢ ((oblP_assigned k (1/2)%Qp ∗ P) ∨ (oblP_discharged k ∗ R))%I.
  Proof. by unfold_opreds. Qed.

  Lemma oblP_inv_alloc_assigned E N k P R :
    oblP_assigned k (1/2) -∗ ▷ P ={E}=∗ oblP_inv N k P R.
  Proof.
    unfold_opreds. iIntros "(#Ge& Ga) HP". iFrame "Ge".
    iApply (oblG_inv_alloc_assigned_false with "[$Ga $HP]").
  Qed.

  Lemma oblP_inv_alloc_discharged E N k P R :
    oblP_discharged k -∗ ▷ R ={E}=∗ oblP_inv N k P R.
  Proof.
    unfold_opreds. iIntros "(#Ge& #Gu) HR". iFrame "Ge".
    iApply (oblG_inv_alloc_discharged with "[$Gu $HR]").
  Qed.

  Lemma oblP_inv_acc_cases E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ oblP_variant k P R) ∗ (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". unfold_opreds. iDestruct "I" as "(#Ge& #I)".
    iMod (oblG_inv_acc with "I") as "[V ACC]"; first done.
    iModIntro. iSplitL "V".
    - iNext. iDestruct "V" as "[[A HP] | [[_ []] | [D HR]]]".
      + iLeft. iFrame "Ge A HP".
      + iRight. iFrame "Ge D HR".
    - iIntros "V". iApply "ACC". iNext.
      iDestruct "V" as "[[(_& A) HP] | [(_& D) HR]]".
      + iLeft. iFrame.
      + iRight. iRight. iFrame.
  Qed.

  Lemma oblP_inv_acc E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))) ∗
    (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (H) "I". iMod (oblP_inv_acc_cases with "I") as "[H $]"; first done.
    iModIntro. iNext. by iApply oblP_variant_unfold.
  Qed.

  Lemma oblP_inv_acc_assigned E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗ ∀ q,
    oblP_assigned k q -∗
    (▷ (oblP_assigned k q ∗ oblP_assigned k (1/2) ∗ P)) ∗
    (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". iMod (oblP_inv_acc with "I") as "[V ACC]"; first done.
    iIntros "!> %q A". iFrame "ACC". iNext. iDestruct "V" as "[[A' HP] | [D _]]".
    - iFrame.
    - iDestruct (oblP_assigned_discharged_false with "A D") as %[].
  Qed.

  Lemma oblP_inv_acc_discharged E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    oblP_discharged k -∗ (▷ R) ∗ (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". iMod (oblP_inv_acc with "I") as "[V ACC]"; first done.
    iIntros "!> #D". iFrame "ACC". iNext. iDestruct "V" as "[[A _] | [_ $]]".
    iDestruct (oblP_assigned_discharged_false with "A D") as %[].
  Qed.

  Lemma oblP_inv_acc_discharged_persistent E N k P R :
    Persistent R →
    ↑N ⊆ E →
    oblP_inv N k P R -∗ oblP_discharged k ={E}[E ∖ ↑N]▷=∗ R.
  Proof.
    iIntros (PR HE) "#I #D". iMod (oblP_inv_acc_discharged with "I D") as "[H ACC]"; first done.
    iModIntro. iNext. iPoseProof "H" as "#H". iFrame "H". iApply "ACC".
    rewrite oblP_variant_unfold. iRight. eauto.
  Qed.

End mupd_rules.
