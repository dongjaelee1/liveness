(** * An obligation-forest rule interface for Lantana

    The class [oblf.obl_forest_interface] gives the signatures of the obligation predicates
    and their core rules for a logic in which obligations form a forest. There are no
    carriers: a *parent* is either a thread or an obligation, and every live obligation is
    a child of exactly one parent.

    - [parP_kids p K]: the children of parent [p] are the obligations [K]. For a thread
      ([thP_kids i K]) this also says that the thread is running; for an obligation
      ([oblP_kids k K]) it exists exactly while [k] is live and in the forest.
    - [oblP_fuel k ℓ μ]: fuel of obligation [k] at layer [ℓ]. It is the only kind of fuel.
    - A step of thread [i] burns one unit of fuel of each child of [i] ([step_progress]).
      All other obligations below [i] burn a unit automatically: this is the job of the
      model, which keeps the fuel of every obligation above the fuel of its parent.
    - [obl_move]: an obligation changes its parent (thread or obligation, in any of the four
      combinations) by burning one unit of its own fuel, and its whole subtree moves with
      it. Below an obligation [q] the unit must be at a layer above a witness layer of [q]
      ([parP_below]); below a thread any layer works.
    - [obl_move_up]: a child of [k] moves up to the parent of [k] for free: it keeps its
      owner, and the fuel the model keeps for it already dominates its new parent.
    - [obl_new] creates a live obligation below a parent; below an obligation [q] its layer
      must be at least a witness layer of [q] ([parP_le]): unlike a move, a new obligation may
      sit at its parent's own layer.
    - [obl_discharge] removes a childless obligation from the forest; its children must have
      moved to another parent before.

    The rules are stated with the modalities of the program logic: the model update
    [|={E}=>m] (sfmupd.v) and the step modalities of [model_physical_updates.v]. The model
    behind the rules is the forest invariant of [oforest.v] (fifth conjunct of
    [model_interp]); the instance is [obl_forest_lantana] in [obl_forest_instance.v]. An
    obligation invariant [oblP_inv N k P R] holds [P] while [k] is live and [R] once it is
    discharged. Derived rules follow the class; [obl_forest_derived.v] re-derives the
    obligation-related lifting lemmas of [lWP] from the class. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.algebra Require Import ordinal_wfocm.
From lantana.algebra Require Export layer.
From lantana.program_logic Require Export sfmupd model_physical_updates.
Import uPred.

Module oblf.

(** * The class

    The model ([oforest.v]). The obligation model [Ω] and the witnesses [W] are those of
    Lantana; the forest is a parent map in a ghost invariant. The owner of an obligation in
    [Ω] is the thread at the root of its tree. Every obligation [d] whose parent is an
    obligation [c] has a fuel piece [π d] stored in the invariant with [π d > fuel c] (the
    model fuel of [c]), and [fuel c < fuel d]. Hence fuel strictly increases downwards and
    the parent map has no cycles.
    - Step of thread [i]: the unit burnt for each child of [i] makes its fuel decrease; every
      other obligation [d] owned by [i] splits its piece into [fuel c] and a unit, which [d]
      burns. After the step [fuel' c < fuel c], so [fuel c] is the new piece of [d]. Every
      obligation owned by [i] makes progress.
    - [obl_move] of [k] to [q]: [fuel q] is bounded by the witness layer of [q], so the
      [▽]-part of the unit (at a higher layer) dominates it and becomes the new [π k]. If [q]
      has the owner of [k], nothing else changes. Otherwise the other part of the unit makes
      the fuel of [k] decrease, which pays the owner change of [k], and by the same cascade as
      in a step the whole subtree of [k] changes owner in the same round.
    - [obl_discharge]: [k] has no children; its piece [π k] is dropped. *)
Class obl_forest_interface `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} `{!TemporalInterp Λ Σ} := {
  (** ** Predicates *)
  (** The children of parent [p] are [K]; for a thread, the thread is also running. *)
  parP_kids : parent → oids → iProp Σ;
  (** Thread [i] has terminated. *)
  thP_done : positive → iProp Σ;
  (** Obligation [k] is live; [q] is a fraction. *)
  oblP_assigned : oid → Qp → iProp Σ;
  (** Obligation [k] is discharged. *)
  oblP_discharged : oid → iProp Σ;
  (** Fuel [μ] of obligation [k] at layer [ℓ]. *)
  oblP_fuel : oid → ord.t → measure → iProp Σ;
  (** Invariant over the status of [k]: [P] while live, [R] once discharged. *)
  oblP_inv : namespace → oid → iProp Σ → iProp Σ → iProp Σ;
  (** Witness of [k] at layer [ℓ]. *)
  witP_layer : oid → ord.t → iProp Σ;
  (** Witness credits of [k]. *)
  witP_cred : oid → obl_fuel → iProp Σ;
  (** Witness [k] at layer [ℓ] with remaining budget [α], carrying the fuels [F]. *)
  wit_fuels : oid → ord.t → obl_fuel → gmap oid (ord.t * measure) → iProp Σ;

  (** ** Structural properties *)
  #[global] parP_kids_timeless :: ∀ p K, Timeless (parP_kids p K);
  #[global] thP_done_timeless :: ∀ i, Timeless (thP_done i);
  #[global] thP_done_persistent :: ∀ i, Persistent (thP_done i);
  #[global] oblP_assigned_timeless :: ∀ k q, Timeless (oblP_assigned k q);
  #[global] oblP_assigned_fractional :: ∀ k, Fractional (oblP_assigned k);
  #[global] oblP_discharged_timeless :: ∀ k, Timeless (oblP_discharged k);
  #[global] oblP_discharged_persistent :: ∀ k, Persistent (oblP_discharged k);
  #[global] oblP_fuel_timeless :: ∀ k ℓ μ, Timeless (oblP_fuel k ℓ μ);
  #[global] oblP_inv_persistent :: ∀ N k P R, Persistent (oblP_inv N k P R);
  #[global] oblP_inv_contractive_1 :: ∀ N k R, Contractive (λ P, oblP_inv N k P R);
  #[global] oblP_inv_contractive_2 :: ∀ N k P, Contractive (λ R, oblP_inv N k P R);
  #[global] witP_layer_timeless :: ∀ k ℓ, Timeless (witP_layer k ℓ);
  #[global] witP_layer_persistent :: ∀ k ℓ, Persistent (witP_layer k ℓ);
  #[global] witP_cred_timeless :: ∀ k a, Timeless (witP_cred k a);
  #[global] wit_fuels_timeless :: ∀ k ℓ α F, Timeless (wit_fuels k ℓ α F);
  #[global] wit_fuels_empty_persistent :: ∀ k ℓ α, Persistent (wit_fuels k ℓ α ∅);

  (** ** Logical rules *)
  oblP_assigned_discharged_false k q :
    oblP_assigned k q -∗ oblP_discharged k -∗ False;
  (** Only live obligations have a children predicate (a discharged obligation has no
      children) ... *)
  oblP_kids_discharged_false E k K :
    parP_kids (PObl k) K -∗ oblP_discharged k -∗ |={E}=>m False;
  (** ... and only live obligations are children (a discharged obligation is not in the
      forest). Both facts are read off the forest invariant, hence the ghost update. *)
  parP_kids_discharged E k p K :
    parP_kids p K -∗ oblP_discharged k -∗ |={E}=>m ⌜ k ∉ K ⌝ ∗ parP_kids p K;

  oblP_fuel_proper k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 == ℓ2)%ordi →
    (measure_rep (ℓ1, 1) μ1 == measure_rep (ℓ2, 1) μ2)%ord →
    oblP_fuel k ℓ1 μ1 ⊣⊢ oblP_fuel k ℓ2 μ2;
  oblP_fuel_mon_gen k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep (ℓ1, 1) μ1 <= measure_rep (ℓ2, 1) μ2)%ord →
    oblP_fuel k ℓ2 μ2 ==∗ oblP_fuel k ℓ1 μ1;
  oblP_fuel_add k ℓ μ1 μ2 :
    oblP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2;
  oblP_fuel_extend k ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    oblP_fuel k ℓ2 1 ==∗ oblP_fuel k ℓ1 μ;

  witP_cred_proper k a0 a1 :
    (a0 == a1)%ord → witP_cred k a0 ⊣⊢ witP_cred k a1;
  witP_cred_mon k a0 a1 :
    (a0 <= a1)%ord → witP_cred k a1 ==∗ witP_cred k a0;
  witP_cred_split k a0 a1 :
    witP_cred k (a0 ⊕ a1)%ord ⊣⊢ witP_cred k a0 ∗ witP_cred k a1;

  (** ** Invariants over obligations *)
  oblP_inv_alloc_assigned E N k P R :
    oblP_assigned k (1/2) -∗ ▷ P ={E}=∗ oblP_inv N k P R;
  oblP_inv_alloc_discharged E N k P R :
    oblP_discharged k -∗ ▷ R ={E}=∗ oblP_inv N k P R;
  oblP_inv_acc E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))) ∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R)) ={E ∖ ↑N,E}=∗ True);

  (** ** Witness induction *)
  wit_fuels_init k ℓ :
    witP_layer k ℓ -∗ ∃ α, wit_fuels k ℓ α ∅;
  wit_fuels_witP_layer k ℓ α F :
    wit_fuels k ℓ α F ==∗ witP_layer k ℓ;
  (** Fuel above the layer of the witness can be stored in the induction ... *)
  wit_fuels_add k ℓ1 α F f ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    wit_fuels k ℓ1 α F -∗ oblP_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F);
  (** ... and comes back for each witness credit. *)
  wit_fuels_decr k ℓ α F :
    wit_fuels k ℓ α F -∗ witP_cred k Ord.one ==∗
    ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m);

  (** ** Model updates that keep every obligation live *)
  thread_terminate E i :
    parP_kids (PThread i) ∅ -∗ |={E}=>m thP_done i;
  (** A new live obligation [k] below [p], without children, at layer [ℓ]. *)
  obl_new E p K ℓ μ :
    parent_le witP_layer p ℓ -∗
    parP_kids p K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ parP_kids (PObl k) ∅ ∗
                 oblP_assigned k 1 ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ;
  (** A discharged obligation (outside the forest). *)
  obl_new_discharged E ℓ :
    ⊢ |={E}=>m ∃ k, oblP_discharged k ∗ witP_layer k ℓ;
  (** [k] moves, with its whole subtree, from parent [p1] to parent [p2], burning one unit
      of its fuel at a layer [ℓ] large enough for [p2]. *)
  obl_move E p1 p2 K1 K2 k ℓ :
    k ∈ K1 →
    parent_below witP_layer p2 ℓ -∗
    parP_kids p1 K1 -∗ parP_kids p2 K2 -∗ oblP_fuel k ℓ 1 -∗
    |={E}=>m ⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ parP_kids p2 ({[k]} ∪ K2);
  (** [x], a child of [k], moves with its subtree up to the parent [p] of [k], for free. *)
  obl_move_up E p K k Kk x :
    k ∈ K → x ∈ Kk →
    parP_kids p K -∗ parP_kids (PObl k) Kk -∗
    |={E}=>m ⌜ x ∉ K ⌝ ∗ parP_kids p ({[x]} ∪ K) ∗ parP_kids (PObl k) (Kk ∖ {[x]});
  obl_check_witness E r ℓ :
    witP_layer r ℓ -∗ |={E}=>m (witP_cred r Ord.O ∨ oblP_discharged r);

  (** ** Discharge *)
  (** A childless obligation [k] below [p] is discharged and leaves the forest. *)
  obl_discharge E p K k :
    k ∈ K →
    parP_kids p K -∗ parP_kids (PObl k) ∅ -∗ oblP_assigned k 1 -∗
    |={E}=>m parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k;

  (** ** Physical steps *)
  (** A step of thread [i] burns one unit of fuel of each child of [i] and gives one credit
      for each live witness in [R]. *)
  step_progress n Θ i K R P :
    parP_kids (PThread i) K -∗
    ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ 1) -∗
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    (parP_kids (PThread i) K -∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)
     ={∅}=∗ P) -∗
    @={n,Θ,i}=↓ P;
  (** A step that forks the threads [π] gives each of them an empty set of children. *)
  step_fork n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (([∗ set] j ∈ π, parP_kids (PThread j) ∅) ={∅}=∗ P) -∗
    @={n1,n2,Θ1,Θ2}=> P;
}.

(** * Derived notions *)
Notation thP_kids i K := (parP_kids (PThread i) K).
Notation oblP_kids k K := (parP_kids (PObl k) K).
Notation parP_below p ℓ := (parent_below witP_layer p ℓ).
Notation parP_le p ℓ := (parent_le witP_layer p ℓ).
(** Burning one unit of fuel of each obligation of a set. *)
Notation oblP_fuels K n := ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ n)%I.
(** One witness credit: a step gives one to each live witness ([step_progress]), and each
    round of the witness induction consumes one ([wit_fuels_decr]). *)
Notation witP_cred1 r := (witP_cred r Ord.one).
(** No witness credit, as given by checking a witness ([obl_check_witness]). *)
Notation witP_cred0 r := (witP_cred r Ord.O).

(** The two states of an obligation invariant. *)
Definition oblP_variant `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} `{!TemporalInterp Λ Σ}
  `{!@obl_forest_interface SI Λ Σ _ _ _ _} k (P R : iProp Σ) : iProp Σ :=
  ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))%I.

(** * Derived rules: invariants, witnesses, model updates, steps *)
Section derived.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!TemporalInterp Λ Σ}.
  Context `{!@obl_forest_interface SI Λ Σ _ _ _ _}.

  (* BEGIN derived *)
  (** ** Obligation predicates and invariants *)
  Global Instance oblP_assigned_as_fractional k q :
    AsFractional (oblP_assigned k q) (oblP_assigned k) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance oblP_inv_ne_1 N k R : NonExpansive (λ P, oblP_inv N k P R).
  Proof. apply _. Qed.
  Global Instance oblP_inv_ne_2 N k P : NonExpansive (λ R, oblP_inv N k P R).
  Proof. apply _. Qed.
  Global Instance oblP_inv_proper_1 N k R : Proper (equiv ==> equiv) (λ P, oblP_inv N k P R).
  Proof. apply ne_proper, _. Qed.
  Global Instance oblP_inv_proper_2 N k P : Proper (equiv ==> equiv) (λ R, oblP_inv N k P R).
  Proof. apply ne_proper, _. Qed.

  Global Instance oblP_variant_timeless k P R :
    Timeless P → Timeless R → Timeless (oblP_variant k P R).
  Proof. rewrite /oblP_variant. apply _. Qed.

  Lemma oblP_variant_unfold k P R :
    oblP_variant k P R ⊣⊢ ((oblP_assigned k (1/2)%Qp ∗ P) ∨ (oblP_discharged k ∗ R))%I.
  Proof. done. Qed.

  Lemma oblP_inv_acc_cases E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ oblP_variant k P R) ∗ (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof. apply oblP_inv_acc. Qed.

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

  (** ** Witness induction (as in [obli]) *)
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
    □ ((witP_cred1 k ==∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m) ∗ P) ==∗ P) ∗
    wit_fuels k ℓ α F
    ⊢ |==> P.
  Proof.
    iIntros "[#H WF]". iInduction α as [α IH] using (well_founded_ind WFOCM.lt_wf).
    iApply "H". iIntros "Wc". iMod (wit_fuels_decr with "WF Wc") as "(%&%& WF& Fs)".
    iFrame "Fs". iApply ("IH" with "[//] WF").
  Qed.

  Lemma wit_layer_ind k ℓ G l m (P : iProp Σ) :
    (ℓ < l)%ordi →
    □ ((witP_cred1 k ==∗ ([∗ set] g ∈ G, oblP_fuel g l m) ∗ P) ==∗ P) ∗
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

  (** ** Parents *)
  Global Instance parent_below_persistent p ℓ : Persistent (parP_below p ℓ).
  Proof. destruct p; rewrite /parent_below; apply _. Qed.

  Lemma parP_below_thread i ℓ : ⊢ parP_below (PThread i) ℓ.
  Proof. done. Qed.

  Lemma parP_below_obl q ℓq ℓ :
    (ℓq < ℓ)%ordi → witP_layer q ℓq -∗ parP_below (PObl q) ℓ.
  Proof. iIntros (Hl) "W". iExists ℓq. by iFrame. Qed.

  Global Instance parent_le_persistent p ℓ : Persistent (parP_le p ℓ).
  Proof. destruct p; rewrite /parent_le; apply _. Qed.

  Lemma parP_le_thread i ℓ : ⊢ parP_le (PThread i) ℓ.
  Proof. done. Qed.

  Lemma parP_le_obl q ℓq ℓ :
    (ℓq <= ℓ)%ordi → witP_layer q ℓq -∗ parP_le (PObl q) ℓ.
  Proof. iIntros (Hl) "W". iExists ℓq. by iFrame. Qed.

  Lemma parP_below_le p ℓ : parP_below p ℓ -∗ parP_le p ℓ.
  Proof.
    destruct p as [i|q]; first by iIntros. iIntros "(%ℓq& %Hl& W)". iExists ℓq. iFrame.
    iPureIntro. by apply ord.lt_le.
  Qed.

  (** ** Ghost updates in their usual shapes *)
  Lemma obl_new_thread E i K ℓ μ :
    thP_kids i K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ thP_kids i ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_assigned k 1 ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "T". iPoseProof (parP_le_thread i ℓ) as "B". iApply (obl_new with "B T").
  Qed.

  Lemma obl_new_obl E q K ℓq ℓ μ :
    (ℓq <= ℓ)%ordi →
    witP_layer q ℓq -∗ oblP_kids q K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ oblP_kids q ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_assigned k 1 ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros (Hl) "W C". iPoseProof (parP_le_obl q ℓq ℓ Hl with "W") as "B".
    iApply (obl_new with "B C").
  Qed.

  Lemma obl_alloc_assigned E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_assigned k (1/2)%Qp ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 (∀ E N (P R : iProp Σ), ▷ P ={E}=∗ oblP_inv N k P R).
  Proof.
    iIntros "B C". iMod (obl_new with "B C") as (k) "(%Hk& C& Ck& [A1 A2]& F& W)".
    iModIntro. iExists k. iFrame "C Ck A1 F W". iSplit; first done.
    iIntros (E' N P R) "H". iApply (oblP_inv_alloc_assigned with "A2 H").
  Qed.

  Lemma obl_move_thread E p1 j K1 K2 k ℓ :
    k ∈ K1 →
    parP_kids p1 K1 -∗ thP_kids j K2 -∗ oblP_fuel k ℓ 1 -∗
    |={E}=>m ⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ thP_kids j ({[k]} ∪ K2).
  Proof.
    iIntros (Hk) "P1 P2 F". iPoseProof (parP_below_thread j ℓ) as "B".
    iApply (obl_move with "B P1 P2 F"). done.
  Qed.

  Lemma obl_move_obl E p1 q K1 K2 k ℓq ℓ :
    k ∈ K1 →
    (ℓq < ℓ)%ordi →
    witP_layer q ℓq -∗ parP_kids p1 K1 -∗ oblP_kids q K2 -∗ oblP_fuel k ℓ 1 -∗
    |={E}=>m ⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ oblP_kids q ({[k]} ∪ K2).
  Proof.
    iIntros (Hk Hl) "W P1 P2 F". iPoseProof (parP_below_obl q ℓq ℓ Hl with "W") as "B".
    iApply (obl_move with "B P1 P2 F"). done.
  Qed.

  (** Moving a set [X] of children of [p1] to [p2], one unit each. *)
  Lemma obl_move_set E p1 p2 K1 K2 X ℓ :
    X ⊆ K1 →
    parP_below p2 ℓ -∗ parP_kids p1 K1 -∗ parP_kids p2 K2 -∗ ([∗ set] k ∈ X, oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ parP_kids p2 (X ∪ K2).
  Proof.
    induction X as [|x X Hx IH] using set_ind_L; iIntros (HX) "#B P1 P2 Fs".
    { rewrite difference_empty_L left_id_L. iModIntro. iFrame. iPureIntro. set_solver. }
    iPoseProof (big_sepS_insert with "Fs") as "[Fx Fs]"; first done.
    iMod (IH with "B P1 P2 Fs") as "(%Hdis& P1& P2)"; first set_solver.
    iMod (obl_move _ _ _ _ _ x with "B P1 P2 Fx") as "(%Hx2& P1& P2)"; first set_solver.
    replace (K1 ∖ X ∖ {[x]}) with (K1 ∖ ({[x]} ∪ X)) by set_solver.
    replace ({[x]} ∪ (X ∪ K2)) with ({[x]} ∪ X ∪ K2) by set_solver.
    iModIntro. iFrame. iPureIntro. set_solver.
  Qed.

  (** Moving a set [X] of children of [p1] to [p2], one unit each, each at its own layer. *)
  Lemma obl_move_set_gen E p1 p2 K1 K2 X :
    X ⊆ K1 →
    parP_kids p1 K1 -∗ parP_kids p2 K2 -∗
    ([∗ set] k ∈ X, ∃ ℓ, parP_below p2 ℓ ∗ oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ parP_kids p2 (X ∪ K2).
  Proof.
    induction X as [|x X Hx IH] using set_ind_L; iIntros (HX) "P1 P2 Fs".
    { rewrite difference_empty_L left_id_L. iModIntro. iFrame. iPureIntro. set_solver. }
    iPoseProof (big_sepS_insert with "Fs") as "[(%ℓ& B& Fx) Fs]"; first done.
    iMod (IH with "P1 P2 Fs") as "(%Hdis& P1& P2)"; first set_solver.
    iMod (obl_move _ _ _ _ _ x with "B P1 P2 Fx") as "(%Hx2& P1& P2)"; first set_solver.
    replace (K1 ∖ X ∖ {[x]}) with (K1 ∖ ({[x]} ∪ X)) by set_solver.
    replace ({[x]} ∪ (X ∪ K2)) with ({[x]} ∪ X ∪ K2) by set_solver.
    iModIntro. iFrame. iPureIntro. set_solver.
  Qed.

  (** Moving a set [X] of children of [p1] below the thread [j]: one unit each, at any
      layer. *)
  Lemma obl_move_thread_set E p1 j K1 K2 X :
    X ⊆ K1 →
    parP_kids p1 K1 -∗ thP_kids j K2 -∗ ([∗ set] k ∈ X, ∃ ℓ, oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ thP_kids j (X ∪ K2).
  Proof.
    iIntros (HX) "P1 P2 Fs". iApply (obl_move_set_gen with "P1 P2"); first done.
    iApply (big_sepS_impl with "Fs"). iIntros "!> %k _ [%ℓ F]". iExists ℓ. iFrame "F".
    iApply parP_below_thread.
  Qed.

  (** Moving a set [X] of children of [p1] below the obligation [q]: one unit each, each at
      a layer above the witness layer [ℓq] of [q]. *)
  Lemma obl_move_obl_set E p1 q K1 K2 X ℓq :
    X ⊆ K1 →
    witP_layer q ℓq -∗ parP_kids p1 K1 -∗ oblP_kids q K2 -∗
    ([∗ set] k ∈ X, ∃ ℓ, ⌜ (ℓq < ℓ)%ordi ⌝ ∗ oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ oblP_kids q (X ∪ K2).
  Proof.
    iIntros (HX) "#W P1 P2 Fs". iApply (obl_move_set_gen with "P1 P2"); first done.
    iApply (big_sepS_impl with "Fs"). iIntros "!> %k _ (%ℓ& %Hl& F)". iExists ℓ. iFrame "F".
    by iApply (parP_below_obl q ℓq ℓ Hl).
  Qed.

  (** Moving a set [X] of children of [k] up to the parent [p] of [k], for free. *)
  Lemma obl_move_up_set E p K k Kk X :
    k ∈ K → X ⊆ Kk →
    parP_kids p K -∗ oblP_kids k Kk -∗
    |={E}=>m ⌜ X ## K ⌝ ∗ parP_kids p (X ∪ K) ∗ oblP_kids k (Kk ∖ X).
  Proof.
    induction X as [|x X Hx IH] using set_ind_L; iIntros (Hk HX) "P Ck".
    { rewrite difference_empty_L left_id_L. iModIntro. iFrame. iPureIntro. set_solver. }
    iMod (IH with "P Ck") as "(%Hdis& P& Ck)"; [done|set_solver|].
    iMod (obl_move_up _ _ _ k _ x with "P Ck") as "(%Hx2& P& Ck)"; [set_solver|set_solver|].
    replace (Kk ∖ X ∖ {[x]}) with (Kk ∖ ({[x]} ∪ X)) by set_solver.
    replace ({[x]} ∪ (X ∪ K)) with ({[x]} ∪ X ∪ K) by set_solver.
    iModIntro. iFrame. iPureIntro. set_solver.
  Qed.

  Lemma obl_alloc_discharged E ℓ :
    ⊢ |={E}=>m ∃ k, oblP_discharged k ∗ witP_layer k ℓ ∗
                   (∀ E N (P R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P R).
  Proof.
    iMod (obl_new_discharged E ℓ) as (k) "(#D& W)". iModIntro. iExists k. iFrame "D W".
    iIntros (E' N P R) "H". iApply (oblP_inv_alloc_discharged with "D H").
  Qed.

  Lemma obl_check_witnesses E (R : oids) :
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    |={E}=>m ([∗ set] r ∈ R, (witP_cred0 r) ∨ oblP_discharged r).
  Proof.
    iIntros "Rs". iApply big_sepS_sfmupd. iApply (big_sepS_impl with "Rs").
    iIntros "!> %r _ [%ℓ W]". iApply (obl_check_witness with "W").
  Qed.

  (** ** Model updates in their usual shapes *)
  (** Discharging [k] after moving its children up to its parent [p] (for free). *)
  Lemma obl_discharge_lift_kids E p K k Kk :
    k ∈ K →
    parP_kids p K -∗ oblP_kids k Kk -∗ oblP_assigned k 1 -∗
    |={E}=>m parP_kids p (Kk ∪ (K ∖ {[k]})) ∗ oblP_discharged k.
  Proof.
    iIntros (Hk) "P Ck A".
    iMod (obl_move_up_set _ p K k Kk Kk with "P Ck") as "(%Hdis& P& Ck)"; [done|done|].
    rewrite difference_diag_L.
    iMod (obl_discharge with "P Ck A") as "[P D]"; first set_solver.
    replace ((Kk ∪ K) ∖ {[k]}) with (Kk ∪ (K ∖ {[k]})) by set_solver.
    by iFrame.
  Qed.

  (** Discharging [k] with the invariant [oblP_inv N k P R]: [P] is taken out, and once [R] is
      established [k], a childless child of [p], is discharged. *)
  Lemma obl_discharge_inv E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R -∗
    |={E,E ∖ ↑N}=> ∀ q, oblP_assigned k q -∗
    ▷ (oblP_assigned k q ∗ oblP_assigned k (1/2) ∗ P) ∗
    (∀ p K, ⌜ k ∈ K ⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ oblP_assigned k 1 -∗ ▷ R -∗
     ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k).
  Proof.
    iIntros (HN) "#I". iMod (oblP_inv_acc_assigned with "I") as "H"; first done.
    iIntros "!> %q A". iDestruct ("H" with "A") as "[$ ACC]".
    iIntros (p K Hk) "Kp Kk A HR %E'". iMod (obl_discharge with "Kp Kk A") as "[$ #D]"; first done.
    iModIntro. iMod ("ACC" with "[HR]") as "_".
    { iNext. rewrite oblP_variant_unfold. iRight. iFrame "D HR". }
    iModIntro. iFrame "D".
  Qed.

  (** ** Physical steps in their usual shapes (cf. [model_physical_updates.v]) *)
  Lemma mprog_step n Θ i P :
    (|={∅}=> ∃ K, thP_kids i K ∗ oblP_fuels K 1 ∗
                   ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                        ((thP_kids i K ∗ ([∗ set] r ∈ R, witP_cred1 r ∨ oblP_discharged r))
                         ={∅}=∗ P))
    ⊢ mprog n Θ i P.
  Proof.
    iIntros "H". iApply fupd_mprog. iMod "H" as (K) "(T& F& %R& W& H)". iModIntro.
    iApply (step_progress with "T F W"). iIntros "T C". iApply ("H" with "[$T $C]").
  Qed.

  Lemma mphys_step n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (|={∅}=> ([∗ set] j ∈ π, thP_kids j ∅) ={∅}=∗ P)
    ⊢ mphys n1 n2 Θ1 Θ2 P.
  Proof.
    iIntros (???) "H". iApply fupd_mphys. iMod "H". iModIntro. by iApply (step_fork with "H").
  Qed.
  (* END derived *)

End derived.

(** * Derived rules: fuel and credit algebra *)
Section fuel.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!TemporalInterp Λ Σ}.
  Context `{!@obl_forest_interface SI Λ Σ _ _ _ _}.

  (* BEGIN fuel *)
  Local Open Scope ord.

  (** ** oblP_fuel rules *)
  Lemma oblP_fuel_layer_eq k ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    oblP_fuel k ℓ1 μ ⊣⊢ oblP_fuel k ℓ2 μ.
  Proof.
    intros. apply oblP_fuel_proper; first done.
    apply measure_rep_layer_eq. split; auto.
  Qed.
  Lemma oblP_fuel_layer_eq_list K ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ)%I.
  Proof. intros. apply big_opL_proper. intros. by apply oblP_fuel_layer_eq. Qed.
  Lemma oblP_fuel_layer_eq_set K ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ)%I.
  Proof. intros. apply big_opS_proper. intros. by apply oblP_fuel_layer_eq. Qed.

  Lemma oblP_fuel_eq k ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    oblP_fuel k ℓ μ1 ⊣⊢ oblP_fuel k ℓ μ2.
  Proof. intros. apply oblP_fuel_proper; [reflexivity|done]. Qed.
  Lemma oblP_fuel_eq_list K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opL_proper. intros. by apply oblP_fuel_eq. Qed.
  Lemma oblP_fuel_eq_set K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) (μ1)%M == measure_rep (ℓ, 1) (μ2)%M) →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opS_proper. intros. by apply oblP_fuel_eq. Qed.

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
    intros. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add. done.
  Qed.
  Lemma oblP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
    ((measure_rep (ℓ, 1) (μ1)%M ⊕ measure_rep (ℓ, 1) (μ2)%M) <= measure_rep (ℓ, 1) (μ3)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!> % % %". iApply oblP_fuel_mon_split; auto.
  Qed.
  Lemma oblP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
    ((measure_rep (ℓ, 1) (μ1)%M ⊕ measure_rep (ℓ, 1) (μ2)%M) <= measure_rep (ℓ, 1) (μ3)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
    iIntros "!> % %". iApply oblP_fuel_mon_split; auto.
  Qed.

  Lemma oblP_fuel_lt k ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    oblP_fuel k ℓ μ2 ⊢ |==> oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ (1)%M.
  Proof.
    intros. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add measure_rep_nat. rewrite Hessenberg.add_comm -ord_S_add.
    apply Ord.S_supremum; auto.
  Qed.
  Lemma oblP_fuel_lt_list K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_lt.
  Qed.
  Lemma oblP_fuel_lt_set K ℓ μ1 μ2 :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
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
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    oblP_fuel k ℓ (s × μ2)%M ⊢ |==> oblP_fuel k ℓ (s × μ1)%M ∗ oblP_fuel k ℓ s.
  Proof.
    intros LT. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add !measure_rep_mult.
    transitivity (measure_rep (ℓ, 1) s × Ord.S (measure_rep (ℓ, 1) μ1)).
    - rewrite Jacobsthal.mult_S Hessenberg.add_comm. done.
    - apply Jacobsthal.le_mult_r. by apply Ord.S_supremum.
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
    intros LT Pos. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_mult !measure_rep_expn -(Jacobsthal.expn_S Pos).
    apply Jacobsthal.le_expn_r. by apply Ord.S_supremum.
  Qed.
  Lemma oblP_fuel_expn_list K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    (Ord.O < measure_rep (ℓ, 1) s)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_expn; auto.
  Qed.
  Lemma oblP_fuel_expn_set K ℓ μ1 μ2 s :
    (measure_rep (ℓ, 1) μ1 < measure_rep (ℓ, 1) μ2)%ord →
    (Ord.O < measure_rep (ℓ, 1) s)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_expn; auto.
  Qed.

  Lemma oblP_fuel_extend_list K ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. iIntros "H". by iApply (oblP_fuel_extend with "H").
  Qed.
  Lemma oblP_fuel_extend_set K ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 (1)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. iIntros "H". by iApply (oblP_fuel_extend with "H").
  Qed.

  (** ** witP_cred rules *)
  Lemma witP_cred_eq k a0 a1 :
    (a0 == a1) → witP_cred k a1 ⊣⊢ witP_cred k a0.
  Proof. intros. symmetry. by apply witP_cred_proper. Qed.
  Lemma witP_cred_mon_split k a0 a1 a2 :
    ((a0 ⊕ a1) <= a2)%ord →
    witP_cred k a2 ==∗ witP_cred k a0 ∗ witP_cred k a1.
  Proof. intros. rewrite -witP_cred_split. iIntros "H". by iApply (witP_cred_mon with "H"). Qed.
  Lemma witP_cred_lt k a0 a1 :
    (a0 < a1) → witP_cred k a1 ==∗ witP_cred k a0 ∗ witP_cred1 k.
  Proof.
    intros. iIntros "H". iApply (witP_cred_mon_split with "H").
    transitivity (Ord.S a0); last by apply Ord.S_supremum.
    rewrite Hessenberg.add_comm (ord_S_add a0). reflexivity.
  Qed.

  (** Useful pattern for burning fuels when taking a step *)
  Lemma oblP_fuel_add_nat m1 m2 n k ℓ :
    (n = m1 + m2)%nat →
    oblP_fuel k ℓ n ⊣⊢ (oblP_fuel k ℓ m1 ∗ oblP_fuel k ℓ m2)%I.
  Proof.
    intros ->. rewrite -oblP_fuel_add. apply oblP_fuel_eq.
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
    iDestruct "H" as "(%& H)". iPoseProof (oblP_fuel_add_nat with "H") as "[H F]". 1: eauto.
    iFrame.
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
  (* END fuel *)

End fuel.

End oblf.
