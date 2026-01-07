(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Import mono_nat.
From transfinite.base_logic.lib Require Export gen_heap proph_map.
(* From transfinite.base_logic.lib Require Export gen_heap proph_map gen_inv_heap. *)
From liris.base_logic Require Export thread_map gen_inv_heap.
(* From liris.program_logic Require Export weakestpre. *)
From liris.program_logic Require Export atomic lifting.
From liris.program_logic Require Import ectx_lifting.
From liris.heap_lang Require Export class_instances.
From liris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.
From liris.algebra Require Import ordinal_wfocm.

Class heapGS `{SI : indexT} Σ := HeapGS {
  heapGS_gupdGS : gupdGS Σ;

  #[global] heapGS_gen_heapGS :: gen_heapGS loc (option val) Σ;
  #[global] heapGS_inv_heapGS :: inv_heapGS loc (option val) Σ;
  #[global] heapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
  #[global] heapGS_thread_mapGS :: thread_mapGS thread_id (option val) Σ;
}.

Global Program Instance heapGS_lirisGS `{SI : indexT} `{!heapGS Σ} : lirisGS heap_lang Σ := {
    liris_gupdGS := heapGS_gupdGS;
    state_interp σ Θ κs :=
      (thread_map_interp Θ σ.(thread_map) ∗
       gen_heap_interp σ.(heap) ∗
       proph_map_interp κs σ.(used_proph_id))%I;
    fork_post i v := (thread i false (Some v) 1)%I;
  }.

(** Since we use an [option val] instance of [gen_heap], we need to add a
[Some]. We also seal the definition to avoid confusion between the version from
[gen_heap], and our version with [Some]. That also helps for scopes and
coercions. *)
Local Definition pointsto_def `{SI : indexT} `{@heapGS SI Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {SI Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{SI : indexT} `{!heapGS Σ}.
  Definition inv_pointsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_pointsto_own l (Some v) (from_option I False).
  Definition inv_pointsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_pointsto l (from_option I False).
End definitions.

Global Instance: Params (@inv_pointsto_own) 5 := {}.
Global Instance: Params (@inv_pointsto) 4 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_pointsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

(** Wrappers for othread and thread tokens *)
Local Definition thread_exec_def `{SI : indexT} `{@heapGS SI Σ}
  (i : thread_id) q : iProp Σ :=
  (thread i true None q)%I.
  (* (othread_obls i Ψ q ∗ thread i true None q)%I. *)
Local Definition thread_exec_aux : seal (@thread_exec_def). Proof. by eexists. Qed.
Definition thread_exec := thread_exec_aux.(unseal).
Local Definition thread_exec_unseal :
  @thread_exec = @thread_exec_def := thread_exec_aux.(seal_eq).
Global Arguments thread_exec {SI Σ _}.

Local Definition thread_term_def `{SI : indexT} `{@heapGS SI Σ}
  (i : thread_id) (v : val) : iProp Σ :=
  (thread i false (Some v) 1)%I.
  (* (othread_term i ∗ thread i false (Some v) 1)%I. *)
Local Definition thread_term_aux : seal (@thread_term_def). Proof. by eexists. Qed.
Definition thread_term := thread_term_aux.(unseal).
Local Definition thread_term_unseal :
  @thread_term = @thread_term_def := thread_term_aux.(seal_eq).
Global Arguments thread_term {SI Σ _}.

Section lifting.
Context `{SI : indexT} `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : gmap thread_id expr.
Implicit Types σ : state.
Implicit Types l : loc.

Local Ltac unfold_defs :=
  try rewrite thread_term_unseal /thread_term_def;
  try rewrite thread_exec_unseal /thread_exec_def.

Global Instance thread_term_persistent i v : Persistent (thread_term i v).
Proof. rewrite thread_term_unseal /thread_term_def. apply _. Qed.
Global Instance thread_term_timeless i v : Timeless (thread_term i v).
Proof. rewrite thread_term_unseal /thread_term_def. apply _. Qed.
Global Instance thread_exec_timeless i q : Timeless (thread_exec i q).
Proof. rewrite thread_exec_unseal /thread_exec_def. apply _. Qed.

Lemma thread_term_agree i v1 v2 : thread_term i v1 -∗ thread_term i v2 -∗ ⌜v1 = v2⌝.
Proof.
  unfold_defs. iIntros "H1 H2". iPoseProof (thread_agree with "H1 H2") as "%". by inv H.
Qed.

Lemma thread_exec_op_1 i q1 q2 :
  thread_exec i q1 -∗ thread_exec i q2 -∗ thread_exec i (q1 + q2).
Proof.
  unfold_defs. iIntros "T1 T2".
  iCombine "T1 T2" as "T". iFrame.
Qed.
Lemma thread_exec_op_2 i q1 q2 :
  thread_exec i (q1 + q2) -∗ (thread_exec i q1 ∗ thread_exec i q2).
Proof.
  unfold_defs. iIntros "T".
  iDestruct "T" as "[T1 T2]"; iFrame.
Qed.

Global Instance thread_None_thread_cond i b q : PureExecCond thread_cond (thread i b None q) i.
Proof.
  iIntros (???) "Hc [T H]". iPoseProof (thread_map_thread_read with "T Hc") as "%". done.
Qed.

Lemma thread_exec_thread_cond_0 i q :
  ∀ σ Θ, thread_exec i q -∗ thread_map_interp Θ σ.(thread_map) -∗ ⌜ thread_cond i σ ⌝.
Proof.
  unfold_defs. iIntros (??) "Hc T". iPoseProof (thread_map_thread_read with "T Hc") as "%". done.
Qed.

Lemma thread_exec_thread_cond_1 i q :
  ∀ σ Θ κ, thread_exec i q -∗ state_interp σ Θ κ -∗ ⌜ thread_cond i σ ⌝.
Proof.
  iIntros (???) "Hc [T H]". iPoseProof (thread_exec_thread_cond_0 with "Hc T") as "%". done.
Qed.

Global Instance thread_exec_thread_cond i q : PureExecCond thread_cond (thread_exec i q) i.
Proof. intros ???. apply thread_exec_thread_cond_1. Qed.

Lemma iter_modal_mono_modal M1 M2 P n :
  (∀ A B, (A -∗ B) -∗ (M1 A -∗ M1 B)) →
  (∀ A, M1 A -∗ M2 A) →
  (Nat.iter n M1 P -∗ Nat.iter n M2 P).
Proof.
  intros. revert P. induction n; intros; simpl; eauto.
  iIntros "H". iApply H0. iApply (H with "[] H"). iApply IHn.
Qed.

(** "pure" steps that are reducible with the thread_exec predicate *)
Lemma lwp_pure_step n s i q E E' e1 e2 φ Φ :
  PureExec φ thread_cond n e1 e2 →
  φ →
  Nat.iter n
    (λ P,
       |={E,E'}=> thread_exec i q ∗
                 ∃ G, th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
                 ∃ R, ([∗ map] r↦v ∈ R, gl r v) ∗
                 (thread_exec i q -∗
                  th_obls i G 1 -∗
                  ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
                  ALC (|={E',E}=> P)))
    (£n n -∗ lWP e2 @ s; i; E {{ v, Φ v }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hp) "H". iApply (lwp_pure_step); eauto.
Qed.

Lemma lwp_fork s q i E E' e Φ :
  (|={E,E'}=> thread_exec i q ∗
             ∃ G, th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
             ∃ R, ([∗ map] r↦v ∈ R, gl r v) ∗
             (∀ j, thread_exec i q -∗
                   th_obls i G 1 -∗
                   ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
                   thread_exec j 1 -∗
                   th_obls j ∅ 1 -∗
                   ALC (|={E',E}=>
                   (|={E}=>g Φ (LitV LitUnit)) ∗
                   lWP e @ s; j; ⊤ {{ lift_term j thread_term }}))) -∗
  lWP Fork e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step.
  iIntros (Θ σ1 κ κs) "I". iMod "H" as "(Tx& %&$&$& %&$& H)".
  iPoseProof (thread_exec_thread_cond_1 with "Tx I") as "%Ci".
  iModIntro. iSplit; first eauto with base_step.
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iDestruct "I" as "[It I]". iMod (thread_map_new_thread with "It") as "[It Tj]"; first eapply H1.
  iIntros "!> Tb Wcs Efs". iMod ("H" $! j with "Tx Tb Wcs [Tj] [Efs]") as "H".
  { unfold_defs. eauto. }
  { rewrite dom_singleton_L big_sepS_singleton. iFrame. }
  iMod "H" as "(H& E)". rewrite dom_singleton_L. iFrame.
  rewrite big_sepM_singleton. iModIntro.
  iApply (lwp_mono with "E"). unfold_defs. rewrite /lift_term. iIntros (?) "($&$)".
Qed.

(* (* Wrong spec *) *)
(* Lemma lwp_fork_lat i e : *)
(*   ⊢ <<{ ∀∀ q, thread_exec i q }>> Fork e @ i; ∅ *)
(*     <<{ ∃∃ j, thread_exec i q ∗ thread_exec j 1 | RET (LitV LitUnit); lWP e @ j; ⊤ {{ thread_term j }} }>>. *)
(* Proof. *)
(*   iIntros (Φ) "AU". iApply lwp_fork_fupd. *)
(*   iMod "AU" as (Δ q) "[H↦ [_ Hclose]]". *)
(*   iModIntro. iFrame. *)
(* Qed. *)

(** Exit *)
Lemma lwp_exit s i E e v Φ :
  TCEq (to_val e) (Some v) →
  th_obls i ∅ 1 -∗
  thread_exec i 1 -∗
  (ALC (th_term i -∗ thread_term i v -∗ |={E}=>g Φ v)) -∗
  lWP Exit e @ s; i; E {{ Φ }}.
Proof.
  unfold_defs. iIntros (He) "Tb Tx H".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "I".
  iModIntro. iPoseProof (thread_None_thread_cond with "Tx I") as "%Ci".
  iSplit.
  { destruct e; inv He. eauto with base_step. }
  iExists ∅. iFrame "Tb". iSplitR; first done.
  iExists ∅. iSplitR; first done.
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  inv He. iDestruct "I" as "[It I]".
  iMod (thread_map_thread_update _ _ (Some v) with "[$]") as "[It T]".
  iMod (thread_true_to_false _ _ _ 1 with "T") as "T".
  iIntros "!> Tb _". iMod "H".
  iModIntro. iSplitR; first done. iFrame "It I".
  iMod (gl_terminate with "Tb") as "#Tt". iApply ("H" with "Tt T").
Qed.

(** Can be derived from above *)
Lemma lwp_exit_fupd s i E E' e v Φ :
  TCEq (to_val e) (Some v) →
  (|={E,E'}=>
     th_obls i ∅ 1 ∗
     thread_exec i 1 ∗
     (ALC (th_term i -∗ thread_term i v -∗ |={E'}=>g |={E',E}=> Φ v))) -∗
  lWP Exit e @ s; i; E {{ Φ }}.
Proof.
  iIntros (He) "H". iMod "H" as "(Tb& Te& H)". iApply (lwp_exit with "Tb Te"). iFrame.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val] (and sealing). *)

Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_as_fractional l q v :
  AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
Proof. rewrite pointsto_unseal. apply _. Qed.

Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 : 
  CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  rewrite pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? [=->]]. eauto.
Qed.

Lemma pointsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  rewrite pointsto_unseal.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$" gives %[_ [= ->]].
Qed.

Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
  CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
  (* higher cost than the Fractional instance, which kicks in for #qs *)
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
Qed.

Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. rewrite pointsto_unseal. apply pointsto_valid. Qed.
Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[? [= ?]]. done. Qed.
Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[_ [= ?]]. done. Qed.

Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_frac_ne. Qed.
Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_ne. Qed.

Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. rewrite pointsto_unseal. apply pointsto_persist. Qed.
Lemma pointsto_unpersist l v : l ↦□ v ==∗ ∃ q, l ↦{#q} v.
Proof. rewrite pointsto_unseal. apply pointsto_unpersist. Qed.

Global Instance frame_pointsto p l v q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
Proof. apply: frame_fractional. Qed.

Global Instance inv_pointsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto_own. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.
Global Instance inv_pointsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.

Lemma make_inv_pointsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof.
  iIntros (??) "#HI Hl". rewrite pointsto_unseal.
  iApply make_inv_pointsto; done.
Qed.
Lemma inv_pointsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_pointsto_own_inv. Qed.

Lemma inv_pointsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
      inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv". rewrite pointsto_unseal.
  iMod (inv_pointsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl". rewrite pointsto_unseal.
  iMod (inv_pointsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ True).
Proof.
  iIntros (?) "#Hinv Hl". rewrite pointsto_unseal.
  iMod (inv_pointsto_acc with "Hinv Hl") as ([v|]) "(% & Hl & Hclose)"; [done| |done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs IH] forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_pointsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.pointsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n IH] forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton pointsto_unseal.
  iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma lwp_allocN_seq s q i E v n G R o :
  (0 < n)%Z →
  l{{{ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l);
          £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗
          [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "(T& Tb& Gfs& Rs) HP".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  iSplit.
  { iPureIntro. split; first done. destruct n; auto with lia base_step. }
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hs")
    as "(Hs & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite length_replicate Z2Nat.id; auto with lia. }
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iFrame "Hs Ht Hk". iModIntro. iSplitR; first done.
  iModIntro. iApply "HP". iFrame.
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.

Lemma lwp_alloc s q i E v G R o :
  l{{{ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    Alloc (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l);
          £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗
          l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "P HΦ".
  iApply (lwp_allocN_seq with "P"); [auto with lia..|].
  iIntros (l) "/= (?&?&?&?&?&?)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.

Lemma lwp_free s q i E l v G R o :
  l{{{ l ↦ v ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    Free (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET LitV LitUnit;
          £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)}}}.
Proof.
  iIntros (Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_load s q i E l dq v G R o :
  l{{{ l ↦{dq} v ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    Load (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET v; £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hs Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_store s q i E l v' v G R o :
  l{{{ l ↦ v' ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET LitV LitUnit; £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_xchg s q i E l v' v G R o :
  l{{{ l ↦ v' ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET v'; £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_fail s q i E l dq v' v1 v2 G R o :
  v' ≠ v1 → vals_compare_safe v' v1 →
  l{{{ l ↦{dq} v' ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool false); £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hs Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_suc s q i E l v1 v2 v' G R o :
  v' = v1 → vals_compare_safe v' v1 →
  l{{{ l ↦ v' ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool true); £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_faa s q i E l i1 i2 G R o :
  l{{{ l ↦ LitV (LitInt i1) ∗
       thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  l{{{ RET LitV (LitInt i1); £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) "(Hl& T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_new_proph s q i E G R o :
  l{{{thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗ ([∗ map] r ↦ v ∈ R, gl r v)}}}
    NewProph @ s; i; E
  l{{{ pvs p, RET (LitV (LitProphecy p)); £ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) ∗ proph p pvs }}}.
Proof.
  iIntros (Φ) "(T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  rename select proph_id into p.
  iMod (proph_map_new_proph p with "Hk") as "[Hk Hp]"; first done.
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hs Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a base step for [Resolve e _ _] not to be (base) stuck. *)

Lemma resolve_reducible i e σ Θ (p : proph_id) v :
  thread_cond i σ →
  Atomic StronglyAtomic e → reducible i e σ Θ →
  reducible i (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ Θ.
Proof.
  intros Ci A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃ w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A i σ Θ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor; eauto. by apply prim_step_to_val_is_base_step.
Qed.

Lemma step_resolve i Θ e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step i (Resolve e (Val vp) (Val vt)) σ1 Θ κ e2 σ2 efs →
  base_step i (Resolve e (Val vp) (Val vt)) σ1 Θ κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_base_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A i σ1 Θ _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_base_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_base_step.
Qed.

Lemma lwp_resolve s q i E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  thread_exec i q -∗
  (thread_exec i q -∗ lWP e @ s; i; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }}) -∗
  lWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; i; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [lwp_unfold])
     here, since this breaks the lWP abstraction. *)
  iIntros (A He) "Hp T lWPe". rewrite !lwp_unfold /lwp_pre /= He. simpl in *.
  iIntros (Θ σ1 κ κs) "(Ht & Hσ & Hκ)".
  iPoseProof (thread_exec_thread_cond_0 with "T Ht") as "%Ci".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iSpecialize ("lWPe" with "T").
    iMod ("lWPe" $! Θ σ1 [] κs with "[$Ht $Hσ $Hκ]") as "H".
    iModIntro. iMod "H" as "(%Hs& lWPe)".
    iModIntro. iSplit.
    { iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_base_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - iSpecialize ("lWPe" with "T").
    rewrite -assoc.
    iMod ("lWPe" $! Θ σ1 _ _ with "[$Ht $Hσ $Hκ]") as "H".
    iModIntro. iMod "H" as "(%Hs& lWPe)".
    iModIntro. iSplit.
    { iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inv_base_step; simplify_list_eq.
    iMod ("lWPe" $! (Val w') σ2 efs with "[%]") as ">lWPe".
    { by eexists [] _ _. }
    iMod "lWPe" as ">(($& $& Hκ)& lWPe& Efs)".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. iFrame.
    rewrite !lwp_unfold /lwp_pre /=.
    iApply ("lWPe" with "[] HPost"). eauto.
Qed.

End lifting.
