(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Import mono_nat.
From transfinite.base_logic.lib Require Export gen_heap proph_map.
(* From transfinite.base_logic.lib Require Export gen_heap proph_map gen_inv_heap. *)
From liris.base_logic Require Export thread_map gen_inv_heap.
(** adequacy fixes step index to ordinals *)
From liris.program_logic Require Export atomic adequacy.
From liris.program_logic Require Import ectx_lifting.
From liris.heap_lang Require Export class_instances.
From liris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.
From liris.algebra Require Export ordinal_wfocm.

Class heapGS Σ :=
  HeapGS {
      heapGS_mupdGS : mupdGS Σ;
      heapGS_histGS : histGS.histGS Σ (state * thread_pool heap_lang * list (observation));

      #[global] heapGS_gen_heapGS :: gen_heapGS loc (option val) Σ;
      #[global] heapGS_inv_heapGS :: inv_heapGS loc (option val) Σ;
      #[global] heapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
      #[global] heapGS_thread_mapGS :: thread_mapGS thread_id (expr) Σ;
    }.

(** Since we use an [option val] instance of [gen_heap], we need to add a
[Some]. We also seal the definition to avoid confusion between the version from
[gen_heap], and our version with [Some]. That also helps for scopes and
coercions. *)
Local Definition pointsto_def `{heapGS Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
                         (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(** Predicates for label invocations. *)
Definition thread_expr `{heapGS Σ} (i : thread_id) (e : expr) : iProp Σ :=
  (thread i true e 1).

Local Definition label_def `{heapGS Σ}
  (i : thread_id) (x : string) (v : val) : iProp Σ :=
  (∃ (K : ctx heap_lang), ⌜ LanguageCtx K ⌝ ∧ thread_expr i (K (Label x (of_val v)))).
Local Definition label_aux : seal (@label_def). Proof. by eexists. Qed.
Definition label := label_aux.(unseal).
Local Definition label_unseal :
  @label = @label_def := label_aux.(seal_eq).
Global Arguments label {Σ _}.

Definition state_interp `{!heapGS Σ} (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  (gen_heap_interp σ.(heap) ∗
   thread_map_interp (dom Θ) Θ ∗
   proph_map_interp κs σ.(used_proph_id))%I.

Definition state_interp_aux `{!heapGS Σ} (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  ([∗ map] i ↦ e ∈ Θ, thread_expr i e)%I.

(** State predicate. *)
Definition state_pred_interp `{!heapGS Σ} (π : state_pred) : iProp Σ :=
  match π with
  | pred_pointsto l df v =>
      pointsto l df v
  | pred_label i x v =>
      label i x v
  end.

Lemma thread_expr_read `{!heapGS Σ} :
  ∀ (Θ : thread_pool heap_lang) i e,
  thread_map_interp (dom Θ) Θ -∗ thread_expr i e -∗ ⌜Θ !! i = Some e⌝.
Proof.
  iIntros (???) "TI Ti".
  iPoseProof (thread_map_thread_read with "TI Ti") as "%". eauto.
Qed.

Lemma state_interp_wf `{!heapGS Σ} :
  ∀ (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) (π : state_pred),
  state_interp σ Θ κs ∗ state_pred_interp π ⊢ ⌜state_sat σ Θ π⌝.
Proof.
  iIntros (????) "[(HI& TI& PI) SP]". destruct π; simpl.
  - rewrite pointsto_unseal /pointsto_def. iPoseProof (gen_heap_valid with "HI SP") as "%". eauto.
  - rewrite label_unseal /label_def. iDestruct "SP" as "(%&%& Ti)".
    iPoseProof (thread_expr_read with "TI Ti") as "%". eauto.
Qed.

Global Instance heapGS_state_interp_class `{!heapGS Σ} : state_interp_class heap_lang Σ := {
    state_interp := state_interp;
    state_interp_aux := state_interp_aux;
    state_pred_interp := state_pred_interp;
    state_interp_wf := state_interp_wf;
  }.

Global Instance heapGS_temporalGS `{!heapGS Σ} : temporalGS heap_lang Σ := {
    temporal_mupdGS := heapGS_mupdGS;
    temporal_state_interp_class := heapGS_state_interp_class;
    temporal_histGS := heapGS_histGS;
  }.

Global Instance heapGS_lirisGS `{!heapGS Σ} : lirisGS heap_lang Σ := {
    liris_temporalGS := heapGS_temporalGS;
    fork_post i v := (True)%I;
    (* fork_post i v := (thread_term i (of_val v))%I; *)
  }.

(** [gen_inv_heap]: Similar to pointsto,
except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions here. *)
Section definitions.
  Context `{!heapGS Σ}.
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

(* TODO: define tf representations for inv_heap *)

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : gmap thread_id expr.
Implicit Types σ : state.
Implicit Types Θ : thread_pool heap_lang.
Implicit Types l : loc.
Implicit Types e : expr.
Implicit Types v : val.

Local Ltac unfold_defs :=
  (* try rewrite thread_term_unseal /thread_term_def; *)
  try rewrite label_unseal /label_def.

Global Instance thread_expr_timeless i e : Timeless (thread_expr i e).
Proof. apply _. Qed.
Global Instance label_timeless i t v : Timeless (label i t v).
Proof. rewrite label_unseal /label_def. apply _. Qed.

Lemma iter_modal_mono_modal M1 M2 P n :
  (∀ A B, (A -∗ B) -∗ (M1 A -∗ M1 B)) →
  (∀ A, M1 A -∗ M2 A) →
  (Nat.iter n M1 P -∗ Nat.iter n M2 P).
Proof.
  intros. revert P. induction n; intros; simpl; eauto.
  iIntros "H". iApply H0. iApply (H with "[] H"). iApply IHn.
Qed.

Definition trivial_cond : thread_id → iProp Σ := λ _, True%I.

Global Instance trivial_pure_exec_si i : PureExecSI (trivial_cond) i.
Proof.
  repeat intro. iIntros "(_& SI& SIa)".
  iDestruct "SI" as "(HI& TI& PI)".
  iPoseProof (big_sepM_delete _ _ _ _ H0 with "SIa") as "[Ti SIa]".
  iMod (thread_map_thread_update _ _ (K e2) with "[$TI $Ti]") as "[TI Ti]".
  iFrame "HI PI".
  rewrite dom_insert_lookup_L; last eauto. iFrame "TI". iModIntro.
  iApply (big_sepM_insert_delete). iFrame.
Qed.

(** pure steps *)
Lemma lwp_pure_step n o s i E E' e1 e2 φ Φ :
  PureExec φ n e1 e2 →
  φ →
  Nat.iter n
    (λ P,
       |={E,E'}=> ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
                 ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (thP_obls i G 1 -∗
                  ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                  ALC (£ o ={E',E}=∗ P)))
    (lWP e2 @ s; i; E {{ v, Φ v }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hp) "H". iApply (lwp_pure_step); eauto.
  iApply iter_modal_mono_modal. 3: iApply "H".
  - simpl. iIntros "%% HAB >H". iDestruct "H" as "(%& $& $& %& $& H)".
    iIntros "!> TG Crs". iMod ("H" with "TG Crs") as "H".
    iIntros "LC". iMod ("H" with "LC") as "H". by iApply "HAB".
  - simpl. iIntros "% >H". iModIntro. iSplitR; first done.
    iDestruct "H" as "(%& $& $& %& $& H)". iIntros "_ TG Crs".
    iMod ("H" with "TG Crs") as "H". iIntros "LC". iMod ("H" with "LC") as "$". done.
Qed.

Lemma lwp_fork s i E E' e Φ :
  (|={E,E'}=> ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
             ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
             (∀ j, thP_obls i G 1 -∗
                   ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                   thP_obls j ∅ 1 -∗
                   ALC (|={E',E}=>
                   (|={E}=>m Φ (LitV LitUnit)) ∗
                   lWP e @ s; j; ⊤ {{ lift_term j (λ _ _, True) }}))) -∗
  lWP Fork e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step.
  iIntros (K h n σ1 κ κs Θ HK HT) "I". iMod "H" as "(%&$&$& %&$& H)".
  iModIntro. iSplit; first eauto with base_step.
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iEval (rewrite /history_interp -lock) in "I". iDestruct "I" as "(%HI& Ha& (Ih& It& Ip)& Ia)".
  iMod (thread_map_new_thread j e with "It") as "[It Tj]"; first eapply H0.
  iIntros "!> Tb Wcs Efs". iMod ("H" $! j with "Tb Wcs [Efs]") as "H".
  { rewrite dom_singleton_L big_sepS_singleton. eauto. }
  iMod "H" as "(H& E)".
  iMod (hG_history_auth_app with "Ha") as "Ha".
  rewrite /history_interp -lock big_sepM_singleton. iFrame.
  replace (dom (<[i:=K #()]> Θ ∪ {[j := e]})) with (dom Θ ∪ {[j]}); cycle 1.
  { rewrite dom_union_L dom_insert_lookup_L; eauto. rewrite dom_singleton_L. auto. }
  iPoseProof (big_sepM_delete _ _ _ _ HT with "Ia") as "[Ti Ia]".
  iMod (thread_map_thread_update _ _ (K #()) with "[$It $Ti]") as "[It Ti]".
  replace (<[i:=K #()]> (<[j:=e]> Θ)) with (<[i:=K #()]> Θ ∪ {[j := e]}); cycle 1.
  { rewrite -insert_union_l. f_equal. rewrite insert_union_singleton_r; auto. apply not_elem_of_dom. auto. }
  iFrame. iModIntro. iSplitR "H"; cycle 1.
  (* iMod "H". Not working, probably because of the type of expr? *)
  { iApply sfmupd_lwpupd_elim. iMod "H". by iFrame. }
  iSplitR.
  { iPureIntro. destruct HI. split.
    - rewrite length_app H. simpl. lia.
    - rewrite last_app. simpl. auto. }
  iApply (big_sepM_union).
  { apply map_disjoint_singleton_r_2, not_elem_of_dom. rewrite dom_insert_lookup; eauto. }
  rewrite big_sepM_singleton. iFrame "Tj".
  iApply (big_sepM_insert_delete). iFrame.
Qed.

(* (* Wrong spec *) *)
(* Lemma lwp_fork_lat i e : *)
(*   ⊢ <<{ ∀∀ q, label i q }>> Fork e @ i; ∅ *)
(*     <<{ ∃∃ j, label i q ∗ label j 1 | RET (LitV LitUnit); lWP e @ j; ⊤ {{ thread_term j }} }>>. *)
(* Proof. *)
(*   iIntros (Φ) "AU". iApply lwp_fork_fupd. *)
(*   iMod "AU" as (Δ q) "[H↦ [_ Hclose]]". *)
(*   iModIntro. iFrame. *)
(* Qed. *)

(** Label *)
(** We don't need to take an actual step.
    "label i t v" only means that thread i executes "Label t v" in some context,
    and "Label t v" is a pure step.
 *)
Lemma lwpupd_label i E t e v (P : iProp Σ) :
  TCEq (to_val e) (Some v) →
  (* (∀ K n Θ, ⌜LanguageCtx K⌝ -∗ ⌜Θ !! i = Some (K (Label t (of_val v)))⌝ -∗ *)
  (*           label i t v -∗ |={E:n,dom Θ}=>m (label i t v ∗ P)) -∗ *)
  (∀ n D, label i t v -∗ |={E:n,D}=>m (label i t v ∗ P)) -∗
  lwpupd i E (Label t e) P.
Proof.
  Local Transparent lwpupd.
  rewrite /lwpupd. iIntros (He) "H %%%%%% %HK %HT I".
  Local Opaque lwpupd.
  iEval (rewrite /history_interp -lock) in "I". iDestruct "I" as "(%HI& Ha& (Ih& It& Ip)& Ia)".
  iPoseProof (big_sepM_delete _ _ _ _ HT with "Ia") as "[Ti Ia]".
  inv He. apply of_to_val in H0. subst e.
  iMod ("H" $! n (dom Θ) with "[Ti]") as "[Ti $]".
  { rewrite label_unseal /label_def. iFrame. eauto. }
  rewrite label_unseal /label_def. iDestruct "Ti" as "(%&%& Ti)".
  clear dependent K. iPoseProof (thread_expr_read with "It Ti") as "%HT".
  iModIntro. rewrite /history_interp -lock. iFrame. iSplitR; first eauto.
  iApply (big_sepM_delete _ _ _ _ HT). iFrame.
Qed.

(* Label itself is pure, so a pure step rule can take care of the actual step. *)
Lemma lwp_label s i E t e v Φ :
  TCEq (to_val e) (Some v) →
  (∀ n D, label i t v -∗ |={E:n,D}=>m (label i t v ∗ lWP Label t e @ s; i; E {{ Φ }})) -∗
  lWP Label t e @ s; i; E {{ Φ }}.
Proof.
  iIntros (He) "H". iMod (lwpupd_label with "H") as "H". eauto.
Qed.

TODO

Lemma lwp_exit s i E e v Φ :
  TCEq (to_val e) (Some v) →
  thP_obls i ∅ 1 -∗
  label i 1 -∗
  (ALC (th_term i -∗ thread_term i v -∗ |={E}=>m Φ v)) -∗
  lWP Exit e @ s; i; E {{ Φ }}.
Proof.
  unfold_defs. iIntros (He) "Tb Tx H".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "I".
  iModIntro. iPoseProof (thread_None_thread_cond with "Tx I") as "%Ci".
  iSplit.
  { destruct e; inv He. eauto with base_step. }
  iExists ∅. iFrame "Tb". iSplitR; first (rewrite -big_sepM_dom; done).
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
     thP_obls i ∅ 1 ∗
     label i 1 ∗
     (ALC (th_term i -∗ thread_term i v -∗ |={E'}=>m |={E',E}=> Φ v))) -∗
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

Lemma lwp_allocN_seq G R o s q i E v n :
  (0 < n)%Z →
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) }}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l);
          (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗
          [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "(T& Tb& Gfs& Rs) HP".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
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

Lemma lwp_alloc G R o s q i E v :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) }}}
    Alloc (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l);
          (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗
          l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "P HΦ".
  iApply (lwp_allocN_seq with "P"); [auto with lia..|].
  iIntros (l) "/= ((?&?&?&?)&?&?)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.

Lemma lwp_free G R o s q i E l v :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦ v }}}
    Free (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET LitV LitUnit;
          (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) }}}.
Proof.
  iIntros (Φ) "((T& Tb& Gfs& Rs)& Hl) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_load G R o s q i E l dq v :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦{dq} v }}}
    Load (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET v; (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hs Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_store G R o s q i E l v' v :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦ v' }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET LitV LitUnit; (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_xchg G R o s q i E l v' v :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦ v' }}}
    Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET v'; (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_fail G R o s q i E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦{dq} v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool false); (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hs Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_suc G R o s q i E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦ v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool true); (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
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

Lemma lwp_faa G R o s q i E l i1 i2 :
  l{{{ (label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)) ∗ l ↦ LitV (LitInt i1) }}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  l{{{ RET LitV (LitInt i1); (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) "[(T& Tb& Gfs& Rs) Hl] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame "Ht Hk".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_new_proph G R o s q i E :
  l{{{label i q ∗ thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗ ([∗ set] r ∈ R, oblP_id r)}}}
    NewProph @ s; i; E
  l{{{ pvs p, RET (LitV (LitProphecy p)); (£ o ∗ label i q ∗ thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r)) ∗ proph p pvs }}}.
Proof.
  iIntros (Φ) "(T& Tb& Gfs& Rs) HΦ".
  iApply lwp_lift_atomic_base_step_no_fork.
  iIntros (Θ σ1 κ κs) "(Ht & Hs & Hk) !>".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
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
  label i q -∗
  (label i q -∗ lWP e @ s; i; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }}) -∗
  lWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; i; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [lwp_unfold])
     here, since this breaks the lWP abstraction. *)
  iIntros (A He) "Hp T lWPe". rewrite !lwp_unfold /lwp_pre /= He. simpl in *.
  iIntros (Θ σ1 κ κs) "(Ht & Hσ & Hκ)".
  iPoseProof (label_thread_cond_0 with "T Ht") as "%Ci".
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
