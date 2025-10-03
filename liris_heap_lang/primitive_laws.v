(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Import mono_nat.
From transfinite.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From liris.algebra Require Import ordinal_wfocm.
From liris.program_logic Require Export weakestpre.
From liris.program_logic Require Import ectx_lifting.
From liris.heap_lang Require Export class_instances.
From liris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

TODO
(* Define threadsGS *)

Class heapGS_gen `{SI : indexT} Σ := HeapGS {
  heapGS_invGS : invGS Σ;
  heapGS_osatGS : osatGS.osatGS (WF:=ord_wfocm_pack) (language.state heap_lang) thread_id Σ;
  heapGS_othreadGS : othreadGS.othreadGS Σ;
  heapGS_otreeGS : otreeGS.otreeGS Ord.t Σ;

  #[global] heapGS_gen_heapGS :: gen_heapGS loc (option val) Σ;
  #[global] heapGS_inv_heapGS :: inv_heapGS loc (option val) Σ;
  #[global] heapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt : mono_natG Σ;
}.
Local Existing Instance heapGS_step_cnt.

Notation heapGS := (heapGS_gen HasLc).

Section steps.
  Context `{SI : indexT} `{!heapGS_gen hlc Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own heapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own heapGS_step_name n.

  Lemma steps_lb_0 :
    ⊢ |==> steps_lb 0.
  Proof. by apply mono_nat_lb_own_0. Qed.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by iApply mono_nat_lb_own_le. Qed.

End steps.

Global Program Instance heapGS_lirisGS `{SI : indexT} `{!heapGS_gen hlc Σ} : lirisGS_gen hlc heap_lang Σ := {
  liris_invGS := heapGS_invGS;
  liris_osatGS := heapGS_osatGS;
  liris_schedfairGS := heapGS_schedfairGS;
  liris_threadoblGS := heapGS_threadoblGS;
  state_interp σ step_cnt κs _ :=
    (gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id) ∗
     steps_auth step_cnt)%I;
  fork_post _ := True%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  iIntros (???? σ ns κs τ)  "/= ($ & $ & H)".
  by iMod (steps_auth_update_S with "H") as "$".
Qed.

(** Since we use an [option val] instance of [gen_heap], we need to add a
[Some]. We also seal the definition to avoid confusion between the version from
[gen_heap], and our version with [Some]. That also helps for scopes and
coercions. *)
Local Definition pointsto_def `{SI : indexT} `{@heapGS_gen SI hlc Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {SI hlc Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{SI : indexT} `{!heapGS_gen hlc Σ}.
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

Section lifting.
Context `{SI : indexT} `{!heapGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma lwp_lb_update s i n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  lWP e @ s; i; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  lWP e @ s; i; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [lwp_unfold])
  here, since this breaks the lWP abstraction. *)
  rewrite !lwp_unfold /lwp_pre /=. iIntros (->) "Hlb Hlwp".
  iIntros (δ1 Ω1 γ1 σ1 ns κ κs m) "(Hτ & Hsf & Hos & Hto & Hoft & Hσ & Hκ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hlwp" $! δ1 Ω1 γ1 σ1 ns κ κs m with "[$Hτ $Hsf $Hos $Hto $Hoft $Hσ $Hκ $Hsteps]") as "[%Hs Hlwp]".
  iModIntro. iSplit; [done|]. iDestruct "Hlwp" as "(%&%&Hlwp)". iExists _. iSplit; [done|].
  iIntros (e2 σ2 efs Hstep) "% % % Hcred".
  iDestruct ("Hlwp" with "[//] [//] Hcred") as "Hlwp".
  iMod "Hlwp" as "Hlwp". iModIntro. iNext. iMod "Hlwp" as "Hlwp". iIntros "!>".
  iApply (step_fupdN_wand with "Hlwp").
  iIntros "Hlwp". iMod "Hlwp" as "(% & % & % & % & ($ & $ & $ & $ & $ & $ & Hsteps)& Hlwp & $)".
  iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
  iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
  iModIntro. iExists _. iSplit; [done|]. iFrame "Hsteps".
  iApply (lwp_wand with "Hlwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(* (** A stronger version of [tlwp_lwp_step] to turn a TlWP into a lWP. Provided *)
(* [steps_lb n], this version gives us [S n] laters ([tlwp_lwp_step] gives just one) *)
(* and [S n] later credits ([tlwp_lwp_step] gives i none). *) *)
(* Lemma tlwp_lwp_step_lc s i n E e P Φ : *)
(*   TCEq (to_val e) None → *)
(*   steps_lb n -∗ *)
(*   ▷^(S n) P -∗ *)
(*   lWP e @ s; i; E [{ v, P -∗ £ (S n) ={E}=∗ Φ v }] -∗ *)
(*   lWP e @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (?) "#Hlb HP Hlwp". *)
(*   iApply (tlwp_lwp_fupdN_strong (S n) _ _ _ _ (P ∗ £ (S n))); [done|]. iSplit. *)
(*   - iIntros (σ ns κ m) "(Hσ & Hκ & Hsteps)". *)
(*     iDestruct (steps_lb_valid with "[$] [$]") as %?. *)
(*     iApply fupd_mask_intro_discard; [set_solver|]. *)
(*     iPureIntro. rewrite /num_laters_per_step /=. lia. *)
(*   - iSplitL "HP". *)
(*     + iIntros "!> ?". iApply step_fupdN_intro; [done|]. *)
(*       iIntros "!> !>". by iFrame. *)
(*     + iApply (tlwp_wand with "Hlwp"). *)
(*       iIntros (v) "H [??]". by iApply ("H" with "[$]"). *)
(* Qed. *)

(* (** A version of [tlwp_lwp_step_lc] that provides only a single later modality *)
(* (but still [S n] later credits). This version is tailored to lift total Texan *)
(* triples to a partial Texan triples with later credits, see e.g., [lwp_alloc_lc] *)
(* below. *) *)
(* Lemma tlwp_lwp_step_lc_texan s i n E e P Φ : *)
(*   TCEq (to_val e) None → *)
(*   steps_lb n -∗ *)
(*   ▷ P -∗ *)
(*   lWP e @ s; i; E [{ v, P -∗ £ (S n) ={E}=∗ Φ v }] -∗ *)
(*   lWP e @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros (?) "#Hlb HP Hlwp". *)
(*   iApply (tlwp_lwp_step_lc with "[$] [HP] Hlwp"); auto. *)
(* Qed. *)

Lemma lwp_step_fupdN_lb s i n E1 E2 e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hlwp".
  iApply lwp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (σ ns κs nt) "(? & ? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. rewrite /num_laters_per_step /=. lia.
Qed.

(* (** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *) *)
(* Lemma lwp_rec_löb s i E f x e Φ Ψ : *)
(*   □ ( □ (∀ v, Ψ v -∗ lWP (rec: f x := e)%V v @ s; i; E {{ Φ }}) -∗ *)
(*      ∀ v, Ψ v -∗ lWP (subst' x v (subst' f (rec: f x := e) e)) @ s; i; E {{ Φ }}) -∗ *)
(*   ∀ v, Ψ v -∗ lWP (rec: f x := e)%V v @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ". *)
(*   iApply lifting.lwp_pure_step_later; first done. *)
(*   iIntros "!> _". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ". *)
(*   iApply ("IH" with "HΨ"). *)
(* Qed. *)

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma lwp_fork s i E e Φ :
  (∀ σ ns κs τ, state_interp σ ns κs τ ={E,∅}=∗
                ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ heap_ectx_lang ⌉)) ∗
                       (∀ j, ⌜ j ∉ τ ⌝ -∗
                             toL_thread i q L -∗
                             sfS_fuel_credit_forallL heap_ectx_lang -∗
                             toL_thread j 1 [] -∗
                             £ 1 ={∅,E}=∗
                             |={E}▷=> (state_interp σ (S ns) κs (τ ∪ {[ j ]}) ∗
                                      Φ (LitV LitUnit) ∗
                                      lWP e @ s; j; ⊤ {{ lift_term j (λ _ : val, True) }}))) -∗
  lWP Fork e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κ κs τ) "Hσ". iSpecialize ("H" $! σ1 ns (κ ++ κs) τ with "Hσ").
  iMod "H" as "(%&%& $ & $ &H)". iModIntro. iSplit; first by eauto with base_step.
  iIntros (v2 σ2 efs Hstep) "HL Hsf HLs Hcred"; inv_base_step.
  iMod ("H" $! i0 H0 with "HL Hsf [HLs] Hcred") as "H".
  { replace (dom {[i0 := e]}) with ({[i0]} : gset _) by set_solver. by rewrite big_sepS_singleton. }
  iModIntro. by rewrite big_sepM_singleton.
Qed.

Lemma tlwp_fork s E e Φ :
  lWP e @ s; i; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ lWP Fork e @ s; i; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply tlwp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κs i nt) "(?&?&Hsteps) !>"; iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  by iFrame.
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

Lemma tlwp_allocN_seq s E v n :
  (0 < n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  iSplit; first by destruct n; auto with lia base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite length_replicate Z2Nat.id; auto with lia. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; do 2 (iSplit; first done). iFrame "Hσ Hκs Hsteps". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.
Lemma lwp_allocN_seq s E v n :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply tlwp_allocN_seq; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_allocN_seq_lc s E v n n' :
  (0 < n)%Z →
  {{{ steps_lb n' }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  {{{ l, RET LitV (LitLoc l); ([∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) ∗ £ (S n') }}}.
Proof.
  iIntros (Hn Φ) "#? HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply tlwp_allocN_seq; [by auto..|]; iIntros (l) "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_alloc s E v :
  [[{ True }]]
    Alloc (Val v) @ s; i; E
  [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply tlwp_allocN_seq; [auto with lia..|].
  iIntros (l) "/= (? & _)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.
Lemma lwp_alloc s E v :
  {{{ True }}}
    Alloc (Val v) @ s; i; E
  {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply tlwp_alloc; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_alloc_lc s E v n :
  {{{ steps_lb n }}}
    Alloc (Val v) @ s; i; E
  {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "#? HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply tlwp_alloc; [by auto..|]; iIntros (l) "[??] HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_free s E l v :
  [[{ l ↦ v }]] Free (Val $ LitV $ LitLoc l) @ s; i; E
  [[{ RET LitV LitUnit; True }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma lwp_free s E l v :
  {{{ ▷ l ↦ v }}} Free (Val $ LitV (LitLoc l)) @ s; i; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_free with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_free_lc s E l v n :
  {{{ steps_lb n ∗ ▷ l ↦ v }}} Free (Val $ LitV (LitLoc l)) @ s; i; E
  {{{ RET LitV LitUnit; £ (S n) }}}.
Proof.
  iIntros (Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_free with "H"); [by auto..|]; iIntros "H HΦ ? !>". by iApply "HΦ".
Qed.

Lemma tlwp_load s E l dq v :
  [[{ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ s; i; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; [done|]. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma lwp_load s E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; i; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_load with "H"). iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_load_lc s E l dq v n :
  {{{ steps_lb n ∗ ▷ l ↦{dq} v }}}
    Load (Val $ LitV $ LitLoc l) @ s; i; E
  {{{ RET v; l ↦{dq} v ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_load with "H"). iIntros "H HΦ ? !>". iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma lwp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; i; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_store with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_store_lc s E l v' v n :
  {{{ steps_lb n ∗ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; i; E
  {{{ RET LitV LitUnit; l ↦ v ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_store with "H"); [by auto..|]; iIntros "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_xchg s E l v' v :
  [[{ l ↦ v' }]] Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  [[{ RET v'; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma lwp_xchg s E l v' v :
  {{{ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; i; E
  {{{ RET v'; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_xchg with "H"); [by auto..|]. iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_xchg_lc s E l v' v n :
  {{{ steps_lb n ∗ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; i; E
  {{{ RET v'; l ↦ v ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_xchg with "H"); [by auto..|]. iIntros "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma lwp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_cmpxchg_fail_lc s E l dq v' v1 v2 n :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ steps_lb n ∗ ▷ l ↦{dq} v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' ∗ £ (S n) }}}.
Proof.
  iIntros (?? Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma lwp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_cmpxchg_suc_lc s E l v1 v2 v' n :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ steps_lb n ∗ ▷ l ↦ v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ £ (S n) }}}.
Proof.
  iIntros (?? Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma tlwp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]]
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply tlwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs i nt) "(Hσ & Hκs & Hsteps) !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ e2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma lwp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (tlwp_lwp_step with "HΦ").
  iApply (tlwp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
Lemma lwp_faa_lc s E l i1 i2 n :
  {{{ steps_lb n ∗ ▷ l ↦ LitV (LitInt i1) }}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "[#? >H] HΦ". iApply (tlwp_lwp_step_lc_texan with "[$] HΦ").
  iApply (tlwp_faa with "H"); [by auto..|]; iIntros "H HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.

Lemma lwp_new_proph s E :
  {{{ True }}}
    NewProph @ s; i; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply lwp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs i nt) "(Hσ & HR & Hsteps) !>". iSplit; first by eauto with base_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_". inv_base_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit; first done. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a base step for [Resolve e _ _] not to be (base) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_base_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  base_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
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
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_base_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_base_step.
Qed.

Lemma lwp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  lWP e @ s; i; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  lWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; i; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [lwp_unfold])
     here, since this breaks the lWP abstraction. *)
  iIntros (A He) "Hp lWPe". rewrite !lwp_unfold /lwp_pre /= He. simpl in *.
  iIntros (σ1 ns κ κs i nt) "(Hσ & Hκ & Hsteps)".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("lWPe" $! σ1 ns [] κs i nt with "[$Hσ $Hκ $Hsteps]") as "[Hs lWPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; i; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_base_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("lWPe" $! σ1 ns _ _ nt with "[$Hσ $Hκ $Hsteps]") as "[Hs lWPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; i; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step) "Hcred". apply step_resolve in step; last done.
    inv_base_step; simplify_list_eq.
    iMod ("lWPe" $! (Val w') σ2 efs with "[%] Hcred") as "lWPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "lWPe" as "lWPe". iModIntro.
    iApply (step_fupdN_wand with "lWPe"); iIntros "> [($ & Hκ & $) lWPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !lwp_unfold /lwp_pre /=. iDestruct "lWPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

End lifting.
