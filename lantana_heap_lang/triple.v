(** The fuel-burning triple of the paper and its rules.

    The paper writes [{P}^G_i e {v. Q v}^G'_E]. Here the triple is defined at the HeapLang
    level, with the parts the paper leaves implicit made explicit:
    - the stuckness [s] and the invariant mask [E];
    - the evaluation context [C] around [e] in thread [i]'s expression. The triple carries
      the thread-expression token [thread_expr i C e] along with the carrier predicate
      [thP_carriers i G], so that neither appears in [P] or [Q]. Top-level (closed) triples
      use [C = []], where the token for a value [v] is [exits v@i].

    Triples are persistent by definition. Every triple-based rule displayed in the paper is
    proved below, named [fbtriple_*] and marked with the paper's rule name; the paper elides
    later modalities, masks, and later credits, which appear here. Where a rule deviates from
    the submitted paper, its comment says how: CARRIER-ALLOC and CARRIER-DELETE (post-carriers),
    WIT-IND (one-shot induction hypothesis), and FINALLY-EXIT* (the thread's last step instead
    of [Return]). Logic-level rules (fuels, until, persistence) are restated at the end. *)
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(** The paper's fuel predicate: fuel [μ] at layer [ℓ] for each carrier in [G]. *)
Notation fuels G ℓ μ := ([∗ set] g ∈ G, crP_fuel g ℓ μ)%I.

Section definition.
  Context `{!heapGS Σ}.

  (** The non-persistent core of the triple. It is used on its own only for the induction
      hypothesis of WIT-IND, which is a one-shot triple. *)
  Definition fbtriple_once (s : stuckness) (i : thread_id) (C : list ectx_item) (E : coPset)
      (G G' : gset ocid) (P : iProp Σ) (e : expr) (Q : val → iProp Σ) : iProp Σ :=
    ∀ Φ, thread_expr i C e ∗ thP_carriers i G ∗ P -∗
         (∀ v, thread_expr i C (of_val v) ∗ thP_carriers i G' ∗ Q v -∗ Φ v) -∗
         lWP e @ s; i; E {{ Φ }}.

  (** The fuel-burning triple. *)
  Definition fbtriple (s : stuckness) (i : thread_id) (C : list ectx_item) (E : coPset)
      (G G' : gset ocid) (P : iProp Σ) (e : expr) (Q : val → iProp Σ) : iProp Σ :=
    □ fbtriple_once s i C E G G' P e Q.
End definition.

(** [⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄^G'] is the paper's [{P}^G_i e {v. Q}^G'_E]. The carrier
    sets [G] and [G'] are parsed at level 9, so compound sets need parentheses. *)
Notation "'⦃' P '⦄^' G e @ s ; i ; C ; E '⦃' v , Q '⦄^' G'" :=
  (fbtriple s i C E G G' P%I e%E (λ v, Q%I))
  (at level 20, G at level 9, G' at level 9, P, e, Q at level 200, v name,
   format "'[hv' ⦃  '[' P  ']' ⦄^ G  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' C ;  '/' E  ']' '/' ⦃  '[' v ,  '/' Q  ']' ⦄^ G' ']'") : bi_scope.
Notation "'⦃' P '⦄^' G e @ i ; C ; E '⦃' v , Q '⦄^' G'" :=
  (fbtriple NotStuck i C E G G' P%I e%E (λ v, Q%I))
  (at level 20, G at level 9, G' at level 9, P, e, Q at level 200, v name,
   format "'[hv' ⦃  '[' P  ']' ⦄^ G  '/  ' e  '/' @  '[' i ;  '/' C ;  '/' E  ']' '/' ⦃  '[' v ,  '/' Q  ']' ⦄^ G' ']'") : bi_scope.

Section rules.
  Context `{!heapGS Σ}.
  Implicit Types (P R : iProp Σ) (Q : val → iProp Σ) (e : expr) (v w : val).
  Implicit Types (G : gset ocid) (i : thread_id) (C : list ectx_item).

  Global Instance fbtriple_persistent s i C E G G' P e Q :
    Persistent (fbtriple s i C E G G' P e Q).
  Proof. rewrite /fbtriple. apply _. Qed.

  Lemma fbtriple_once_intro s i C E G G' P e Q :
    fbtriple s i C E G G' P e Q ⊢ fbtriple_once s i C E G G' P e Q.
  Proof. rewrite /fbtriple. iIntros "#$". Qed.

  (** The triple is the texan triple of the case studies, with the token and the carriers
      spelled out. *)
  Lemma fbtriple_texan s i C E G G' P e Q :
    fbtriple s i C E G G' P e Q ⊣⊢
    l{{{ thread_expr i C e ∗ thP_carriers i G ∗ P }}} e @ s; i; E
    l{{{ v, RET v; thread_expr i C (of_val v) ∗ thP_carriers i G' ∗ Q v }}}.
  Proof. done. Qed.

  Lemma fbtriple_conseq s i C E G G' P P' e Q Q' :
    □ (P' -∗ P) -∗ □ (∀ v, Q v -∗ Q' v) -∗
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G' -∗ ⦃ P' ⦄^G e @ s; i; C; E ⦃ v, Q' v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#HP #HQ #H !> %Φ (TE& TG& HP') HΦ".
    iApply ("H" with "[$TE $TG HP']"); first by iApply "HP".
    iIntros (v) "(TE& TG& HQv)". iApply "HΦ". iFrame. by iApply "HQ".
  Qed.

  (** * Structural rules *)

  Lemma fbtriple_value s i C E G v :
    ⊢ ⦃ True ⦄^G (of_val v) @ s; i; C; E ⦃ w, ⌜w = v⌝ ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "!> %Φ (TE& TG& _) HΦ".
    iApply lwp_value. iApply "HΦ". by iFrame.
  Qed.

  (** EXIT *)
  Lemma fbtriple_exit s i C E v :
    ⊢ ⦃ True ⦄^∅ (of_val v) @ s; i; C; E ⦃ w, ⌜w = v⌝ ⦄^∅.
  Proof. apply fbtriple_value. Qed.

  (** A top-level triple, at the empty context and from and to the empty carrier set, gives
      the weakest precondition that adequacy (Theorem 1) consumes: the thread may exit. *)
  Lemma fbtriple_top_lwp s i E P e Q (Ψ : thread_id → val → iProp Σ) :
    (∀ v, Q v ⊢ Ψ i v) →
    ⦃ P ⦄^∅ e @ s; i; []; E ⦃ v, Q v ⦄^∅ -∗
    thread_expr i [] e -∗ thP_carriers i ∅ -∗ P -∗
    lWP e @ s; i; E {{ lift_term i Ψ }}.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (HQ) "#H TE TG HP". iApply lwp_sfgupd.
    iApply ("H" with "[$TE $TG $HP]"). iIntros (v) "(_& TG& HQv)".
    iMod (thread_terminate with "TG") as "Td". iModIntro. rewrite /lift_term. iFrame.
    by iApply HQ.
  Qed.

  (** BIND. The token for [e] lives in the context [K ++ C]. *)
  Lemma fbtriple_bind s i C E K G0 G1 G2 P e Q1 Q2 :
    ⦃ P ⦄^G0 e @ s; i; K ++ C; E ⦃ v, Q1 v ⦄^G1 -∗
    (∀ v, ⦃ Q1 v ⦄^G1 (fill K (of_val v)) @ s; i; C; E ⦃ w, Q2 w ⦄^G2) -∗
    ⦃ P ⦄^G0 (fill K e) @ s; i; C; E ⦃ w, Q2 w ⦄^G2.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H1 #H2 !> %Φ (TE& TG& HP) HΦ".
    iEval (rewrite thread_expr_fill) in "TE". iApply (lwp_bind K).
    iApply ("H1" with "[$TE $TG $HP]"). iIntros (v) "(TE& TG& HQ)".
    iEval (rewrite -thread_expr_fill) in "TE". iApply ("H2" with "[$TE $TG $HQ] HΦ").
  Qed.

  (** FRAME *)
  Lemma fbtriple_frame s i C E G G' P R e Q :
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G' ⊢ ⦃ P ∗ R ⦄^G e @ s; i; C; E ⦃ v, Q v ∗ R ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H !> %Φ (TE& TG& HP& HR) HΦ".
    iApply ("H" with "[$TE $TG $HP]"). iIntros (v) "(TE& TG& HQ)". iApply "HΦ". iFrame.
  Qed.

  (** UPD-ELIM, for Iris's fancy update and for Lantana's ghost update. *)
  Lemma fbtriple_upd_elim s i C E G G' P e Q :
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G' ⊢ ⦃ |={E}=> P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H !> %Φ (TE& TG& >HP) HΦ".
    iApply ("H" with "[$TE $TG $HP] HΦ").
  Qed.

  Lemma fbtriple_gupd_elim s i C E G G' P e Q :
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G' ⊢ ⦃ |={E}=>g P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H !> %Φ (TE& TG& >HP) HΦ".
    iApply ("H" with "[$TE $TG $HP] HΦ").
  Qed.

  (** ALWAYS-ALLOC *)
  Lemma fbtriple_always_alloc s i C E G G' N (I : tf Σ) P e Q :
    (⟦alwaysP N I⟧ₗ ⊢ ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G') →
    ⊢ ⦃ P ∗ ▷ ⟦I⟧ₗ ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once tf_always_logic. iIntros (H) "!> %Φ (TE& TG& HP& HI) HΦ".
    iMod (inv_alloc N with "HI") as "#Hinv".
    iDestruct (H with "Hinv") as "#Ht". iApply ("Ht" with "[$TE $TG $HP] HΦ").
  Qed.

  (** ALWAYS-ACC *)
  Lemma fbtriple_always_acc s i C E G G' N (I : tf Σ) P e Q
      `{!Atomic (stuckness_to_atomicity s) e} :
    ↑N ⊆ E →
    ⟦alwaysP N I⟧ₗ -∗
    ⦃ ▷ ⟦I⟧ₗ ∗ P ⦄^G e @ s; i; C; E ∖ ↑N ⦃ v, ▷ ⟦I⟧ₗ ∗ Q v ⦄^G' -∗
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once tf_always_logic.
    iIntros (HN) "#Hinv #H !> %Φ (TE& TG& HP) HΦ".
    iMod (inv_acc with "Hinv") as "[HI Hclose]"; first done.
    iApply ("H" with "[$TE $TG $HP $HI]"). iIntros (v) "(TE& TG& HI& HQ)".
    iMod ("Hclose" with "HI") as "_". iModIntro. iApply "HΦ". iFrame.
  Qed.

  (** * Carriers and obligations *)

  (** CARRIER-ALLOC. The paper displays the premise's post-carriers as [{g} ∪ G]; they must
      be the conclusion's [G'], since [g] is bound in the premise. *)
  Lemma fbtriple_carrier_alloc s i C E G G' ℓ μ P e Q :
    (∀ g, ⌜g ∉ G⌝ →
          ⦃ P ∗ crP_obls g ℓ ∅ ∗ fuels {[g]} ℓ μ ⦄^({[g]} ∪ G) e @ s; i; C; E ⦃ v, Q v ⦄^G') ⊢
    ⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H !> %Φ (TE& TG& HP) HΦ".
    iMod (carrier_alloc _ _ _ ℓ μ with "TG") as "(%g& %Hg& TG& Cg& Fg)".
    iApply ("H" $! g Hg with "[$TE $TG $HP $Cg Fg] HΦ"). by rewrite big_sepS_singleton.
  Qed.

  (** CARRIER-DELETE. As for CARRIER-ALLOC, the post-carriers are the same in the premise and
      the conclusion. *)
  Lemma fbtriple_carrier_delete s i C E G G' g ℓ P e Q :
    g ∈ G →
    ⦃ P ⦄^(G ∖ {[g]}) e @ s; i; C; E ⦃ v, Q v ⦄^G' ⊢
    ⦃ P ∗ crP_obls g ℓ ∅ ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (Hg) "#H !> %Φ (TE& TG& HP& Cg) HΦ".
    iMod (carrier_delete with "TG Cg") as "TG"; first done.
    iApply ("H" with "[$TE $TG $HP] HΦ").
  Qed.

  (** OBLS-OFFLOAD *)
  Lemma fbtriple_obls_offload s i C E G G' g1 g2 K1 K2 K ℓ1 ℓ2 ℓ P e Q :
    K ⊆ K1 → (ℓ2 <= ℓ)%ordi →
    ⦃ P ∗ crP_obls g1 ℓ1 (K1 ∖ K) ∗ crP_obls g2 ℓ2 (K2 ∪ K) ∗ ⌜K2 ## K⌝ ⦄^G
      e @ s; i; C; E ⦃ v, Q v ⦄^G' ⊢
    ⦃ P ∗ crP_obls g1 ℓ1 K1 ∗ crP_obls g2 ℓ2 K2 ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1) ⦄^G
      e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (HK Hℓ) "#H !> %Φ (TE& TG& HP& C1& C2& OF) HΦ".
    iMod (obl_offload_set with "C1 C2 OF") as "(C1& C2& %Hdisj)"; [done|done|].
    iApply ("H" with "[$TE $TG $HP $C1 $C2] HΦ"). done.
  Qed.

  (** UNTIL-ALLOC *)
  Lemma fbtriple_until_alloc s i C E G G' g K ℓ1 ℓ2 μ N (Φ Ψ : tf Σ) P e Q :
    (ℓ1 <= ℓ2)%ordi →
    (∀ k, ⌜k ∉ K⌝ →
          ⦃ P ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗ ⟦untilP N k 1 Φ Ψ⟧ₗ ∗
            witP_layer k ℓ2 ∗ oblP_fuel k ℓ2 μ ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G') ⊢
    ⦃ P ∗ crP_obls g ℓ1 K ∗ ▷ ⟦Φ⟧ₗ ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (Hℓ) "#H !> %Φ' (TE& TG& HP& Cg& HΦ) Hpost".
    iMod (tf_until_alloc _ _ _ false _ ℓ2 μ with "Cg") as "(%k& %Hk& Cg& Of& #Wl& Acc)"; first done.
    iMod ("Acc" $! _ N Φ Ψ with "HΦ") as "HU".
    iApply ("H" $! k Hk with "[$TE $TG $HP $Cg $HU $Wl $Of] Hpost").
  Qed.

  (** FINALLY-ALLOC* *)
  Lemma fbtriple_finally_alloc s i C E G G' g K ℓ N (Ψ : tf Σ) P e Q :
    (∀ k, ⌜k ∉ K⌝ →
          ⦃ P ∗ crP_obls g ℓ ({[k]} ∪ K) ∗ ⟦finallyP N k 1 Ψ⟧ₗ ⦄^G
            e @ s; i; C; E ⦃ v, Q v ⦄^G') ⊢
    ⦃ P ∗ crP_obls g ℓ K ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "#H !> %Φ' (TE& TG& HP& Cg) Hpost".
    iMod (tf_until_alloc _ _ _ false ℓ ℓ 0 with "Cg") as "(%k& %Hk& Cg& _& _& Acc)"; first done.
    iMod ("Acc" $! _ N (⌜True⌝)%F Ψ with "[]") as "HU".
    { tf_red. by iNext. }
    iApply ("H" $! k Hk with "[$TE $TG $HP $Cg $HU] Hpost").
  Qed.

  (** UNTIL-ACC. Accessing [Φ] takes a later, paid with a later credit. *)
  Lemma fbtriple_until_acc s i C E G G' N k q (Φ Ψ : tf Σ) P e Q
      `{!Atomic (stuckness_to_atomicity s) e} :
    ↑N ⊆ E →
    ⦃ P ∗ ⟦Φ⟧ₗ ⦄^G e @ s; i; C; E ∖ ↑N ⦃ v, Q v ∗ ▷ ⟦Φ⟧ₗ ⦄^G' ⊢
    ⦃ P ∗ ⟦untilP N k q Φ Ψ⟧ₗ ∗ £ 1%ord ⦄^G e @ s; i; C; E
    ⦃ v, Q v ∗ ⟦untilP N k q Φ Ψ⟧ₗ ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (HN) "#H !> %Φ' (TE& TG& HP& HU& LC) Hpost".
    iMod (tf_until_acc with "HU") as "HU"; first done.
    iMod (lc_fupd_elim_later_ord with "LC HU") as "[HΦ Hclose]".
    iApply ("H" with "[$TE $TG $HP $HΦ]"). iIntros (v) "(TE& TG& HQ& HΦ)".
    iMod ("Hclose" with "HΦ") as "HU". iModIntro. iApply "Hpost". iFrame.
  Qed.

  (** UNTIL-DISCHARGE. Discharging takes two laters, paid with later credits. *)
  Lemma fbtriple_until_discharge s i C E G G' N k (Φ Ψ : tf Σ) g ℓ K P e Q
      `{!Atomic (stuckness_to_atomicity s) e} :
    TCEq (to_val e) None → ↑N ⊆ E →
    ⦃ P ∗ ⟦Φ⟧ₗ ⦄^G e @ s; i; C; E ∖ ↑N ⦃ v, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝ ⦄^G' ⊢
    ⦃ P ∗ ⟦untilP N k 1 Φ Ψ⟧ₗ ∗ £ 2 ⦄^G e @ s; i; C; E
    ⦃ v, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k ⦄^G'.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (He Hmask) "#H !> %Φ' (TE& TG& HP& HU& LC) Hpost".
    iMod (tf_until_discharge with "HU") as "HUacc"; first done.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first done.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HUacc" as "[HΦ HUacc]".
    iApply lwp_lwpupd.
    iPoseProof ("H" $! (λ v, |={E ∖ ↑N}=>m |={E ∖ ↑N,E}=> Φ' v)%I with "[$TE $TG $HP $HΦ]") as "Hwp".
    iApply lwp_mono.
    { iIntros (?) "H". iApply sfmupd_lwpupd. iApply "H". }
    iApply "Hwp". iIntros (v) "(TE& TG& HQ& HΨ& Cg& %Ink)".
    iMod ("HUacc" with "HΨ") as ">HUacc".
    iPoseProof ("HUacc" with "[//] Cg") as "HUacc".
    iApply (lc_sfmupd_add_later with "LC"). iNext.
    iMod ("HUacc" $! _) as "HUacc". iModIntro.
    iMod "HUacc" as "(HΨ& Cg& #Od)".
    iApply ("Hpost" with "[$TE $TG $HQ $HΨ $Cg]"). eauto.
  Qed.

  (** WIT-IND. The induction hypothesis is a one-shot triple: it is tied to the remaining
      witness budget, so it cannot be persistent. *)
  Lemma fbtriple_wit_ind s i C E G P e Q k ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    ⦃ P ∗ (witP_cred k 1 ={E}=∗ fuels G ℓ2 μ ∗ fbtriple_once s i C E G G P e Q) ⦄^G
      e @ s; i; C; E ⦃ v, Q v ⦄^G -∗
    witP_layer k ℓ1 -∗
    ⦃ P ∗ fuels G ℓ2 (μ × ▽)%M ⦄^G e @ s; i; C; E ⦃ v, Q v ⦄^G.
  Proof.
    rewrite /fbtriple. iIntros (LTl) "#H #Wl !> %Φ (TE& TG& HP& FS) HΦ".
    iRevert (Φ) "TE TG HP HΦ".
    iAssert (|==> ∀ Φ, thread_expr i C e -∗ thP_carriers i G -∗ P -∗
                       (∀ v, thread_expr i C (of_val v) ∗ thP_carriers i G ∗ Q v -∗ Φ v) -∗
                       lWP e @ s; i; E {{ Φ }})%I with "[-]" as "HA"; cycle 1.
    { iMod "HA" as "HA". iIntros (Φ) "TE TG HP HΦ". iApply ("HA" with "TE TG HP HΦ"). }
    iApply (wit_layer_ind with "[$Wl $FS]"); first done.
    iIntros "!> IH !> %Φ TE TG HP HΦ".
    iApply ("H" with "[$TE $TG $HP IH] HΦ").
    iIntros "Wc". iMod ("IH" with "Wc") as "[Fs IH]". iFrame. iModIntro.
    iIntros (Φ') "(TE& TG& HP) HΦ'". iApply ("IH" with "TE TG HP HΦ'").
  Qed.

  (** * Step rules *)

  (** Fuel at layer 0 can pay for a step, whose rules accept fuel at any layer. *)
  Local Lemma fuels_any_layer G :
    fuels G 0 1 ⊢ [∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1.
  Proof. iIntros "H". iApply (big_sepS_impl with "H"). iIntros "!> %% H". by iExists _. Qed.

  Local Lemma tlc_mult_1 (α : Ord.t) : £ (α × 1)%ord ⊢ £ α.
  Proof. iIntros "LC". iApply (tlc_equiv with "LC"). by rewrite Jacobsthal.mult_1_r. Qed.

  (** STEP-PURE-WIT, for a set [R] of witnessed obligations (the paper shows [R = {k}]). Every
      step gives later credits [£ α] of the proof's choice. *)
  Lemma fbtriple_step_pure_wit s i C E G e v φ (R : gset oid) (α : Ord.t) :
    PureExec φ 1 e (of_val v) → φ →
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    ⦃ fuels G 0 1 ⦄^G e @ s; i; C; E
    ⦃ w, ⌜w = v⌝ ∗ £ α ∗ ([∗ set] r ∈ R, witP_cred r 1 ∨ oblP_discharged r) ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (Hexec Hφ) "#Rs !> %Φ (TE& TG& HF) HΦ".
    iApply (lifting.lwp_pure_step_simple 1 G R α s i E e (of_val v) φ Φ
              (λ i e, thread_expr i C e)); [done|].
    iFrame "TE TG Rs". iSplitL "HF"; first by iApply fuels_any_layer.
    iIntros "TE TG Ws LC". iModIntro. iApply lwp_value. iApply "HΦ". iFrame "TE TG Ws".
    iSplit; first done. by iApply tlc_mult_1.
  Qed.

  (** STEP-PURE-LC *)
  Lemma fbtriple_step_pure_lc s i C E G e v φ (α : Ord.t) :
    PureExec φ 1 e (of_val v) → φ →
    ⊢ ⦃ fuels G 0 1 ⦄^G e @ s; i; C; E ⦃ w, ⌜w = v⌝ ∗ £ α ⦄^G.
  Proof.
    intros Hexec Hφ. iPoseProof (fbtriple_step_pure_wit s i C E G e v φ ∅ α Hexec Hφ with "[]") as "H".
    { by rewrite big_sepS_empty. }
    iApply (fbtriple_conseq with "[] [] H"); first by iIntros "!> $".
    iIntros "!> %w ($& $& _)".
  Qed.

  (** STEP-PURE *)
  Lemma fbtriple_step_pure s i C E G e v φ :
    PureExec φ 1 e (of_val v) → φ →
    ⊢ ⦃ fuels G 0 1 ⦄^G e @ s; i; C; E ⦃ w, ⌜w = v⌝ ⦄^G.
  Proof.
    intros Hexec Hφ. iPoseProof (fbtriple_step_pure_lc s i C E G e v φ 0 Hexec Hφ) as "H".
    iApply (fbtriple_conseq with "[] [] H"); first by iIntros "!> $".
    iIntros "!> %w ($& _)".
  Qed.

  (** STEP-REF *)
  Lemma fbtriple_step_ref s i C E G v (α : Ord.t) :
    ⊢ ⦃ fuels G 0 1 ⦄^G (ref (Val v)) @ s; i; C; E
      ⦃ w, ∃ l : loc, ⌜w = #l⌝ ∗ l ↦ v ∗ £ α ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "!> %Φ (TE& TG& HF) HΦ".
    iApply (lwp_alloc G ∅ α with "[$TE $TG HF]").
    { iSplitL "HF"; first by iApply fuels_any_layer. by rewrite big_sepS_empty. }
    iIntros (l) "(TE& (LC& TG& _)& Hl& _)". iApply "HΦ". iFrame "TE TG LC". iExists l. by iFrame.
  Qed.

  (** STEP-STORE *)
  Lemma fbtriple_step_store s i C E G (l : loc) v w (α : Ord.t) :
    ⊢ ⦃ l ↦ v ∗ fuels G 0 1 ⦄^G (#l <- Val w) @ s; i; C; E
      ⦃ r, ⌜r = #()⌝ ∗ l ↦ w ∗ £ α ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "!> %Φ (TE& TG& Hl& HF) HΦ".
    iApply (lwp_store G ∅ α with "[$TE $TG HF $Hl]").
    { iSplitL "HF"; first by iApply fuels_any_layer. by rewrite big_sepS_empty. }
    iIntros "(TE& (LC& TG& _)& Hl)". iApply "HΦ". iFrame. done.
  Qed.

  (** STEP-LOAD *)
  Lemma fbtriple_step_load s i C E G (l : loc) dq v (α : Ord.t) :
    ⊢ ⦃ l ↦{dq} v ∗ fuels G 0 1 ⦄^G (! #l) @ s; i; C; E
      ⦃ w, ⌜w = v⌝ ∗ l ↦{dq} v ∗ £ α ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros "!> %Φ (TE& TG& Hl& HF) HΦ".
    iApply (lwp_load G ∅ α with "[$TE $TG HF $Hl]").
    { iSplitL "HF"; first by iApply fuels_any_layer. by rewrite big_sepS_empty. }
    iIntros "(TE& (LC& TG& _)& Hl)". iApply "HΦ". iFrame. done.
  Qed.

  (** FORK*. The child is a fresh thread [j], so its triple is top-level ([C = []], mask [⊤])
      and must end with no carriers. The paper shows the instance [K = K1 = {k}]. *)
  Lemma fbtriple_fork s i C E G g1 ℓ μ K K1 P e (α : Ord.t) :
    K ⊆ K1 →
    (∀ j g2, ⦃ fuels {[g2]} ℓ μ ∗ crP_obls g2 ℓ K ∗ P ⦄^{[g2]} e @ s; j; []; ⊤ ⦃ _, True ⦄^∅) -∗
    ⦃ fuels G 0 1 ∗ crP_obls g1 ℓ K1 ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1) ∗ P ⦄^G
      (Fork e) @ s; i; C; E
    ⦃ w, ⌜w = #()⌝ ∗ crP_obls g1 ℓ (K1 ∖ K) ∗ £ α ⦄^G.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (HK) "#Hc !> %Φ (TE& TG& HF& Cg& OF& HP) HΦ".
    iApply (lwp_fork ℓ μ K P G ∅ α s i E e g1 K1 with "[] [$TE $TG HF $Cg $OF $HP]"); first done.
    { iIntros (j g2 Ψ) "!> (TE& TG& HF& Cg& HP) HΨ".
      iApply lwp_sfgupd. iApply ("Hc" with "[$TE $TG $HF $Cg $HP]").
      iIntros (v) "(_& TG& _)". iMod (thread_terminate with "TG") as "Td". iModIntro.
      iApply "HΨ". rewrite /lift_term. by iFrame. }
    { iSplitL "HF"; first by iApply fuels_any_layer. by rewrite big_sepS_empty. }
    iIntros "(TE& (LC& TG& _)& Cg)". iApply "HΦ". iFrame. done.
  Qed.

  (** STEP-PURE-WIT as displayed, for one witnessed obligation [k]. *)
  Lemma fbtriple_step_pure_wit1 s i C E G e v φ k ℓk (α : Ord.t) :
    PureExec φ 1 e (of_val v) → φ →
    witP_layer k ℓk -∗
    ⦃ fuels G 0 1 ⦄^G e @ s; i; C; E
    ⦃ w, ⌜w = v⌝ ∗ £ α ∗ (witP_cred k 1 ∨ oblP_discharged k) ⦄^G.
  Proof.
    iIntros (Hexec Hφ) "#Wl".
    iPoseProof (fbtriple_step_pure_wit s i C E G e v φ {[k]} α Hexec Hφ with "[]") as "H".
    { rewrite big_sepS_singleton. by iExists ℓk. }
    iApply (fbtriple_conseq with "[] [] H"); first by iIntros "!> $".
    iIntros "!> %w ($& $& Ws)".
    by iDestruct (big_sepS_singleton (λ r, witP_cred r 1 ∨ oblP_discharged r)%I k with "Ws") as "$".
  Qed.

  (** FORK* as displayed: one obligation [k] moves to the child. *)
  Lemma fbtriple_fork1 s i C E G g1 ℓ μ k P e (α : Ord.t) :
    (∀ j g2, ⦃ fuels {[g2]} ℓ μ ∗ crP_obls g2 ℓ {[k]} ∗ P ⦄^{[g2]} e @ s; j; []; ⊤ ⦃ _, True ⦄^∅) -∗
    ⦃ fuels G 0 1 ∗ crP_obls g1 ℓ {[k]} ∗ oblP_fuel k ℓ 1 ∗ P ⦄^G (Fork e) @ s; i; C; E
    ⦃ w, ⌜w = #()⌝ ∗ crP_obls g1 ℓ ∅ ∗ £ α ⦄^G.
  Proof.
    iIntros "#Hc".
    iPoseProof (fbtriple_fork s i C E G g1 ℓ μ {[k]} {[k]} P e α with "Hc") as "H"; first done.
    iApply (fbtriple_conseq with "[] [] H").
    - iIntros "!> ($& $& Of& $)". by iApply (big_sepS_singleton (λ k, oblP_fuel k ℓ 1)%I k).
    - iIntros "!> %w". rewrite difference_diag_L. iIntros "($& $& $)".
  Qed.

  (** * Termination *)

  (** Thread [i] has reached [v] at the empty context: discharge the exit obligation [k], whose
      [finally] predicate [exits v@i] the token now establishes. This is a model update, so it
      happens at a step. *)
  Local Lemma exits_discharge i E v g ℓ K k N :
    ↑N ⊆ E → k ∈ K →
    thread_expr i [] (of_val v) -∗ £ (2 : Ord.t) -∗ crP_obls g ℓ K -∗
    ⟦finallyP N k 1 (exits v@i)⟧ₗ -∗ |={E}=>m
    thread_expr i [] (of_val v) ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hmask Hk) "TE LC Cg HF".
    iMod (tf_until_discharge with "HF") as "HF"; first set_solver.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
    iMod ("HF" with "[TE]") as "HF".
    { iNext. iEval (rewrite tf_atomic_logic). iFrame. }
    iPoseProof ("HF" with "[//] Cg") as "HF".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HF" $! _) as "HF". iMod "HF" as "(TE& $& $)". by iFrame.
  Qed.

  (** FINALLY-EXIT*, the exit rule: the last step of thread [i], here a pure step to [v] at the
      empty context, discharges the exit obligation [k] (its [finally] predicate is [exits v@i])
      and retires the carrier [g]. *)
  Lemma fbtriple_finally_exit s i E g ℓ k N e v φ :
    PureExec φ 1 e (of_val v) → φ → ↑N ⊆ E →
    ⊢ ⦃ fuels {[g]} 0 1 ∗ crP_obls g ℓ {[k]} ∗ ⟦finallyP N k 1 (exits v@i)⟧ₗ ⦄^{[g]}
        e @ s; i; []; E ⦃ w, ⌜w = v⌝ ⦄^∅.
  Proof.
    rewrite /fbtriple /fbtriple_once. iIntros (Hexec Hφ HN) "!> %Φ (TE& TG& HF& Cg& Hfin) HΦ".
    iApply (lifting.lwp_pure_step_simple 1 {[g]} ∅ 2 s i E e (of_val v) φ Φ
              (λ i e, thread_expr i [] e)); [done|].
    iFrame "TE TG". iSplitL "HF"; first by iApply fuels_any_layer.
    iSplitR; first by rewrite big_sepS_empty.
    iIntros "TE TG _ LC". iPoseProof (tlc_mult_1 with "LC") as "LC".
    iMod (exits_discharge with "TE LC Cg Hfin") as "(TE& Cg& _)"; [done|set_solver|].
    replace ({[k]} ∖ {[k]} : gset _) with (∅ : gset oid) by set_solver.
    iMod (carrier_delete with "TG Cg") as "TG"; first set_solver.
    replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
    iModIntro. iApply lwp_value. iApply "HΦ". by iFrame.
  Qed.

End rules.

(** * Logic-level rules of the paper, under the paper's names *)
Section logic.
  Context `{!heapGS Σ}.
  Implicit Types (G : gset ocid).

  (** FUELS-ADD *)
  Lemma fuels_add G ℓ μ1 μ2 : fuels G ℓ (μ1 ⊕ μ2)%M ⊣⊢ fuels G ℓ μ1 ∗ fuels G ℓ μ2.
  Proof. apply crP_fuel_add_set. Qed.

  (** FUELS-UNION *)
  Lemma fuels_union G G' ℓ μ : fuels (G ∪ G') ℓ μ ⊣⊢ fuels (G ∖ G') ℓ μ ∗ fuels G' ℓ μ.
  Proof. rewrite -big_sepS_union; last set_solver. by rewrite difference_union_L. Qed.

  (** FUELS-EMPTY *)
  Lemma fuels_empty ℓ μ : ⊢ fuels ∅ ℓ μ.
  Proof. by rewrite big_sepS_empty. Qed.

  (** FUELS-MONO: fuel can be lowered to a smaller measure, compared by its interpretation at
      layer [ℓ]. *)
  Lemma fuels_mono G ℓ μ1 μ2 :
    (measure_rep (ℓ, 0) μ1 <= measure_rep (ℓ, 0) μ2)%ord → fuels G ℓ μ2 ⊢ |==> fuels G ℓ μ1.
  Proof. apply crP_fuel_mon_set. Qed.

  (** Fuel of some carriers can be dropped; this generalizes FUELS-EMPTY. *)
  Lemma fuels_weaken G G' ℓ μ : G' ⊆ G → fuels G ℓ μ ⊢ fuels G' ℓ μ.
  Proof. iIntros (HG) "H". by iApply (big_sepS_subseteq with "H"). Qed.

  (** FUELS-LAYER *)
  Lemma fuels_layer G ℓ1 ℓ2 μ : (ℓ1 < ℓ2)%ordi → fuels G ℓ2 1 ⊢ |==> fuels G ℓ1 μ.
  Proof. apply crP_fuel_extend_set. Qed.

  (** Persistence facts. *)
  Lemma always_persistent N (I : tf Σ) : Persistent ⟦alwaysP N I⟧ₗ.
  Proof. apply _. Qed.
  Lemma persistently_persistent (P : iProp Σ) : Persistent (□ P).
  Proof. apply _. Qed.
  Lemma persistent_dup (P : iProp Σ) : Persistent P → P ⊢ P ∗ P.
  Proof. intros. iIntros "#H". iFrame "H". Qed.
  Lemma wit_layer_persistent k ℓ : Persistent (witP_layer k ℓ).
  Proof. apply _. Qed.
  Lemma obl_done_persistent k : Persistent (oblP_discharged k).
  Proof. apply _. Qed.

  (** LÖB *)
  Lemma lob (P : iProp Σ) : (▷ P → P) ⊢ P.
  Proof. apply bi.löb. Qed.

  (** LC-SPEND *)
  Lemma lc_spend E (P : iProp Σ) : £ 1%ord ∗ ▷ P ⊢ |={E}=> P.
  Proof. iIntros "[LC HP]". iApply (lc_fupd_elim_later_ord with "LC HP"). Qed.

  (** UNTIL-DONE-FALSE *)
  Lemma until_done_false N k q (Φ Ψ : tf Σ) :
    ⟦untilP N k q Φ Ψ⟧ₗ ∗ oblP_discharged k ⊢ False.
  Proof. iIntros "[HU Od]". iApply (tf_until_discharged_false with "HU Od"). Qed.

  (** UNTIL-SPLIT *)
  Lemma until_split N k q1 q2 (Φ Ψ : tf Σ) :
    ⟦untilP N k q1 Φ Ψ⟧ₗ ∗ ⟦untilP N k q2 Φ Ψ⟧ₗ ⊣⊢ ⟦untilP N k (q1 + q2) Φ Ψ⟧ₗ.
  Proof. symmetry. apply (fractional (Φ := λ q, ⟦untilP N k q Φ Ψ⟧ₗ)). Qed.
End logic.
