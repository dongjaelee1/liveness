From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From iris.algebra Require Import mono_list.
From transfinite.base_logic.lib Require Import saved_prop.
From lantana.base_logic Require Import invariants.
From lantana.program_logic Require Export history_interp.

(** * The temporal registry

    Every structure whose content is trace-visible (an [alwaysI] invariant or an [untilI])
    is registered here, so that the adequacy proof can find it at every check and certify
    its content at that position. The registry is an append-only list of entries tagged
    with the history position at which they were registered; the adequacy appends a marker
    at every check. Positions are non-decreasing along the list, which lets a record about
    position [n] tell whether an item it mentions was registered before the check at [n]
    (then the check certified it) or during step [n] (then the item's own allocation
    certificate is for [n]).

    Trace properties of contents are identified across the registry by saved predicates on
    traces ([saved_ti]); the agreement they give is up to a later, which the step-indexed
    readings of always and until absorb. *)

Inductive rentry :=
  | RMark
  | RAlways (N : namespace) (γ : gname)
  | RUntil (N : namespace) (k : positive) (γP γQ : gname).

Definition treg_wf (l : list (nat * rentry)) : Prop :=
  ∀ i j pe_i pe_j, i ≤ j → l !! i = Some pe_i → l !! j = Some pe_j → pe_i.1 ≤ pe_j.1.

Lemma treg_wf_nil : treg_wf [].
Proof. intros ???? _ ?. done. Qed.

Lemma treg_wf_app l p e :
  treg_wf l → (∀ pe, pe ∈ l → pe.1 ≤ p) → treg_wf (l ++ [(p, e)]).
Proof.
  intros WF LE i j pi pj LEij Li Lj.
  apply lookup_app_Some in Li as [Li|[Hi Li]]; apply lookup_app_Some in Lj as [Lj|[Hj Lj]].
  - by eapply WF.
  - apply list_lookup_singleton_Some in Lj as [_ <-]. simpl. apply LE. by eapply list_elem_of_lookup_2.
  - apply list_lookup_singleton_Some in Li as [? _]. apply lookup_lt_Some in Lj. lia.
  - apply list_lookup_singleton_Some in Li as [_ <-]. apply list_lookup_singleton_Some in Lj as [_ <-]. done.
Qed.

Lemma treg_wf_lookup_pos l i j pi pj :
  treg_wf l → i ≤ j → l !! i = Some pi → l !! j = Some pj → pi.1 ≤ pj.1.
Proof. intros WF. apply WF. Qed.

(** ** Ghost state *)
Module tregGS.

  Class tregGpreS `{SI : sidx} (Λ : language) (Σ : gFunctors) := TregGpreS {
      #[local] tregGpreS_list :: inG Σ (mono_listUR (leibnizO (nat * rentry)));
      #[local] tregGpreS_pred :: savedPredG Σ (trace Λ);
    }.

  Class tregGS `{SI : sidx} (Λ : language) (Σ : gFunctors) := TregG {
      treg_inG : tregGpreS Λ Σ;
      treg_name : gname;
    }.

  Definition tregΣ `{SI : sidx} (Λ : language) : gFunctors :=
    #[GFunctor (mono_listUR (leibnizO (nat * rentry))); savedAnythingΣ (trace Λ -d> ▶ ∙)].

  Global Instance subG_tregΣ `{SI : sidx} {Λ} {Σ} : subG (tregΣ Λ) Σ → tregGpreS Λ Σ.
  Proof. solve_inG. Qed.

End tregGS.
Import tregGS.
Local Existing Instances treg_inG tregGpreS_list tregGpreS_pred.

Section registry.
  Context `{SI : sidx} `{!tregGS Λ Σ}.

  (** The registry list, its prefixes and its entries. *)
  Definition reg_auth (l : list (nat * rentry)) : iProp Σ :=
    ⌜treg_wf l⌝ ∗ own treg_name (●ML (l : list (leibnizO (nat * rentry)))).
  Definition reg_lb (l : list (nat * rentry)) : iProp Σ :=
    ⌜treg_wf l⌝ ∗ own treg_name (◯ML (l : list (leibnizO (nat * rentry)))).
  Definition reg_idx (j p : nat) (e : rentry) : iProp Σ :=
    ∃ l, ⌜l !! j = Some (p, e) ∧ treg_wf l⌝ ∗ own treg_name (◯ML (l : list (leibnizO (nat * rentry)))).

  Global Instance reg_lb_persistent l : Persistent (reg_lb l).
  Proof. apply _. Qed.
  Global Instance reg_idx_persistent j p e : Persistent (reg_idx j p e).
  Proof. apply _. Qed.
  Global Instance reg_auth_timeless l : Timeless (reg_auth l).
  Proof. apply _. Qed.
  Global Instance reg_lb_timeless l : Timeless (reg_lb l).
  Proof. apply _. Qed.
  Global Instance reg_idx_timeless j p e : Timeless (reg_idx j p e).
  Proof. apply _. Qed.

  Lemma reg_auth_wf l : reg_auth l ⊢ ⌜treg_wf l⌝.
  Proof. by iIntros "[$ _]". Qed.
  Lemma reg_lb_wf l : reg_lb l ⊢ ⌜treg_wf l⌝.
  Proof. by iIntros "[$ _]". Qed.

  Lemma reg_auth_lb l : reg_auth l ⊢ reg_lb l.
  Proof.
    iIntros "[$ H]". rewrite mono_list_auth_lb_op. iDestruct "H" as "[_ $]".
  Qed.

  Lemma reg_lb_idx l j p e : l !! j = Some (p, e) → reg_lb l ⊢ reg_idx j p e.
  Proof. iIntros (?) "[% H]". iExists l. by iFrame. Qed.

  Local Lemma reg_lb_lb_valid l l' :
    own treg_name (◯ML (l : list (leibnizO (nat * rentry)))) -∗
    own treg_name (◯ML (l' : list (leibnizO (nat * rentry)))) -∗
    ⌜l `prefix_of` l' ∨ l' `prefix_of` l⌝.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %V. by apply mono_list_lb_op_valid_L in V. Qed.

  Local Lemma reg_auth_lb_valid l l' :
    own treg_name (●ML (l : list (leibnizO (nat * rentry)))) -∗
    own treg_name (◯ML (l' : list (leibnizO (nat * rentry)))) -∗
    ⌜l' `prefix_of` l⌝.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %V. apply mono_list_both_valid_L in V. iPureIntro. apply V. Qed.

  Lemma reg_auth_idx_lookup l j p e : reg_auth l -∗ reg_idx j p e -∗ ⌜l !! j = Some (p, e)⌝.
  Proof.
    iIntros "[_ Ha] (%l'& [%Hl %]& Hl)".
    iDestruct (reg_auth_lb_valid with "Ha Hl") as %Hpre. iPureIntro. by eapply prefix_lookup_Some.
  Qed.

  Lemma reg_auth_lb_prefix l l' : reg_auth l -∗ reg_lb l' -∗ ⌜l' `prefix_of` l⌝.
  Proof. iIntros "[_ Ha] [_ Hl]". by iApply (reg_auth_lb_valid with "Ha Hl"). Qed.

  Lemma reg_idx_agree j p p' e e' : reg_idx j p e -∗ reg_idx j p' e' -∗ ⌜p = p' ∧ e = e'⌝.
  Proof.
    iIntros "(%l& [%Hl _]& Hl) (%l'& [%Hl' _]& Hl')".
    iDestruct (reg_lb_lb_valid with "Hl Hl'") as %[Hpre|Hpre]; iPureIntro.
    - pose proof (prefix_lookup_Some _ _ _ _ Hl Hpre) as Heq. rewrite Hl' in Heq. by simplify_eq.
    - pose proof (prefix_lookup_Some _ _ _ _ Hl' Hpre) as Heq. rewrite Hl in Heq. by simplify_eq.
  Qed.

  (** The marker argument: an entry is either in the prefix that ends with the marker of
      position [m], or it was registered at a position at least [m]. *)
  Lemma reg_idx_lb_pos l j p e m :
    last l = Some (m, RMark) →
    reg_lb l -∗ reg_idx j p e -∗ ⌜l !! j = Some (p, e) ∨ m ≤ p⌝.
  Proof.
    iIntros (Hlast) "[%WF Hl] (%l'& [%Hl' %WF']& Hl')".
    iDestruct (reg_lb_lb_valid with "Hl Hl'") as %[Hpre|Hpre]; iPureIntro.
    - destruct (decide (j < length l)) as [Hj|Hj].
      + left. apply lookup_lt_is_Some_2 in Hj as [? Hj'].
        pose proof (prefix_lookup_Some _ _ _ _ Hj' Hpre) as Heq. rewrite Hl' in Heq. by simplify_eq.
      + right. destruct l as [|x l0]; first done.
        rewrite last_lookup in Hlast.
        assert (Hm : l' !! Init.Nat.pred (length (x :: l0)) = Some (m, RMark)) by (eapply prefix_lookup_Some; eauto).
        assert (Hle : Init.Nat.pred (length (x :: l0)) ≤ j) by (simpl in *; lia).
        exact (treg_wf_lookup_pos l' _ _ _ _ WF' Hle Hm Hl').
    - left. by eapply prefix_lookup_Some.
  Qed.

  (** Appending an entry whose position dominates the list. *)
  Lemma reg_auth_append l p e :
    (∀ pe, pe ∈ l → pe.1 ≤ p) →
    reg_auth l ==∗ reg_auth (l ++ [(p, e)]) ∗ reg_idx (length l) p e.
  Proof.
    iIntros (LE) "[%WF Ha]".
    iMod (own_update with "Ha") as "Ha".
    { apply mono_list_update. by exists [(p, e)]. }
    iModIntro. assert (WF' : treg_wf (l ++ [(p, e)])) by (by apply treg_wf_app).
    rewrite mono_list_auth_lb_op. iDestruct "Ha" as "[Ha #Hl]".
    iSplitL "Ha"; first by iFrame. iExists _. iFrame "Hl". iPureIntro. split; last done.
    rewrite lookup_app_r; last done. by rewrite Nat.sub_diag.
  Qed.

  (** Saved trace predicates, used to identify the step-indexed reading of a content's
      canonical trace property across the registry. *)
  Definition saved_ti (γ : gname) (f : trace Λ → iProp Σ) : iProp Σ :=
    saved_pred_own γ DfracDiscarded f.
  Global Instance saved_ti_persistent γ f : Persistent (saved_ti γ f).
  Proof. rewrite /saved_ti. apply _. Qed.
  Lemma saved_ti_alloc f : ⊢ |==> ∃ γ, saved_ti γ f.
  Proof. by apply saved_pred_alloc. Qed.
  (** Agreement of the predicates (in [trace Λ -d> iPropO Σ]). *)
  Lemma saved_ti_agree_fun γ (f g : trace Λ -d> iPropO Σ) : saved_ti γ f -∗ saved_ti γ g -∗ ▷ (f ≡ g).
  Proof.
    iIntros "H1 H2". rewrite /saved_ti /saved_pred_own.
    iDestruct (saved_anything_agree with "H1 H2") as "Heq".
    rewrite discrete_fun_equivI. iEval (rewrite discrete_fun_equivI) in "Heq". rewrite bi.later_forall. iIntros (τ).
    iSpecialize ("Heq" $! τ). by rewrite /= later_equivI.
  Qed.

End registry.

(** Allocation of the registry ghost state. *)
Lemma treg_alloc `{SI : sidx} {Λ Σ} `{!tregGpreS Λ Σ} : ⊢ |==> ∃ _ : tregGS Λ Σ, reg_auth [].
Proof.
  iMod (own_alloc (●ML ([] : list (leibnizO (nat * rentry))))) as (γ) "H"; first apply mono_list_auth_valid.
  iModIntro. iExists (TregG _ _ _ _ γ). rewrite /reg_auth. iFrame. iPureIntro. apply treg_wf_nil.
Qed.

(** ** The registry state

    The list, and for every entry a history event at its registration position (which
    bounds the position by the current history index) and the entry's handle, whose
    meaning [Hd] is supplied by the temporal layer. The state is part of the interpretation
    that the program logic threads between steps (temporal_class.v), so registering is a
    plain ghost update. *)
Section registry_state.
  Context `{SI : sidx} `{!invGS Σ} `{!state_interp_class Λ Σ}
    `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS Λ Σ}.

  Definition treg_entries (Hd : rentry → iProp Σ) (l : list (nat * rentry)) : iProp Σ :=
    [∗ list] pe ∈ l, (∃ st, hG_event pe.1 st) ∗ Hd pe.2.

  Definition treg_st (Hd : rentry → iProp Σ) : iProp Σ :=
    ∃ l, reg_auth l ∗ treg_entries Hd l.

  Lemma treg_st_init Hd : reg_auth [] ⊢ treg_st Hd.
  Proof. iIntros "Ha". iExists []. iFrame. by rewrite /treg_entries big_sepL_nil. Qed.

  (** Every registered position is bounded by the current history index. *)
  Lemma treg_entries_bound Hd l h n σ Θ κs :
    treg_entries Hd l -∗ history_interp h n σ Θ κs -∗ ⌜∀ pe, pe ∈ l → pe.1 ≤ n⌝.
  Proof.
    iIntros "Hl HI" (pe Hpe). apply list_elem_of_lookup_1 in Hpe as [i Hi].
    iDestruct (big_sepL_lookup with "Hl") as "[(%st& #He) _]"; first done.
    iDestruct (history_interp_hG_event_lookup with "[$HI $He]") as %Hh.
    iDestruct (history_interp_wf with "HI") as %[Hlen _]. iPureIntro.
    apply lookup_lt_Some in Hh. lia.
  Qed.

  (** Register an entry at the current position. *)
  Lemma treg_st_register Hd e h n σ Θ κs :
    treg_st Hd -∗ (∀ st, hG_event n st -∗ Hd e) -∗
    history_interp h n σ Θ κs ==∗ history_interp h n σ Θ κs ∗ treg_st Hd ∗ ∃ j, reg_idx j n e.
  Proof.
    iIntros "(%l& Ha& Hl) He HI".
    iDestruct (treg_entries_bound with "Hl HI") as %Hb.
    iDestruct (history_interp_hG_event_now with "HI") as "#Hnow".
    iMod (reg_auth_append l n e with "Ha") as "[Ha #Hj]"; first done.
    iModIntro. iFrame "HI". iSplitL; last by iExists _.
    iExists _. iFrame "Ha". rewrite /treg_entries big_sepL_app big_sepL_singleton. iFrame "Hl".
    iSplitR; first by iExists _. by iApply "He".
  Qed.

End registry_state.
