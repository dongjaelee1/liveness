(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export weakestpre.
From liris Require Import ordinal_wfocm.
From iris.prelude Require Import options.

Local Definition obl_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k : iProp Σ :=
  oblG_elem k.
Local Definition obl_aux : seal (@obl_def). Proof. by eexists. Qed.
Definition obl := obl_aux.(unseal).
Local Definition obl_unseal :
  @obl = @obl_def := obl_aux.(seal_eq).
Global Arguments obl {SI Λ Σ _}.

Local Definition oGoal_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k T P : iProp Σ :=
  oblG_goal k T P ∗ obl k.
Local Definition oGoal_aux : seal (@oGoal_def). Proof. by eexists. Qed.
Definition oGoal := oGoal_aux.(unseal).
Local Definition oGoal_unseal :
  @oGoal = @oGoal_def := oGoal_aux.(seal_eq).
Global Arguments oGoal {SI Λ Σ _}.

(* Eventually, P always holds. *)
Local Definition oEA_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k P : iProp Σ :=
  (∃ T, oblG_goal k T P).
Local Definition oEA_aux : seal (@oEA_def). Proof. by eexists. Qed.
Definition oEA := oEA_aux.(unseal).
Local Definition oEA_unseal :
  @oEA = @oEA_def := oEA_aux.(seal_eq).
Global Arguments oEA {SI Λ Σ _}.

Local Definition oDone_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k : iProp Σ :=
  oblG_done k ∗ obl k.
Local Definition oDone_aux : seal (@oDone_def). Proof. by eexists. Qed.
Definition oDone := oDone_aux.(unseal).
Local Definition oDone_unseal :
  @oDone = @oDone_def := oDone_aux.(seal_eq).
Global Arguments oDone {SI Λ Σ _}.

Local Definition oFuel_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k a : iProp Σ :=
  oblG_fuel k a ∗ obl k.
Local Definition oFuel_aux : seal (@oFuel_def). Proof. by eexists. Qed.
Definition oFuel := oFuel_aux.(unseal).
Local Definition oFuel_unseal :
  @oFuel = @oFuel_def := oFuel_aux.(seal_eq).
Global Arguments oFuel {SI Λ Σ _}.

Local Definition oWit_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k ℵ : iProp Σ :=
  owitnessG_witness k ℵ ∗ obl k.
Local Definition oWit_aux : seal (@oWit_def). Proof. by eexists. Qed.
Definition oWit := oWit_aux.(unseal).
Local Definition oWit_unseal :
  @oWit = @oWit_def := oWit_aux.(seal_eq).
Global Arguments oWit {SI Λ Σ _}.

Local Definition oCred_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k a : iProp Σ :=
  owitnessG_credit k a ∗ obl k.
Local Definition oCred_aux : seal (@oCred_def). Proof. by eexists. Qed.
Definition oCred := oCred_aux.(unseal).
Local Definition oCred_unseal :
  @oCred = @oCred_def := oCred_aux.(seal_eq).
Global Arguments oCred {SI Λ Σ _}.

Local Definition tHas_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  i Ψ q : iProp Σ :=
  othreadG_obls i Ψ q ∗ othreadG_exec i (q/2) ∗ othreadG_elem i ∗
  ([∗ set] k ∈ Ψ, obl k ∗ oblG_live k (1/2/2)%Qp ∗ othreadG_owns i k (1/2)%Qp).
Local Definition tHas_aux : seal (@tHas_def). Proof. by eexists. Qed.
Definition tHas := tHas_aux.(unseal).
Local Definition tHas_unseal :
  @tHas = @tHas_def := tHas_aux.(seal_eq).
Global Arguments tHas {SI Λ Σ _}.

Local Definition tTerm_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  i : iProp Σ :=
  othreadG_term i ∗ othreadG_elem i.
Local Definition tTerm_aux : seal (@tTerm_def). Proof. by eexists. Qed.
Definition tTerm := tTerm_aux.(unseal).
Local Definition tTerm_unseal :
  @tTerm = @tTerm_def := tTerm_aux.(seal_eq).
Global Arguments tTerm {SI Λ Σ _}.

Section lifting.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Ltac unfold_defs :=
  try rewrite !tTerm_unseal /tTerm_def;
  try rewrite !tHas_unseal /tHas_def;
  try rewrite !oCred_unseal /oCred_def;
  try rewrite !oWit_unseal /oWit_def;
  try rewrite !oFuel_unseal /oFuel_def;
  try rewrite !oDone_unseal /oDone_def;
  try rewrite !oEA_unseal /oEA_def;
  try rewrite !oGoal_unseal /oGoal_def;
  try rewrite !obl_unseal /obl_def.

Section liveness_preds.

  Global Instance obl_persistent k : Persistent (obl k).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oGoal_persistent k T P : Persistent (oGoal k T P).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oEA_persistent k P : Persistent (oEA k P).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oDone_persistent k : Persistent (oDone k).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oWit_persistent k ℵ : Persistent (oWit k ℵ).
  Proof. unfold_defs. apply _. Qed.
  Global Instance tTerm_persistent i : Persistent (tTerm i).
  Proof. unfold_defs. apply _. Qed.

  Global Instance obl_timeless k : Timeless (obl k).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oDone_timeless k : Timeless (oDone k).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oFuel_timeless k a : Timeless (oFuel k a).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oWit_timeless k ℵ : Timeless (oWit k ℵ).
  Proof. unfold_defs. apply _. Qed.
  Global Instance oCred_timeless k a : Timeless (oCred k a).
  Proof. unfold_defs. apply _. Qed.
  Global Instance tHas_timeless i Ψ q : Timeless (tHas i Ψ q).
  Proof. unfold_defs. apply _. Qed.
  Global Instance tTerm_timeless i : Timeless (tTerm i).
  Proof. unfold_defs. apply _. Qed.

  Local Open Scope ord.

  (** oFuel rules *)
  Lemma oFuel_eq k a0 a1 :
    (a0 == a1) → oFuel k a0 = oFuel k a1.
  Proof.
    unfold_defs. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
  Qed.
  Lemma oFuel_eq_list L a0 a1 :
    (a0 == a1) →
    ([∗ list] i ∈ L, oFuel i a0)%I ≡ ([∗ list] i ∈ L, oFuel i a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite oFuel_eq; eauto. Qed.
  Lemma oFuel_eq_set L a0 a1 :
    a0 == a1 →
    ([∗ set] i ∈ L, oFuel i a0)%I ≡ ([∗ set] i ∈ L, oFuel i a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite oFuel_eq; eauto. Qed.

  Lemma oFuel_mon k a0 a1 :
    (a0 <= a1)%ord → oFuel k a1 ==∗ oFuel k a0.
  Proof.
    unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
  Qed.
  Lemma oFuel_mon_list L a0 a1 :
    a0 <= a1 →
    ([∗ list] i ∈ L, oFuel i a1) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oFuel_mon.
  Qed.
  Lemma oFuel_mon_set L a0 a1 :
    a0 <= a1 →
    ([∗ set] i ∈ L, oFuel i a1) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oFuel_mon.
  Qed.

  Lemma oFuel_split k a0 a1 :
    oFuel k (a0 ⊕ a1)%ord ⊣⊢ oFuel k a0 ∗ oFuel k a1.
  Proof.
    unfold_defs. rewrite oblG_fuel_split. iSplit.
    - iIntros "((P1& P2)& #Be)"; iFrame; eauto.
    - iIntros "((P1& B1)& (P2& B2))"; iFrame.
  Qed.
  Lemma oFuel_split_list L a0 a1 :
    ([∗ list] i ∈ L, oFuel i (a0 ⊕ a1)) ⊣⊢ ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oFuel_split.
  Qed.
  Lemma oFuel_split_set L a0 a1 :
    ([∗ set] i ∈ L, oFuel i (a0 ⊕ a1)) ⊣⊢ ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oFuel_split.
  Qed.

  Lemma oFuel_mon_split k a0 a1 a2 :
    ((a0 ⊕ a1) <= a2)%ord → oFuel k a2 ==∗ oFuel k a0 ∗ oFuel k a1.
  Proof.
    unfold_defs. iIntros (Hle) "(P& #Be)".
    iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
    iFrame; eauto.
  Qed.
  Lemma oFuel_mon_split_list L a0 a1 a2 :
    (a0 ⊕ a1) <= a2 →
    ([∗ list] i ∈ L, oFuel i a2) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oFuel_mon_list with "H") as ">H"; first done.
    by iApply oFuel_split_list.
  Qed.
  Lemma oFuel_mon_split_set L a0 a1 a2 :
    (a0 ⊕ a1) <= a2 →
    ([∗ set] i ∈ L, oFuel i a2) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oFuel_mon_set with "H") as ">H"; first done.
    by iApply oFuel_split_set.
  Qed.

  Lemma oFuel_lt k a0 a1 :
    a0 < a1 →
    oFuel k a1 ⊢ |==> oFuel k a0 ∗ oFuel k Ord.one.
  Proof.
    unfold_defs. iIntros (Hlt) "(P& #Be)".
    iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
    iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
  Qed.
  Lemma oFuel_lt_list L a0 a1 :
    a0 < a1 →
    ([∗ list] i ∈ L, oFuel i a1) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i Ord.one).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oFuel_lt.
  Qed.
  Lemma oFuel_lt_set L a0 a1 :
    a0 < a1 →
    ([∗ set] i ∈ L, oFuel i a1) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i Ord.one).
  Proof.
    iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oFuel_lt.
  Qed.

  (** oCred rules *)
  Lemma oCred_eq k a0 a1 :
    (a0 == a1)%ord → oCred k a1 = oCred k a0.
  Proof.
    unfold_defs. intros. rewrite (owitnessG_credit_eq k a0 a1); auto.
  Qed.
  Lemma oCred_mon k a0 a1 :
    (a0 <= a1)%ord → oCred k a1 ==∗ oCred k a0.
  Proof.
    unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply owitnessG_credit_mon.
  Qed.
  Lemma oCred_split k a0 a1 :
    oCred k (a0 ⊕ a1)%ord ⊣⊢ oCred k a0 ∗ oCred k a1.
  Proof.
    unfold_defs. rewrite owitnessG_credit_split. iSplit.
    - iIntros "((P1& P2)& #Be)"; iFrame; eauto.
    - iIntros "((P1& B1)& (P2& B2))"; iFrame.
  Qed.
  Lemma oCred_mon_split k a0 a1 a2 :
    ((a0 ⊕ a1) <= a2)%ord → oCred k a2 ==∗ oCred k a0 ∗ oCred k a1.
  Proof.
    unfold_defs. iIntros (Hle) "(P& #Be)".
    iMod (owitnessG_credit_mon_split with "P") as "[P1 P2]"; first done.
    iFrame; eauto.
  Qed.

  (** oWit rules *)
  Lemma oWit_mon k a0 a1 :
    (a0 <= a1)%ord → oWit k a0 ==∗ oWit k a1.
  Proof.
    unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply owitnessG_witness_mon.
  Qed.
  Lemma oWit_cred_compare k a0 a1 :
    oWit k a0 -∗ oCred k a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
  Proof.
    unfold_defs. iIntros "(P& Be) (Cred& _)". iApply (owitnessG_compare with "[$]").
  Qed.
  Lemma oWit_cred_spend_gen k a0 a1 :
    oWit k a0 -∗ oCred k a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ oWit k a2.
  Proof.
    unfold_defs. iIntros "(Ow& $) (Oc& _)". iApply (owitnessG_credit_spend_gen with "[$]").
  Qed.
  Lemma oWit_cred_spend k a0 a1 :
    (Ord.O < a1)%ord →
    oWit k a0 -∗ oCred k a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ oWit k a2.
  Proof.
    unfold_defs. iIntros (LT) "(Ow& $) (Oc& _)". iApply (owitnessG_credit_spend with "[$]"). done.
  Qed.
  Lemma oWit_cred_spend_one k a :
    oWit k a -∗ oCred k Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ oWit k a0.
  Proof.
    iIntros "Ow Oc". iApply (oWit_cred_spend with "Ow Oc"). apply Ord.S_pos.
  Qed.

  (** tHas rules *)
  Lemma tHas_op_1 i Ψ1 Ψ2 q1 q2 :
    tHas i Ψ1 q1 -∗ tHas i Ψ2 q2 -∗ tHas i (Ψ1 ∪ Ψ2) (q1 + q2).
  Proof.
    unfold_defs. iIntros "(T1& E1& #Te1& Es1) (T2& E2& #Te2& Es2)".
    iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
    iPoseProof (othreadG_obls_op_1 with "[$T1 $T2]") as "T". iFrame.
    iCombine "E1 E2" as "E". iPoseProof (othreadG_exec_frac_op with "E") as "E"; first reflexivity.
    rewrite Qp.div_add_distr. iFrame. iSplitR; auto.
    rewrite big_sepS_union; auto. iFrame.
  Qed.
  Lemma tHas_op_2 i Ψ1 Ψ2 q1 q2 :
    Ψ1 ## Ψ2 →
    tHas i (Ψ1 ∪ Ψ2) (q1 + q2) -∗ (tHas i Ψ1 q1 ∗ tHas i Ψ2 q2).
  Proof.
    unfold_defs. iIntros (Hd) "(T& E& #Te& Es)".
    iPoseProof (othreadG_obls_op_2 with "T") as "[T1 T2]"; first auto.
    rewrite Qp.div_add_distr. iPoseProof (othreadG_exec_frac_op _ (q1/2) (q2/2) with "E") as "[E1 E2]"; first auto.
    iFrame. iFrame "Te". rewrite -big_sepS_union; auto.
  Qed.

End liveness_preds.

Section foupd.

  Lemma alloc_obl E i Ψ q T P a :
    tHas i Ψ q -∗
    |={E}=>o ∃ k, ⌜ k ∉ Ψ ⌝ ∗ tHas i ({[k]} ∪ Ψ) q ∗ obl k ∗ oGoal k T P ∗ oEA k P ∗ oFuel k a ∗ oWit k (owfun a).
  Proof.
    unfold_defs. iIntros "(Tbs& Texi& #Tei& Tds)". iIntros (???) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iApply oupd_unfold. iRight.
    rewrite /oproto. iIntros (??) "(S& T& A& N& %OW)".
    assert (∃ k, k ∉ dom Ω1).
    { exists (fresh (dom Ω1)). apply is_fresh. }
    assert (Dom1 : dom Ω1 = dom W1).
    (* FIXME : apply obl_wit_dom. does not work; type unification not reduced enough? *)
    { apply (obl_wit_dom _ _ _ OW). }
    destruct H as (k& Nink).
    iMod (osat_alloc_obl _ k i a T P with "S") as "(S& #Bgk& #Bek& Blk& Bok& Bfk)". 1: done.
    iPoseProof (oblG_owner_div_2 with "Bok") as "[Bok Bok2]".
    iMod (othread_alloc_obl with "[$S $T $Tbs $Bek $Blk $Bok2]") as "(S& T& %Nink2& Tbs& Tok& Blk)".
    iPoseProof (othreadG_owns_div_2 with "Tok") as "[Tok Tok2]".
    iPoseProof (oassigned_add_obl with "[$A $Bek Bok Tok2]") as "A".
    { iLeft. iFrame. }
    iMod (owitness_alloc_wit _ k (owfun a) with "N") as "[N #Nwk]".
    { rewrite -Dom1. done. }
    iModIntro. iFrame "S T". iSplitR.
    { iPureIntro. econstructor 2. eapply obl_states_step_alloc.
      exists k. eexists. split; last done. by apply not_elem_of_dom. }
    iIntros (W2 [ProgW OW2]).
    iMod (owitness_obl_wit_alloc with "N") as "N". 1: eapply Nink. all: eauto.
    iModIntro. iSplitL "A N".
    { rewrite dom_insert_L. iFrame. auto. }
    iApply oupd_unfold. iLeft. iModIntro. iMod "close" as "_". iModIntro.
    iFrame "SI Tbs Texi Tei Bek Bgk Bfk Nwk".
    iSplitR; first auto.
    iApply big_sepS_union. 1: set_solver.
    iFrame "Tds". iApply big_sepS_singleton. iFrame. auto.
  Qed.

End foupd.

Section liveness.

  TODO

  (* For lwp_step, enable progress and fork. *)
  Lemma lwp_step_pc s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∃ π Ψ K,
         (⌜Ψ = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
          ([∗ set] ρ ∈ Ψ, oblG_elem ρ ∗ oblG_fuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      othreadG_obls i Ψ 1 -∗
                      ((([∗ set] ρ ∈ Ψ, oblG_fuel ρ Ord.one) ∗
                        ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2))) ∨
                         (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ oblG_fuel k ψ))) -∗
                      ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                      ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
    ⊢ lwp_step s i E e1 ν.
  Proof.



  Lemma lwp_step_account_pc s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∃ Ψ q,
         (othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
          [∗ set] ρ ∈ Ψ, oblG_elem ρ ∗ othreadG_owns i ρ true q ∗ oblG_fuel ρ Ord.one) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      othreadG_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othreadG_owns i ρ true q) -∗
                      ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                      ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%Hstuck& %&%& (#Tei& Tbsi& Bps)& H)".
    iModIntro. iSplitR; first done. iExists Ω1. iSplitR; first done.
    iIntros (??? Hstep).
    iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (true, q) Ψ) with "[S T F Tbsi Bps]")
      as "(%& %Hprog& S& T& F& Tbsi &Tos)".
    { by rewrite dom_gset_to_gmap. }
    { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Bps").
      iIntros "!>" (??). iIntros "(E& O& P)". iFrame. iPureIntro. apply Ord.S_lt. }
    rewrite big_sepM_gset_to_gmap.
    iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
    { symmetry. eapply fork_thread_ids; eauto. }
    iModIntro. iMod ("H" with "[//] Tbsi Tos Efs") as ">[I H]".
    iModIntro. iExists Ω1, Ω', Ω'.
    assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
    iFrame. iPureIntro. split; done.
  Qed.

  Lemma lwp_step_suspended_pc s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∃ π Ψ K,
         (⌜Ψ = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
          ([∗ set] ρ ∈ Ψ, oblG_elem ρ ∗ oblG_fuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      othreadG_obls i Ψ 1 -∗
                      ((([∗ set] ρ ∈ Ψ, oblG_fuel ρ Ord.one) ∗
                        ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2))) ∨
                         (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ oblG_fuel k ψ))) -∗
                      ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                      ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%Hstuck& %&%&%& (%Dom& #Tei& Tbsi& Bps)& H)".
    iModIntro. iSplitR; first done. iExists Ω1. iSplitR; first done.
    iIntros (??? Hstep).
    iDestruct "Bps" as "(#Beπ& #Feπ& Bps& M)".
    iAssert ([∗ map] k ↦ _ ∈ K, oblG_elem k)%I with "[Bps]" as "#Bes".
    { rewrite Dom -big_sepM_dom. iApply (big_sepM_impl with "Bps"). iIntros "!>" (???) "[H _]". iFrame. }
    iMod (oforest_wait_cases_many _ _ _ ((λ '(x, ψ), (x, i, ψ)) <$>K) with "[S U F M]") as "(S& F& [(Fws& Fos& U) | (U& #Bdπ& M)])".
    { iFrame. iSplitR; first eauto. iSplitR; first eauto.
      rewrite big_sepM_fmap. iApply (big_sepM_impl with "M"). iIntros "!>" (???). destruct x. by iIntros. }
    - rewrite !big_sepM_fmap.
      iAssert (
          ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k false (1/2)) ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_edge π k 1)
        )%I with "[Fos]" as "[Fos Fes]".
      { iApply big_sepM_sep. iApply (big_sepM_impl with "Fos"). iIntros "!>" (???) "A". destruct x. iFrame. }
      iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (false, (1/2)%Qp) Ψ) with "[S T F Tbsi Fos]")
        as "(%& %Hprog& S& T& F& Tbsi& Fos)".
      { by rewrite dom_gset_to_gmap. }
      { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
        iSplitR; first auto. iApply (big_sepM_impl with "Fos"). iIntros "!>" (???) "H". by destruct x. }
      iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos". iPoseProof ("U" with "[Fes Fos]") as "U".
      { subst Ψ. rewrite -big_sepM_dom. iPoseProof (big_sepM_sep_2 with "Fos Fes") as "Fs".
        iApply (big_sepM_impl with "Fs"). iIntros "!>" (???) "H". by destruct x. }
      iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
      { symmetry. eapply fork_thread_ids; eauto. }
      iModIntro. iMod ("H" with "[//] Tbsi [Bps Fws] Efs") as ">[I H]".
      { iLeft. iSplitR "Fws".
        - iPoseProof (big_sepS_sep with "Bps") as "[H1 H2]". iFrame.
        - iApply (big_sepM_impl with "Fws"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω1, Ω', Ω'.
      assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
      iFrame. iPureIntro. split; done.
    - rewrite !big_sepM_fmap.
      iAssert (
          ([∗ map] k ↦ _ ∈ K, othreadG_owns i k true (1/2) ∗ oblG_fuel k Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, oblG_fuel k ψ)
        )%I with "[Bps M]" as "[Tos Bps]".
      { subst Ψ. rewrite -big_sepM_dom -big_sepM_sep. iPoseProof (big_sepM_sep_2 with "Bps M") as "M".
        iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H". destruct x. iDestruct "H" as "((_&B)&C&D)". iFrame. }
      iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (true, (1/2)%Qp) Ψ) with "[S T F Tbsi Tos]")
        as "(%& %Hprog& S& T& F& Tbsi& Fos)".
      { by rewrite dom_gset_to_gmap. }
      { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
        iSplitR; first auto. iApply (big_sepM_impl with "Tos"). iIntros "!>" (???) "[H1 H2]".
        iFrame. iPureIntro. apply Ord.S_pos. }
      iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos".
      iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
      { symmetry. eapply fork_thread_ids; eauto. }
      iModIntro. iMod ("H" with "[//] Tbsi [Bps Fos] Efs") as ">[I H]".
      { iRight. iSplitR; first auto. subst Ψ. rewrite -big_sepM_dom.
        iPoseProof (big_sepM_sep_2 with "Fos Bps") as "H".
        iApply (big_sepM_impl with "H"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω1, Ω', Ω'.
      assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
      iFrame. iPureIntro. split; done.
  Qed.

  (* For ghost_step, enable allocating, progressing, suspendring, resolving and waiting for obligations. *)
  Lemma ghost_step_wait_obls E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i Ψ π K,
         (⌜Ψ = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
         (othreadG_obls i Ψ 1 -∗
          (([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2)) ∨
             (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ oblG_fuel k ψ))) -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%&%& (%Dom& #Tei& Tbsi& Bps)& H)".
    iDestruct "Bps" as "(#Beπ& #Feπ& M)".
    iMod (oforest_wait_cases_many _ _ _ ((λ '(x, ψ), (x, i, ψ)) <$>K) with "[S U F M]") as "(S& F& [(Fws& Fos& U) | (U& #Bdπ& M)])".
    { iFrame. iSplitR; first eauto. iSplitR; first eauto.
      rewrite big_sepM_fmap. iApply (big_sepM_impl with "M"). iIntros "!>" (???). destruct x. by iIntros. }
    - rewrite !big_sepM_fmap.
      iPoseProof ("U" with "Fos") as "U".
      iMod ("H" with "Tbsi [Fws]") as "[I H]".
      { iLeft. iApply (big_sepM_impl with "Fws"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω. iFrame. done.
    - rewrite !big_sepM_fmap.
      iMod ("H" with "Tbsi [M]") as "[I H]".
      { iRight. iSplitR; first auto. iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω. iFrame. done.
  Qed.

  Lemma ghost_step_alloc_obl E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i Ψ q,
         othreadG_elem i ∗ othreadG_obls i Ψ q ∗
         (∃ T P α β, ∀ k,
            ⌜k ∉ Ψ⌝ -∗ othreadG_obls i ({[k]} ∪ Ψ) q -∗
            oblG_elem k -∗ oblG_goal k T P -∗
            oblG_suspend_bound k α -∗ oblG_suspend k α -∗ oblG_fuel k β -∗
            othreadG_owns i k true (1/2)%Qp -∗ otreeG_elem k -∗
            |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%& #Tei& Tbs& %&%&%&%& H)".
    iMod (osat_alloc_obl _ α i  β T P with "S") as "(%k& %Nink& S& #Bgk& #Bek& Blk& Btk& #Btbk& Bok& Bpsk& Bpk)".
    assert (Nink2 : k ∉ dom Ω) by (by apply not_elem_of_dom in Nink).
    iMod (osuspend_alloc_obl _ _ Nink2 with "U") as "(U& #Fek)".
    iMod (othread_alloc_obl with "[S T Tbs Blk]") as "(S& T& %NinkΨ& Tbs& Tok& Blk)"; first (iFrame; eauto).
    iPoseProof (oblG_owner_div_2 _ _ (1/2)%Qp with "Bok") as "[Bok1 Bok2]".
    iMod (othread_obl_acquire with "[T Tok Bok1]") as "(T& Tok)"; first (iFrame; eauto).
    iPoseProof (othreadG_owns_div_2 _ _ _ (1)%Qp with "Tok") as "[Tok1 Tok2]".
    iMod (oforest_alloc_obl _ _ _ α β Nink2 with "[F Tok1 Blk Bok2 Bpsk]") as "F"; first (iFrame; eauto).
    iMod ("H" with "[//] Tbs Bek Bgk Btbk Btk Bpk Tok2 Fek") as "[I H]".
    iModIntro. iExists (<[k:=olive α i β]> Ω). rewrite !dom_insert_L. iFrame.
    iPureIntro. eapply rtc_l; last reflexivity. eapply obl_states_step_alloc.
    exists k. eauto.
  Qed.

  Lemma ghost_step_resolve_obl E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i Ψ q k T P,
         othreadG_elem i ∗ othreadG_obls i Ψ q ∗ othreadG_owns i k true (1/2)%Qp ∗ ⌜k ∈ Ψ⌝ ∗
         oblG_elem k ∗ oblG_goal k T P ∗ ⌜T σ⌝ ∗ (▷ P) ∗
         (othreadG_obls i (Ψ ∖ {[k]}) q -∗ oblG_done k -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%&%&%&%& #Tei& Tbs& Toi& %Ink& #Bek& #Bgk& GT& GP& H)".
    iMod (oforest_resolve_one with "[$]") as "(%&%&%&%Prog& S& T& U& F& #Bdk& Tbs)"; first auto.
    iMod ("H" with "Tbs Bdk") as "[I H]". iModIntro. iFrame. iPureIntro. destruct Prog as [Prog1 Prog2].
    eapply rtc_l.
    - eapply obl_states_step_resolve; eauto.
    - eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto.
  Qed.

  Lemma ghost_step_suspend_obls_gen E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ π ℵ K,
         (oblG_elem π ∗ oblG_suspend_bound π ℵ ∗
          ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K,
             ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
             oblG_elem k ∗ otreeG_elem k ∗ oblG_suspend k α ∗ oblG_suspend k β)) ∗
         (((oblG_done π ∗
            [∗ map] k ↦ '(θ, ψ, α, β) ∈ K, othreadG_owns θ k true (1/2)%Qp ∗ oblG_suspend k α ∗ oblG_suspend k β) ∨
             ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K, ∃ x, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp)) -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%& (#Beπ& #Btbπ& M)& H)".
    iPoseProof (osat_elem_cases _ π with "[S]") as "[%Live | #Bdπ]"; first (iFrame; eauto); cycle 1.
    { iMod ("H" with "[M]") as "[I H]".
      - iLeft. iSplitR; first eauto. iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H".
        destruct x as [[[? ?] ?] ?]. iDestruct "H" as "(%& H1& H2& H3& H4& H5)". iFrame.
      - iModIntro. iExists Ω. iFrame. done. }
    iAssert (([∗ map] k↦'(θ, ψ, _, _) ∈ K, ∃ x : positive, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1 / 2)) ={∅,E}=∗
              state_interp σ Θ κs ∗ ν)%I with "[H]" as "H".
    { iIntros "A". iApply "H". by iRight. }
    iStopProof. revert Ω Live. induction K using map_ind; iIntros (Ω Live) "((#Beπ& #Btbπ)& S& T& U& F& M& K)".
    { iMod ("K" with "[]") as "[I K]".
      - done.
      - iModIntro. iExists Ω. iFrame. done. }
    rewrite !big_sepM_insert; auto. destruct x as [[[θ ψ] α] β].
    iDestruct "M" as "[(%LT& #Teθ& Toi& #Bii& #Tei& Bti1& Bti2) M]". destruct LT as [LT1 LT2].
    destruct Live as [d Live].
    iDestruct (oforest_suspend_one_tree _ _ i θ π ψ ℵ α β with "[$]")
      as "[(S& T& U& F& Toi& Bti1& Bti2& #Bdπ) | >(%&%&%Prog1& S& T& U& F& Susi)]".
    1,2: simpl; auto.
    { iPoseProof (osat_obl_is_done_weak _ π with "[S]") as "%"; first (iFrame; eauto).
      destruct H0. by rewrite Live in H0. }
    destruct Prog1 as [Prog1 DecC]. iMod (IHK Ω' with "[-]") as "H".
    { specialize (Prog1 π). rewrite Live in Prog1. inv Prog1. destruct H2. destruct (DecC π (obl_live d)).
      - apply H0 in H3 . destruct y; try done. rewrite -H1. eauto.
      - apply H2 in H3. rewrite -H1 -H3. eauto. }
    2:{ iDestruct "H" as "(%& %Prog2& H)". iModIntro. iFrame. iPureIntro. etrans; last eauto.
        eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto. }
    clear IHK. iSplitR; first eauto. iFrame. iIntros "M". iApply "K". iFrame.
  Qed.

  Lemma ghost_step_progress_obls_gen E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ K,
         (([∗ map] k ↦ '(θ, ψ) ∈ K,
             othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
             ∃ a, ⌜(Ord.O < a)%ord⌝ ∗ oblG_elem k ∗ oblG_suspend k a) ∗
          (([∗ map] k ↦ '(θ, ψ) ∈ K, othreadG_owns θ k true (1/2)%Qp ∗ oblG_fuel k ψ) -∗
           |={∅,E}=> state_interp σ Θ κs ∗ ν)))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%& M& H)".
    iStopProof. revert Ω. induction K using map_ind; iIntros (Ω) "(S& T& U& F& M& K)".
    { iMod ("K" with "[]") as "[I K]".
      - done.
      - iModIntro. iExists Ω. iFrame. done. }
    rewrite !big_sepM_insert; auto. destruct x as [θ ψ].
    iDestruct "M" as "((#Teθ& Toi& %& %LTa& #Bei& Bti)& M)".
    iMod (oforest_get_progress_one _ _ θ i a ψ with "[S T F Toi Bti]") as "(%&%&%& S& T& F& Toi& Bpi)".
    { simpl; auto. }
    { iFrame. auto. }
    destruct H0 as [Prog1 DecC]. iMod (IHK Ω' with "[-]") as "H".
    2:{ iDestruct "H" as "(%& %Prog2& H)". iModIntro. iFrame. iPureIntro. etrans; last eauto.
        eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto. }
    clear IHK. assert (dom Ω' = dom Ω).
    { apply obl_states_cond_rel_dom in Prog1. auto. }
    rewrite -!H0. iFrame. iIntros "M". iApply "K". iFrame.
  Qed.

  Lemma ghost_step_terminate E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i,
         othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2) ∗
         (othreadG_term i -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%& Tbs& Tei& H)".
    iMod (othread_exec_to_term with "[T Tei Tbs]") as "(T& #Tti)"; first iFrame.
    iMod ("H" with "Tti") as "[I H]". iModIntro. iFrame. done.
  Qed.

  Lemma ghost_step_done_acc E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ k T P,
         oblG_goal k T P ∗ oblG_done k ∗
         ((▷ P) ={∅,E}=∗ (▷ P) ∗ state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%& #Bg& #Bd& H)".
    iPoseProof (osat_done_open _ k T P with "[$S $Bg $Bd]") as "[HP S]".
    iMod ("H" with "HP") as "(HP& $& $)".
    iFrame. iModIntro. iSplitR; first done. by iApply "S".
  Qed.

  Lemma ghost_step_done_pers E ν k T P :
    Persistent P →
    oblG_goal k T P -∗ oblG_done k -∗ ((▷ P) -∗ ν) -∗ ghost_step E ν.
  Proof.
    iIntros (?) "#Bg #Bd H". iApply ghost_step_done_acc.
    iIntros (???) "I".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iFrame "Bg Bd". iIntros "#HP". iMod "Hclose" as "_". iFrame.
    iModIntro. iFrame "HP". by iApply "H".
  Qed.

  (* lwp versions with interface definitions *)
  Lemma lwp_lift_step_fupd s ς i E e1 Φ :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                    ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                    |={∅,E}=>
       state_interp σ2 (Θ ∪ dom efs) κs ∗
       lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
    { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
      iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
    iApply lwp_step_progress_no_lc.
    iIntros (????) "I". iMod ("H" with "I") as "(%& H)". destruct H as [_ H].
    iModIntro. iSplitR; first done.
    iIntros (????) "Efs". iMod ("H" with "[//] [Efs]") as "(I& H& Efs)".
    - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
    - iFrame. iApply (lwp_cond_elim with "H Hc").
  Qed.

  Lemma lwp_lift_step_fupd_lc s ς i E e1 Φ :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∃ Ψ q,
         (tHas i Ψ 1 ∗ [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                      ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                      ALC (|={∅,E}=>
                             state_interp σ2 (Θ ∪ dom efs) κs ∗
                             lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
    { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
      iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
    iApply lwp_step_progress_get_lc_with_obls.
    iIntros (????) "I". iMod ("H" with "I") as "(%HS& (%&%& ((Tbs& Te& #Tei& #Es)& Ds)& H))".
    destruct HS as [_ HS]. iModIntro. iSplitR; first done.
    iExists Ψ, q. iFrame "Tbs". iSplitL "Ds".
    { iFrame "Tei". iApply (big_sepS_impl with "Ds"). iIntros "!>" (??) "((To& [Be Fe]& Te)& P& _)". iFrame. }
    iIntros (????) "A B Efs".
    iMod ("H" with "[//] [A Te] [B] [Efs]") as ">(I& H& Efs)"; iFrame; auto.
    - iCombine "Es B" as "B". iPoseProof (big_sepS_sep with "B") as "B".
      iApply (big_sepS_impl with "B"). iIntros "!>" (??) "(#Esx& To)". iFrame. auto.
    - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
    - iApply (lwp_cond_elim with "H Hc").
  Qed.

  Lemma lwp_lift_step_fupd_suspended s ς i E e1 Φ :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       ∃ π Ψ K,
         (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
          ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      tHas i Ψ 1 -∗
                      ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                         (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                      ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                      ALC (|={∅,E}=>
                             state_interp σ2 (Θ ∪ dom efs) κs ∗
                             lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
    { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
      iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
    iApply lwp_step_progress_get_lc_suspended_obls.
    iIntros (????) "I". iMod ("H" with "I") as "(%HS& (%& %& %& (%& (Tbs& Txi& #Tei& #Es)& (#Bep& #Fep)& Ps& Ws)& H))".
    destruct HS as [_ HS]. iModIntro. iSplitR; first done.
    iExists π, Ψ, K. iFrame "Tbs".
    iAssert ([∗ map] k↦'(x, ψ) ∈ K, otreeG_suspend k x i π ψ ∗ (oblG_elem k ∗ otreeG_elem k) ∗ (oblG_elem π ∗ otreeG_elem π) ∗ othreadG_elem i)%I with "[Ws]" as "#HK".
    { iApply (big_sepM_impl with "Ws"). iIntros (???) "!>". destruct x. iIntros "(W&S&A&B&C)". iFrame. }
    iSplitR "Hc Txi H".
    { iFrame "Tei Bep Fep". iSplit; first done. iSplitL "Ps".
      - iApply (big_sepS_impl with "Ps"). iIntros "!>" (??) "(P& Ex& _)". iFrame.
      - iApply (big_sepM_impl with "Ws"). iIntros "!>" (???). destruct x. iIntros "(W& S& (E1& E2)& _)". iFrame. }
    iIntros (????) "A B Efs".
    iMod ("H" with "[//] [A Txi] [B] [Efs]") as ">(I& H& Efs)"; iFrame; auto.
    - iDestruct "B" as "[[A B] | [A B]]".
      + iLeft. iSplitL "A".
        * iCombine "Es A" as "A". iPoseProof (big_sepS_sep with "A") as "A".
          iApply (big_sepS_impl with "A"). iIntros "!>" (??) "(#Esx& P)". iFrame. auto.
        * iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
          iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "(A& B)". iFrame.
      + iRight. iFrame "A Bep Fep". 
        iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
        iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "((S&E1&E2&E3)& (O&P))". iFrame.
        iPoseProof (big_sepS_elem_of_acc _ Ψ k with "Es") as "[$ _]". subst. by apply elem_of_dom.
    - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
    - iApply (lwp_cond_elim with "H Hc").
  Qed.

  Inductive get_lc := NoLc | GetLc | GetLcSus.

  Lemma lwp_lift_step_fupd_gen (glc : get_lc) s ς i E e1 Φ :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
       match glc with
       | NoLc =>
           (∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                         ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                         |={∅,E}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
       | GetLc =>
           (∃ Ψ q,
               (tHas i Ψ 1 ∗ [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
               ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                            tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                            ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                            ALC (|={∅,E}=>
                                   state_interp σ2 (Θ ∪ dom efs) κs ∗
                                   lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
       | GetLcSus =>
           (∃ π Ψ K,
               (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
                ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
               ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                            tHas i Ψ 1 -∗
                            ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                               (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                            ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                            ALC (|={∅,E}=>
                                   state_interp σ2 (Θ ∪ dom efs) κs ∗
                                   lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
       end)
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    destruct glc.
    - apply lwp_lift_step_fupd.
    - apply lwp_lift_step_fupd_lc.
    - apply lwp_lift_step_fupd_suspended.
  Qed.

  Lemma lwp_wait_obls s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ j Ψ π K,
         (⌜Ψ = dom K⌝ ∗ tHas j Ψ 1 ∗ obl π ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x j π ψ (1/2))) ∗
         (tHas j Ψ 1 -∗
          (([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x j π ψ (1/2)) ∨
             (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns j k (1/2) ∗ oFuel k ψ))) -∗
          |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_wait_obls.
    iIntros (???) "I". iMod ("H" with "I") as "(%&%&%&%& (%& (Tbs& Txi& #Tei& #Es)& (#Bep& #Fep)& Ws)& H)".
    iModIntro. iExists j, Ψ, π, K. iFrame "Tbs".
    iAssert ([∗ map] k↦'(x, ψ) ∈ K, otreeG_suspend k x j π ψ ∗ (oblG_elem k ∗ otreeG_elem k) ∗ (oblG_elem π ∗ otreeG_elem π) ∗ othreadG_elem j)%I with "[Ws]" as "#HK".
    { iApply (big_sepM_impl with "Ws"). iIntros (???) "!>". destruct x. iIntros "(W&S&A&B&C)". iFrame. }
    iSplitR "Txi H".
    { iFrame "Tei Bep Fep". iSplit; first done.
      iApply (big_sepM_impl with "Ws"). iIntros "!>" (???). destruct x. iIntros "(W& S& (E1& E2)& _)". iFrame. }
    iIntros "A B".
    iMod ("H" with "[A Txi] [B]") as "(I& H)"; iFrame; auto.
    iDestruct "B" as "[A | [A B]]".
    - iLeft. iCombine "HK A" as "A". iPoseProof (big_sepM_sep with "A") as "A".
      iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "(A& B)". iFrame.
    - iRight. iFrame "A Bep Fep".
      iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
      iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "((S&E1&E2&E3)& (O&P))". iFrame.
      iPoseProof (big_sepS_elem_of_acc _ Ψ k with "Es") as "[$ _]". subst. by apply elem_of_dom.
  Qed.

  Lemma lwp_alloc_obl s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ j Ψ q,
         tHas j Ψ q ∗
         (∃ T P α β, ∀ k,
            ⌜k ∉ Ψ⌝ -∗ tHas j ({[k]} ∪ Ψ) q -∗
            oGoal k T P -∗
            obl_bound k α -∗ obl_sc k α -∗ oFuel k β -∗
            othread_owns j k (1/2)%Qp -∗
          |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_alloc_obl.
    iIntros (???) "I". iMod ("H" with "I") as "(%&%&%& (Tbs& Txi& #Tei& #Es)& %&%&%&%& H)".
    iModIntro. iExists j, Ψ, q. iFrame "Tbs Tei". iExists T, P, α, β.
    iIntros (k) "% Tbs #Bek #Bgk #Btbk Btk Bpk Tok #Fek".
    iApply ("H" $! k with "[//] [Tbs Txi] [] [] [Btk] [Bpk] [Tok]"); auto.
    iFrame. iFrame "Tei". iApply big_sepS_union. 1: set_solver.
    rewrite big_sepS_singleton. auto.
  Qed.

  Lemma lwp_resolve_obl s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ j Ψ q k T P,
         tHas j Ψ q ∗ othread_owns j k (1/2)%Qp ∗ ⌜k ∈ Ψ⌝ ∗
         oGoal k T P ∗ ⌜T σ⌝ ∗ (▷ P) ∗
         (tHas j (Ψ ∖ {[k]}) q -∗ oDone k -∗
          |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_resolve_obl.
    iIntros (???) "I".
    iMod ("H" with "I") as "(%&%&%&%&%&%& (Tbs& Txi& #Tei& #Es)& (Tok& [#Bek #Fek]& #Tej)& %& (#Bgk& _)& %HT& P& H)".
    iModIntro. iExists j, Ψ, q, k, T, P. iFrame. iFrame "Tei Bek Bgk". iSplitR; first auto. iSplitR; first auto.
    iIntros "Tbs #Bdk".
    iApply ("H" with "[Tbs Txi] []"); auto.
    iFrame. iFrame "Tei". iPoseProof (big_sepS_delete _ _ k with "Es") as "[_ Es2]"; auto.
  Qed.

  Lemma lwp_suspend_obls_gen s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ π ℵ K,
         (obl_bound π ℵ ∗
          ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K,
             ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ othread_owns θ k (1/2)%Qp ∗ obl_sc k α ∗ obl_sc k β)) ∗
         (((oDone π ∗
            [∗ map] k ↦ '(θ, ψ, α, β) ∈ K, othread_owns θ k (1/2)%Qp ∗ obl_sc k α ∗ obl_sc k β) ∨
             ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K, ∃ x, obl_wait k x θ π ψ (1/2))) -∗
          |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_suspend_obls_gen.
    iIntros (???) "I".
    iMod ("H" with "I") as "(%&%&%& ((#Btbp& #Bep& #Fep)& M)& H)".
    iModIntro. iExists π, ℵ, K. iFrame "Bep Btbp".
    iAssert ([∗ map] k↦'(θ, _, α, β) ∈ K, ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ oblG_elem k ∗ otreeG_elem k ∗ othreadG_elem θ)%I with "[M]" as "#MM".
    { iApply (big_sepM_impl with "M"). iIntros (???). destruct x as [[[? ?] ?] ?].
      iIntros "!> (%& (A1& [A2 A3]& A4)& [B _]& [C _])". iFrame. done. }
    iSplitL "M".
    { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [[[? ?] ?] ?].
      iIntros "(%& (A1& [A2 A3]& A4)& [B _]& [C _])". iFrame. done. }
    iIntros "A". iApply "H". iDestruct "A" as "[ [A B] | A]".
    - iLeft. iFrame. iFrame "Bep Fep". iApply (big_sepM_impl with "B").
      iIntros "!>" (???). destruct x as [[[? ?] ?] ?]. iIntros "($&$&$)".
      iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(%& #Bek& #Fek& #Te)". auto.
    - iRight. iApply (big_sepM_impl with "A").
      iIntros "!>" (???). destruct x as [[[? ?] ?] ?]. iIntros "(%&$&$)".
      iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(%& #Bek& #Fek& #Te)". auto.
  Qed.

  Lemma lwp_progress_obls_gen s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ K,
         (([∗ map] k ↦ '(θ, ψ) ∈ K, othread_owns θ k (1/2)%Qp ∗ ∃ a, ⌜(Ord.O < a)%ord⌝ ∗ obl_sc k a) ∗
          (([∗ map] k ↦ '(θ, ψ) ∈ K, othread_owns θ k (1/2)%Qp ∗ oFuel k ψ) -∗
           |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_progress_obls_gen.
    iIntros (???) "I".
    iMod ("H" with "I") as "(%& M& H)".
    iAssert ([∗ map] k↦'(θ, _) ∈ K, oblG_elem k ∗ otreeG_elem k ∗ othreadG_elem θ)%I with "[M]" as "#MM".
    { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [? ?].
      iIntros "((_& A& B)& _)". iFrame. }
    iModIntro. iExists K.
    iSplitL "M".
    { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [? ?].
      iIntros "((To& He& Te)& (%& %& T& Be& Fe))". iFrame. auto. }
    iIntros "A". iApply "H".
    iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x as [? ?].
    iIntros "(O& P)". iFrame.
    iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(#Bek& #Fek& #Te)". auto.
  Qed.

  Lemma lwp_terminate s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ j,
         tHas j ∅ 1 ∗
         (tTerm j -∗
          |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs.
    iIntros "H". iApply ghost_step_elim. iApply ghost_step_terminate.
    iIntros (???) "I". iMod ("H" with "I") as "(%& (Tbs& Tx& #Te& _)& H)".
    iModIntro. iExists j. iFrame. iIntros "A". iApply "H". auto.
  Qed.

  Lemma lwp_done_acc s ς i E e Φ :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ k T P,
         oGoal k T P ∗ oDone k ∗
         ((▷ P) ={∅,E}=∗ (▷ P) ∗ state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
    ⊢ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs. iIntros "H". iApply ghost_step_elim. iApply ghost_step_done_acc.
    iIntros (???) "I". iMod ("H" with "I") as "(%&%&%& (Bg& Bg0)& (Bd& Bd0)& H)".
    iModIntro. iFrame.
  Qed.

  Lemma lwp_done_pers s ς i E e Φ k T P :
    Persistent P →
    oGoal k T P -∗ oDone k -∗ ((▷ P) -∗ lWP e @ s; ς; i; E {{ Φ }}) -∗
    lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    unfold_defs. iIntros (?) "[#Bg _] [#Bd _] H". iApply ghost_step_elim.
    iApply (ghost_step_done_pers with "Bg Bd H").
  Qed.

End liveness.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma lwp_lc_later_ord s ς i E e Φ :
  £ Ord.one -∗ (▷ lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "LC H". by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
Qed.
Lemma lwp_lc_later s ς i E e Φ :
  £n 1 -∗ (▷ lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
Proof. iApply lwp_lc_later_ord. Qed.
Lemma lwp_lc_laterN n s ς i E e Φ :
  £n n -∗ (▷^n lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
Qed.

Lemma lwp_lift_stuck ς i E Φ e :
  to_val e = None →
  (∀ Ω Θ σ κs,
     (ς ∗ osat Ω ∗ othread Θ ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗ state_interp σ Θ κs)
     ={E,∅}=∗
     ⌜ stuck i e σ Θ ⌝)
  ⊢ lWP e @ ς; i; E ?{{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H Hc" (?? σ κ κs) "Hσ".
  iMod ("H" with "[Hc Hσ]") as %[? Hirr]; first iFrame.
  iModIntro. iSplit; first done.
  iExists Ω1. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma lwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s ς i E Φ e1 C :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})
⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
  iApply lwp_lift_step_fupd. iIntros (Θ σ1 κ κs) "Hσ".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iPoseProof (HCC with "Hc Hσ") as "%HC".
  iSplit.
  { iPureIntro. split.
    - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
    - destruct s; auto. }
  iIntros (e2 σ2 efs ?) "Hefs".
  destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
  replace (Θ ∪ dom ∅) with Θ by set_solver.
  iMod "Hclose" as "_". iModIntro. rewrite big_sepM_empty.
  iFrame. iSplitL; last auto. iApply (lwp_cond_elim with "[H] Hc").
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_pure_step_no_fork_lc `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (|={E,E'}=>
     ∃ Ψ q,
     (tHas i Ψ 1 ∗
      [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
     (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
      ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
  iApply lwp_lift_step_fupd_lc. iIntros (Θ σ1 κ κs) "Hσ".
  iPoseProof (HCC with "Hc Hσ") as "%HC".
  iMod "H" as "(%&%& D& H)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit.
  { iPureIntro. split.
    - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
    - destruct s; auto. }
  iExists _, _. iFrame "D".
  iIntros (e2 σ2 efs ?) "Tbs Bos Efs".
  destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
  replace (Θ ∪ dom ∅) with Θ by set_solver.
  iMod ("H" with "Tbs Bos [//]") as "H".
  iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
  iSplitL; last auto. iApply (lwp_cond_elim with "H Hc").
Qed.

Lemma lwp_lift_pure_step_no_fork_suspended `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (|={E,E'}=>
     ∃ π Ψ K,
     (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
      ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
     (tHas i Ψ 1 -∗
      ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
         (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
      ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
  iApply lwp_lift_step_fupd_suspended. iIntros (Θ σ1 κ κs) "Hσ".
  iMod "H" as "(%&%&%& D& H)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iPoseProof (HCC with "Hc Hσ") as "%HC".
  iSplit.
  { iPureIntro. split.
    - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
    - destruct s; auto. }
  iExists _, _, _. iFrame "D". iIntros (e2 σ2 efs ?) "Tbs Bos Efs".
  destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
  replace (Θ ∪ dom ∅) with Θ by set_solver.
  iMod ("H" with "Tbs Bos [//]") as "H".
  iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
  iSplitL; last auto. iApply (lwp_cond_elim with "H Hc").
Qed.

Lemma lwp_lift_pure_step_no_fork_gen (glc : get_lc) `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (match glc with
   | NoLc =>
       (∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})
   | GetLc =>
       |={E,E'}=>
         (∃ Ψ q,
             (tHas i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
             (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
              ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
   | GetLcSus =>
       |={E,E'}=>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             (tHas i Ψ 1 -∗
              ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                 (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
              ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
   end)
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_pure_step_no_fork.
  - apply lwp_lift_pure_step_no_fork_lc.
  - apply lwp_lift_pure_step_no_fork_suspended.
Qed.

Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} ς i E Φ e :
  (∀ σ τ, stuck i e σ τ) →
  True ⊢ lWP e @ ς; i; E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply lwp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case (Hstuck inhabitant ∅).
  - iIntros (????) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

Lemma lwp_lift_atomic_step_fupd {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
     ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                  ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                  |={E2,E1}=>
     state_interp σ2 (Θ ∪ dom efs) κs ∗
     (ς -∗ from_option Φ False (to_val e2)) ∗
     [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (lwp_lift_step_fupd s _ i E1 e1); iIntros (Θ σ1 κ κs) "Hσ1".
  iMod ("H" with "Hσ1") as "(%& H)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; first auto. iIntros (????) "Hefs".
  iMod "Hclose" as "_". iMod ("H" with "[//] Hefs") as "H".
  iDestruct "H" as "(Hs&Hq&Hefs)". iFrame.
  iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply lwp_value; last eauto. by apply of_to_val.
Qed.

Lemma lwp_lift_atomic_step_fupd_lc {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
     ∃ Ψ q,
       (tHas i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
       ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                    ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                    ALC (|={E2,E1}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           (ς -∗ from_option Φ False (to_val e2)) ∗
                           [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (lwp_lift_step_fupd_lc s _ i E1 e1).
  iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; first auto.
  iDestruct "H" as "(%&%& D& H)". iExists _, _. iFrame "D".
  iIntros (????) "H1 H2 Hefs".
  iMod ("H" with "[//] H1 H2 Hefs") as "H".
  iMod "Hclose" as "_".
  iMod "H" as "(Hs&Hq&Hefs)". iFrame.
  iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply lwp_value; last eauto. by apply of_to_val.
Qed.

Lemma lwp_lift_atomic_step_fupd_suspended {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    tHas i Ψ 1 -∗
                    ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                       (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                    ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                    ALC (|={E2,E1}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           (ς -∗ from_option Φ False (to_val e2)) ∗
                           [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (lwp_lift_step_fupd_suspended s _ i E1 e1).
  iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; first auto.
  iDestruct "H" as "(%&%&%& D& H)". iExists _, _, _. iFrame "D".
  iIntros (????) "H1 H2 Hefs".
  iMod ("H" with "[//] H1 H2 Hefs") as "H".
  iMod "Hclose" as "_".
  iMod "H" as "(Hs&Hq&Hefs)". iFrame.
  iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply lwp_value; last eauto. by apply of_to_val.
Qed.

Lemma lwp_lift_atomic_step_fupd_gen (glc : get_lc) {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
     match glc with
     | NoLc =>
         (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                       ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                       |={E2,E1}=>
            state_interp σ2 (Θ ∪ dom efs) κs ∗
            (ς -∗ from_option Φ False (to_val e2)) ∗
            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
     | GetLc =>
         (∃ Ψ q,
             (tHas i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
             ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                          ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                          ALC (|={E2,E1}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 (ς -∗ from_option Φ False (to_val e2)) ∗
                                 [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     | GetLcSus =>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          tHas i Ψ 1 -∗
                          ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                             (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                          ([∗ set] j ∈ dom efs, tHas j ∅ 1) -∗
                          ALC (|={E2,E1}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 (ς -∗ from_option Φ False (to_val e2)) ∗
                                 [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     end)
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_atomic_step_fupd.
  - apply lwp_lift_atomic_step_fupd_lc.
  - apply lwp_lift_atomic_step_fupd_suspended.
Qed.

Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s ς i E Φ C} e1 e2 :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (lWP e2 @ s; ς; i; E {{ Φ }})
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork s _ i E); try done.
  { naive_solver. }
  iIntros "% % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
Qed.

Lemma lwp_lift_pure_det_step_no_fork_lc `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (|={E,E'}=>
     ∃ Ψ q,
     (tHas i Ψ 1 ∗
      [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
     (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
      ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork_lc s _ i E E'); try done.
  { naive_solver. }
  iMod "H" as "(%&%& $& H)". iModIntro.
  iIntros "H1 H2". iMod ("H" with "H1 H2") as ">H".
  iIntros "!> % % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
Qed.

Lemma lwp_lift_pure_det_step_no_fork_suspended `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (|={E,E'}=>
     ∃ π Ψ K,
     (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
      ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
     (tHas i Ψ 1 -∗
      ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
         (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
      ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork_suspended s _ i E E'); try done.
  { naive_solver. }
  iMod "H" as "(%&%&%& $& H)". iModIntro.
  iIntros "H1 H2". iMod ("H" with "H1 H2") as ">H".
  iModIntro. iIntros "% % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
Qed.

Lemma lwp_lift_pure_det_step_no_fork_gen (glc : get_lc) `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
  (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
  (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
  (match glc with
   | NoLc =>
       (lWP e2 @ s; ς; i; E {{ Φ }})
   | GetLc =>
       |={E,E'}=>
         (∃ Ψ q,
             (tHas i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
             (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
              ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
   | GetLcSus =>
       |={E,E'}=>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             (tHas i Ψ 1 -∗
              ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                 (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
              ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
   end)
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_pure_det_step_no_fork.
  - apply lwp_lift_pure_det_step_no_fork_lc.
  - apply lwp_lift_pure_det_step_no_fork_suspended.
Qed.

Class PureExecCond (C : thread_id → state Λ → Prop) ς (i : thread_id) :=
  pure_exec_cond : ∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝.

Lemma lwp_pure_step `{!Inhabited (state Λ)} s ς i E e1 e2 φ n Φ C :
  PureExec φ C n e1 e2 →
  φ →
  PureExecCond C ς i →
  (lWP e2 @ s; ς; i; E {{ Φ }})
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
  { by iApply "Hlwp". }
  iApply (lwp_lift_pure_det_step_no_fork).
  - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
  - eauto.
  - eauto.
  - by iApply "IH".
Qed.

Lemma lwp_pure_step_lc `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
  PureExec φ C n e1 e2 →
  φ →
  PureExecCond C ς i →
  (Nat.iter n (λ P, |={E,E'}=>
                 ∃ Ψ q,
                 (tHas i Ψ 1 ∗
                  [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
                 (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                  ALC (|={E',E}=> P)))
     (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
  { iMod tlc_zero as "Hz". by iApply "Hlwp". }
  iApply (lwp_lift_pure_det_step_no_fork_lc (E':=E')).
  - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
  - eauto.
  - eauto.
  - iDestruct "Hlwp" as ">(%&%& $& H)".
    iModIntro. iIntros "H1 H2". iDestruct ("H" with "H1 H2") as "H".
    iDestruct "H" as "(%& H)". iExists (Ord.S x). iIntros "LC".
    iPoseProof (tlc_succ with "LC") as "[LC LC2]".
    iMod ("H" with "LC2") as "H". iModIntro. iMod "H".
    iApply "IH". iModIntro.
    iRevert "H". iApply (bi.iter_modal_mono with "[-]").
    + iIntros (??) "PQ >H". iDestruct "H" as "(%&%& $& H)".
      iIntros "!> H1 H2". iMod ("H" with "H1 H2") as ">H". by iApply "PQ".
    + iIntros "H1 H2". iApply "H1". iApply tlc_succ_nat. iFrame.
Qed.

Lemma lwp_pure_step_suspended `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
  PureExec φ C n e1 e2 →
  φ →
  PureExecCond C ς i →
  (Nat.iter n (λ P, |={E,E'}=>
                 ∃ π Ψ K,
                 (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
                  ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                  ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
                 (tHas i Ψ 1 -∗
                  ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                    ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                     (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                  ALC (|={E',E}=> P)))
     (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
  { iMod tlc_zero as "Hz". by iApply "Hlwp". }
  iApply (lwp_lift_pure_det_step_no_fork_suspended (E':=E')).
  - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
  - eauto.
  - eauto.
  - iDestruct "Hlwp" as ">(%&%&%& $& H)".
    iModIntro. iIntros "H1 H2". iPoseProof ("H" with "H1 H2") as "H".
    iDestruct "H" as "(%& H)". iExists (Ord.S x). iIntros "LC".
    iPoseProof (tlc_succ with "LC") as "[LC LC2]".
    iMod ("H" with "LC2") as "H". iModIntro. iMod "H".
    iApply "IH". iModIntro.
    iRevert "H". iApply (bi.iter_modal_mono with "[-]").
    + iIntros (??) "PQ >H". iDestruct "H" as "(%&%&%& $& H)".
      iIntros "!> H1 H2". iMod ("H" with "H1 H2") as ">H". by iApply "PQ".
    + iIntros "H1 H2". iApply "H1". iApply tlc_succ_nat. iFrame.
Qed.

Lemma lwp_pure_step_gen (glc : get_lc) `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
  PureExec φ C n e1 e2 →
  φ →
  PureExecCond C ς i →
  (match glc with
   | NoLc =>
       (lWP e2 @ s; ς; i; E {{ Φ }})
   | GetLc =>
       (Nat.iter n (λ P, |={E,E'}=>
                      ∃ Ψ q,
                      (tHas i Ψ 1 ∗
                       [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ oFuel ρ Ord.one) ∗
                      (tHas i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                       ALC (|={E',E}=> P)))
          (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
   | GetLcSus =>
       (Nat.iter n (λ P, |={E,E'}=>
                      ∃ π Ψ K,
                      (⌜Ψ = dom K⌝ ∗ tHas i Ψ 1 ∗ obl π ∗
                       ([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                       ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
                      (tHas i Ψ 1 -∗
                       ((([∗ set] ρ ∈ Ψ, oFuel ρ Ord.one) ∗
                         ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                          (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ oFuel k ψ))) -∗
                       ALC (|={E',E}=> P)))
          (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
   end)
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_pure_step.
  - apply lwp_pure_step_lc.
  - apply lwp_pure_step_suspended.
Qed.

End lifting.
