(** Transfinite later credit version *)

From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
(* From transfinite.stepindex Require Import ordinal_arith. *)
(* From transfinite.algebra Require Import ordinals. *)
From transfinite.base_logic.lib Require Export own.
From transfinite.base_logic.lib Require Import wsat.
From lantana.algebra Require Import ordinal_ucmra.
From lantana.base_logic Require Export later_credits.
From iris.prelude Require Import options.
Export wsatGS.
Import uPred.

Class invGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
  InvGpreS {
      #[local] invGpreS_wsat :: wsatGpreS Σ;
      #[local] invGpreS_lc :: tlcGpreS Σ;
    }.

(* [invGS_lc] needs to be global in order to enable the use of lemmas like
[lc_split] that require [lcGS], and not [invGS]. [invGS_wsat] also needs to be
global as the lemmas in [invariants.v] require it. *)
Class invGS `{SI : indexT} (Σ : gFunctors) : Set := InvG {
  #[global] invGS_wsat :: wsatGS Σ;
  #[global] invGS_lc :: tlcGS Σ;
}.
Global Hint Mode invGS - - : typeclass_instances.
Global Hint Mode invGpreS - - : typeclass_instances.

Definition invΣ `{SI : indexT} : gFunctors :=
  #[wsatΣ; tlcΣ].
Global Instance subG_invΣ `{SI : indexT} {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.

(* Allocation of invGS. *)
Lemma invGS_alloc `{SI : indexT} `{!invGpreS Σ} :
  ⊢ |==> ∃ _ : invGS Σ, (∃ x : Ord.t, rupd_pred x) ∗ wsat ∗ ownE ⊤.
Proof.
  iIntros. iMod (wsat_alloc) as "(%& W& O)".
  iMod (auth_rupd_alloc OrdUR Ord.O) as "(%& R& _)".
  iExists (InvG _ _ H H0). iFrame. done.
Qed.

Local Definition uPred_fupd_def `{SI : indexT} `{!invGS Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 -∗ |==>r ◇ (wsat ∗ ownE E2 ∗ P))%I.
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {SI Σ _}.
Local Lemma uPred_fupd_unseal `{SI : indexT} `{!invGS Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma uPred_fupd_mixin `{SI : indexT} `{!invGS Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>".
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_unseal /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance uPred_bi_fupd `{SI : indexT} `{!invGS Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd `{SI : indexT} `{!invGS Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.


(** Additional lemmas *)
Lemma fupd_step `{SI : indexT} {Σ : gFunctors} `{!invGS Σ} P E1 E2:
  (∀ (x : Ord.t), ●£ x -∗ |==> (∃ y, ⌜(y < x)%ord⌝ ∗ ●£ y ∗ ▷ |={E1, E2}=> P)) -∗ |={E1, E2}=> P.
Proof.
  rewrite uPred_fupd_unseal /uPred_fupd_def. iIntros "Hupd Hwsat".
  rewrite /bupd /bi_bupd_bupd; simpl.
  iApply rupd_step; iIntros (x) "Hpr".
  iSpecialize ("Hupd" with "Hpr").
  pose (@uPred_bi_bupd SI (iResUR Σ)).
  iApply (bupd_wand_l with "[Hupd Hwsat]"). iSplitR "Hupd"; last iApply "Hupd".
  iIntros "Hupd". iDestruct "Hupd" as (y Htc) "[Hpr Hupd]".
  iExists y. iFrame. iSplit.
  { iPureIntro. by econstructor. }
  iNext. by iApply "Hupd".
Qed.

Lemma rupd_fupd `{SI : indexT} {Σ : gFunctors} `{!invGS Σ} P E:
  (|==>r P) -∗ |={E}=> P.
Proof.
  rewrite uPred_fupd_unseal /uPred_fupd_def. iIntros "Hupd Hwsat".
  by iMod "Hupd" as "$".
Qed.


(** Later credits *)

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
  This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
  where ["Hcredit"] is a credit available in the context and ["HP"] is the
  assumption from which a later should be stripped. *)
Lemma lc_fupd_elim_later_ord `{SI : indexT} `{!invGS Σ} E P :
   £ 1%ord -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iIntros "[$ $]". iApply (tlc_later with "[$Hf Hupd]").
  iNext. by iModIntro.
Qed.

Lemma lc_fupd_elim_later `{SI : indexT} `{!invGS Σ} E P :
   £n 1 -∗ (▷ P) -∗ |={E}=> P.
Proof. rewrite tlc_one_nat. apply lc_fupd_elim_later_ord. Qed.

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_fupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_fupd_add_later_ord `{SI : indexT} `{!invGS Σ} E1 E2 P :
  £ 1%ord -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later_ord with "Hf Hupd").
Qed.

Lemma lc_fupd_add_later `{SI : indexT} `{!invGS Σ} E1 E2 P :
  £n 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof. rewrite tlc_one_nat. apply lc_fupd_add_later_ord. Qed.

(** Similar to above, but here we are adding [n] laters. *)
Lemma lc_fupd_add_laterN `{SI : indexT} `{!invGS Σ} E1 E2 P n :
  £ (Ord.from_nat n) -∗ (▷^n |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iInduction n as [|n] "IH"; first done.
  rewrite tlc_succ_nat. iDestruct "Hf" as "[H1 Hf]".
  iApply (lc_fupd_add_later with "H1"); iNext.
  iApply ("IH" with "[$] [$]").
Qed.
