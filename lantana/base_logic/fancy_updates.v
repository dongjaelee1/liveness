(** Fancy updates [|={E1,E2}=> P] on top of the relational update of transfinite later credits
    (instead of the basic update), and the rules for spending credits at fancy updates.
    Adapted from Transfinite Iris's [transfinite.base_logic.lib.fancy_updates]. *)

From stdpp Require Export coPset.
From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Export own.
From transfinite.base_logic.lib Require Import wsat.
From lantana.algebra Require Import ordinal_ucmra.
From lantana.base_logic Require Export later_credits.
From iris.prelude Require Import options.
Export wsatGS.

Class invGpreS `{SI : sidx} (Σ : gFunctors) : Set :=
  InvGpreS {
      #[local] invGpreS_wsat :: wsatGpreS Σ;
      #[local] invGpreS_lc :: tlcGpreS Σ;
    }.

(* Global, so that the credit lemmas (under [tlcGS]) and the lemmas of [invariants.v] (under
   [wsatGS]) apply under [invGS]. *)
Class invGS `{SI : sidx} (Σ : gFunctors) : Set := InvG {
  #[global] invGS_wsat :: wsatGS Σ;
  #[global] invGS_lc :: tlcGS Σ;
}.
Global Hint Mode invGS - - : typeclass_instances.
Global Hint Mode invGpreS - - : typeclass_instances.

Definition invΣ `{SI : sidx} : gFunctors :=
  #[wsatΣ; tlcΣ].
Global Instance subG_invΣ `{SI : sidx} {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.

Lemma invGS_alloc `{SI : sidx} `{!invGpreS Σ} :
  ⊢ |==> ∃ _ : invGS Σ, (∃ x : Ord.t, rupd_pred x) ∗ wsat ∗ ownE ⊤.
Proof.
  iIntros. iMod (wsat_alloc) as "(%& W& O)".
  iMod (auth_rupd_alloc OrdUR Ord.O) as "(%& R& _)".
  iExists (InvG _ _ H H0). iFrame. done.
Qed.

Local Definition uPred_fupd_def `{SI : sidx} `{!invGS Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 -∗ |==>r ◇ (wsat ∗ ownE E2 ∗ P))%I.
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {SI Σ _}.
Local Lemma uPred_fupd_unseal `{SI : sidx} `{!invGS Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma uPred_fupd_mixin `{SI : sidx} `{!invGS Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
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
Global Instance uPred_bi_fupd `{SI : sidx} `{!invGS Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd `{SI : sidx} `{!invGS Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

Lemma rupd_fupd `{SI : sidx} {Σ : gFunctors} `{!invGS Σ} P E:
  (|==>r P) -∗ |={E}=> P.
Proof.
  rewrite uPred_fupd_unseal /uPred_fupd_def. iIntros "Hupd Hwsat".
  by iMod "Hupd" as "$".
Qed.

(** * Later credits at fancy updates *)

(** Typical use: [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP"]. *)
Lemma lc_fupd_elim_later_ord `{SI : sidx} `{!invGS Σ} E P :
   £ 1%ord -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iIntros "[$ $]". iApply (tlc_later with "[$Hf Hupd]").
  iNext. by iModIntro.
Qed.

Lemma lc_fupd_elim_later `{SI : sidx} `{!invGS Σ} E P :
   £n 1 -∗ (▷ P) -∗ |={E}=> P.
Proof. rewrite tlc_one_nat. apply lc_fupd_elim_later_ord. Qed.

(** Typical use on a fancy-update goal: [iApply (lc_fupd_add_later with "Hcredit")]. *)
Lemma lc_fupd_add_later_ord `{SI : sidx} `{!invGS Σ} E1 E2 P :
  £ 1%ord -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later_ord with "Hf Hupd").
Qed.

Lemma lc_fupd_add_later `{SI : sidx} `{!invGS Σ} E1 E2 P :
  £n 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof. rewrite tlc_one_nat. apply lc_fupd_add_later_ord. Qed.

Lemma lc_fupd_add_laterN `{SI : sidx} `{!invGS Σ} E1 E2 P n :
  £ (Ord.from_nat n) -∗ (▷^n |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iInduction n as [|n] "IH"; first done.
  rewrite tlc_succ_nat. iDestruct "Hf" as "[H1 Hf]".
  iApply (lc_fupd_add_later with "H1"); iNext.
  iApply ("IH" with "[$] [$]").
Qed.
