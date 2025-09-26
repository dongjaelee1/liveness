(** From the artifact of
    Later Credits: Resourceful Reasoning for the Later Modality
    by Spies et al. 2022
 *)

From stdpp Require Export coPset.
From iris.prelude Require Import options.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Export own.
From transfinite.base_logic.lib Require Import wsat.
From liris.base_logic Require Export later_credits.
(* From liris.base_logic Require Export relational_updates. *)
Export wsatGS.
Import uPred.
Import le_upd_if.


Class invGpreS `{SI : indexT} (Σ : gFunctors) : Set := InvGpreS {
  #[local] invGpreS_wsat :: wsatGpreS Σ;
  #[local] invGpreS_lc :: lcGpreS Σ;
}.

(* [invGS_lc] needs to be global in order to enable the use of lemmas like
[lc_split] that require [lcGS], and not [invGS]. [invGS_wsat] also needs to be
global as the lemmas in [invariants.v] require it. *)
Class invGS_gen `{SI : indexT} (hlc : has_lc) (Σ : gFunctors) : Set := InvG {
  #[global] invGS_wsat :: wsatGS Σ;
  #[global] invGS_lc :: lcGS Σ;
}.
Global Hint Mode invGS_gen - - - : typeclass_instances.
Global Hint Mode invGpreS - - : typeclass_instances.

Notation invGS := (invGS_gen HasLc).

Definition invΣ `{SI : indexT} : gFunctors :=
  #[wsatΣ; lcΣ].
Global Instance subG_invΣ `{SI : indexT} {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.


Definition fupd_def {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 -∗ |==>r ◇ (wsat ∗ ownE E2 ∗ P))%I.
Definition fupd_aux : seal (@fupd_def). Proof. by eexists. Qed.
Definition fupd' := fupd_aux.(unseal).
Global Arguments fupd' {SI Σ X _ _}.
Lemma fupd_eq {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} : @fupd _ fupd' = fupd_def.
Proof. rewrite -fupd_aux.(seal_eq) //. Qed.

Lemma fupd_mixin {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} : BiFUpdMixin (iPropI Σ) fupd'.
Proof.
  split.
  - rewrite fupd_eq. solve_proper.
  - intros E1 E2 P (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite fupd_eq /fupd_def ownE_op //.
    by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>".
  - rewrite fupd_eq /fupd_def.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite fupd_eq. iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite fupd_eq /fupd_def. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite fupd_eq /fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite fupd_eq /fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance fupd_bi_fupd {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} : BiFUpd (iPropI Σ) :=
  {| bi_fupd_mixin := fupd_mixin |}.

Global Instance fupd_bi_bupd_fupd {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X}: BiBUpdFUpd (iPropI Σ).
Proof. rewrite /BiBUpdFUpd fupd_eq. by iIntros (E P) ">? [$ $] !> !>". Qed.


Lemma fupd_step {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} P E1 E2:
(∀ x, rupd_pred x -∗ |==> (∃ y, ⌜tc rupd_rel y x⌝ ∗ rupd_pred y ∗ ▷ |={E1, E2}=> P)) -∗ |={E1, E2}=> P.
Proof.
  rewrite fupd_eq /fupd_def. iIntros "Hupd Hwsat".
  rewrite /bupd /bi_bupd_bupd; simpl.
  iApply (rupd_step); iIntros (x) "Hpr".
  iSpecialize ("Hupd" with "Hpr").
  pose (@uPred_bi_bupd SI (iResUR Σ)).
  iApply (bupd_wand_l with "[$Hupd Hwsat]").
  iIntros "Hupd". iDestruct "Hupd" as (y Htc) "[Hpr Hupd]".
  iExists y. iFrame. iSplit; first done.
  iNext.
  by iApply "Hupd".
Qed.


Lemma rupd_fupd {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{!rupdG Σ X} P E:
  (|==>r P) -∗ |={E}=> P.
Proof.
  rewrite fupd_eq /fupd_def. iIntros "Hupd Hwsat".
  by iMod "Hupd" as "$".
Qed.


(* there is a canonical satisfiability instance for every notion of satisfiable *)
Definition sat_at {SI} {Σ: gFunctors SI} {X} `{!invG Σ} `{rG: !rupdG Σ X} (sat: iProp Σ → Prop) E := (sat_frame sat (wsat ∗ ownE E)%I).
Global Instance: Params (@sat_at) 7 := {}.

Section canonical_sat_at.
  Context {SI} {Σ: gFunctors SI} `{!invG Σ} `{rG: !rupdG Σ X} {sat: iProp Σ → Prop} `{Sat: !Satisfiable sat} `{RUpd: !SatisfiableRUpd sat} `{Later: !SatisfiableLater sat}.

  Global Instance sat_at_satisfiable_at_fupd:
    SatisfiableAtFupd (sat_at sat).
  Proof using Later RUpd Sat.
    split; rewrite /sat_at /sat_frame; intros E1 E2 P Hs; eapply sat_later, sat_rupd, sat_mono, Hs.
    iIntros "((W & O) & P)". rewrite fupd_eq /fupd_def.
    iSpecialize ("P" with "[W O]"); first by iFrame.
    iMod "P". iModIntro. iApply except_0_later.
    iMod "P" as "($ & $ & $)".
  Qed.
End canonical_sat_at.
