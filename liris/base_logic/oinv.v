From iris.algebra Require Import gmap_view gset coPset reservation_map dfrac_agree mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Import bank.
From liris.algebra Require Export ordinal_wfocm layer.
From liris.base_logic Require Export osat invariants.

(* Each obl has this variant as an invariant: P until (Q and always R). *)
Definition oblG_variant `{SI : indexT} `{!osatGS.osatGS Σ}
  (k : oid) (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  (oblG_assigned k false q ∗ P) ∨
    ((oblG_assigned k true q ∨ oblG_fulfilled k) ∗ Q).

Definition oblG_inv `{SI : indexT} `{!osatGS.osatGS Σ} `{!invGS Σ}
  (N : namespace) (k : oid) (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  inv N (oblG_variant k q P Q).

(** Properties *)
Section oinv.
  Context `{SI : indexT} `{!osatGS.osatGS Σ} `{!invGS Σ} `{OMF : !ord_mono_fun_class}.

  (** Instances *)
  (* Variant *)
  Global Instance oblG_inv_contractive_1 N k q Q : Contractive (λ P, oblG_inv N k q P Q).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.
  Global Instance oblG_inv_contractive_2 N k q P : Contractive (λ Q, oblG_inv N k q P Q).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.

  Global Instance oblG_inv_persistent N k q P Q : Persistent (oblG_inv N k q P Q).
  Proof. apply _. Qed.

  (** oblG_inv rules *)
  Lemma oblG_inv_acc E N k q P Q :
    ↑N ⊆ E →
    oblG_inv N k q P Q ={E,E ∖ ↑N}=∗
    ▷ oblG_variant k q P Q ∗
    (▷ oblG_variant k q P Q ={E ∖ ↑N,E}=∗ True).
  Proof. iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto. Qed.

  Lemma oblG_inv_acc_assigned E N k q1 P Q :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q
    ={E,E ∖ ↑N}=∗ ∀ b q2,
    oblG_assigned k b q2 -∗
    ((▷ (oblG_assigned k b q2 ∗
         if b then (oblG_assigned k true q1 ∗ Q) else (oblG_assigned k false q1 ∗ P))) ∗
     (▷ oblG_variant k q1 P Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#GU". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iIntros (b ?) "Ga". destruct b.
      + iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[Ga' _]".
        iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
      + iFrame.
    - iModIntro. iIntros (b ?) "Ga". destruct b.
      + iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "([Ga2 | #Gf]& HQ)".
        * iFrame.
        * iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.        
      + iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[[Ga2 | #Gf] _]".
        * iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
        * iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
  Qed.

  Lemma oblG_inv_acc_fulfilled E N k q P Q :
    ↑N ⊆ E →
    oblG_inv N k q P Q
    ={E,E ∖ ↑N}=∗ oblG_fulfilled k -∗
    ((▷ ((Q))) ∗
     (▷ oblG_variant k q P Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#GU". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iIntros "#Gf". iSplitR "ACC"; last done.
      iNext. iDestruct "H" as "[H _]". iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    - iModIntro. iIntros "#Gf". iSplitR "ACC"; iFrame. iNext. iDestruct "H" as "[_ $]".
  Qed.

  Lemma oblG_inv_acc_fulfilled_persistent E N k q P Q :
    Persistent Q →
    ↑N ⊆ E →
    oblG_inv N k q P Q -∗ oblG_fulfilled k ={E}[E ∖ ↑N]▷=∗ Q.
  Proof.
    iIntros (PR HE) "#GU #Gf". iMod (oblG_inv_acc_fulfilled with "GU Gf") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "#H". iFrame "H". iApply "ACC". iRight. eauto.
  Qed.

  (* Allocations *)
  Lemma oblG_inv_alloc_assigned_false E N k q P Q :
    (▷ (oblG_assigned k false q ∗ P)) ={E}=∗ oblG_inv N k q P Q.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma oblG_inv_alloc_assigned_true E N k q P Q :
    (▷ (oblG_assigned k true q ∗ Q)) ={E}=∗ oblG_inv N k q P Q.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$)". Qed.
  Lemma oblG_inv_alloc_fulfilled E N k q P Q :
    (▷ (oblG_fulfilled k ∗ Q)) ={E}=∗ oblG_inv N k q P Q.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$)". Qed.

End oinv.
