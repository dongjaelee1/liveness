(** * Invariants of obligations

    [oblG_inv N k q P Q R]: an invariant that holds [P] or [Q] while the obligation [k] is
    assigned (depending on its flag) and [R] once it is discharged. *)

From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From lantana.algebra Require Export ordinal_wfocm layer.
From lantana.base_logic Require Export osat invariants.

(* The three states of the invariant. *)
Definition oblG_variant `{SI : sidx} `{!osatGS.osatGS Σ}
  (k : oid) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  (oblG_assigned k false q ∗ P) ∨
    (oblG_assigned k true q ∗ Q) ∨
    (oblG_discharged k ∗ R).

Definition oblG_inv `{SI : sidx} `{!osatGS.osatGS Σ} `{!invGS Σ}
  (N : namespace) (k : oid) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  inv N (oblG_variant k q P Q R).

(** Properties *)
Section oinv.
  Context `{SI : sidx} `{!osatGS.osatGS Σ} `{!invGS Σ} `{OMF : !ord_mono_fun_class}.

  (** Instances *)
  (* Variant *)
  Global Instance oblG_inv_contractive_1 N k q Q R : Contractive (λ P, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.
  Global Instance oblG_inv_contractive_2 N k q P R : Contractive (λ Q, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.
  Global Instance oblG_inv_contractive_3 N k q P Q : Contractive (λ R, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.

  Global Instance oblG_inv_persistent N k q P Q R : Persistent (oblG_inv N k q P Q R).
  Proof. apply _. Qed.

  (** oblG_inv rules *)
  Lemma oblG_inv_acc E N k q P Q R :
    ↑N ⊆ E →
    oblG_inv N k q P Q R ={E,E ∖ ↑N}=∗
    ▷ oblG_variant k q P Q R ∗
    (▷ oblG_variant k q P Q R ={E ∖ ↑N,E}=∗ True).
  Proof. iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto. Qed.

  Lemma oblG_inv_acc_assigned E N k q1 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R
    ={E,E ∖ ↑N}=∗ ∀ b q2,
    oblG_assigned k b q2 -∗
    ((▷ (oblG_assigned k b q2 ∗
         if b then (oblG_assigned k true q1 ∗ Q) else (oblG_assigned k false q1 ∗ P))) ∗
     (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#GU". iMod (oblG_inv_acc with "GU") as "[H ACC]"; first auto.
    iIntros "!> %% Ga". iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[H | [H | H]]".
    - iDestruct "H" as "[Ga2 HP]". iPoseProof (oblG_assigned_agree with "[$Ga $Ga2]") as "%".
      destruct H0 as [? _]. subst. iFrame.
    - iDestruct "H" as "[Ga2 HP]". iPoseProof (oblG_assigned_agree with "[$Ga $Ga2]") as "%".
      destruct H0 as [? _]. subst. iFrame.
    - iDestruct "H" as "[Gf _]". iPoseProof (oblG_assigned_discharged_false with "[$]") as "%". done.
  Qed.

  Lemma oblG_inv_acc_discharged E N k q P Q R :
    ↑N ⊆ E →
    oblG_inv N k q P Q R
    ={E,E ∖ ↑N}=∗ oblG_discharged k -∗
    ((▷ (R)) ∗
     (▷ oblG_variant k q P Q R ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#GU". iMod (oblG_inv_acc with "GU") as "[H ACC]"; first auto.
    iIntros "!> #Gf". iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[H | [H | H]]".
    - iDestruct "H" as "[Ga2 HP]". iPoseProof (oblG_assigned_discharged_false with "[$]") as "%". done.
    - iDestruct "H" as "[Ga2 HP]". iPoseProof (oblG_assigned_discharged_false with "[$]") as "%". done.
    - iDestruct "H" as "[_ $]".
  Qed.

  Lemma oblG_inv_acc_discharged_persistent E N k q P Q R :
    Persistent R →
    ↑N ⊆ E →
    oblG_inv N k q P Q R -∗ oblG_discharged k ={E}[E ∖ ↑N]▷=∗ R.
  Proof.
    iIntros (PR HE) "#GU #Gf". iMod (oblG_inv_acc_discharged with "GU Gf") as "[H ACC]". 1: auto.
    iModIntro. iNext. iPoseProof "H" as "#H". iFrame "H". iApply "ACC". iRight. iRight. eauto.
  Qed.

  (* Allocations *)
  Lemma oblG_inv_alloc_assigned_false E N k q P Q R :
    (▷ (oblG_assigned k false q ∗ P)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma oblG_inv_alloc_assigned_true E N k q P Q R :
    (▷ (oblG_assigned k true q ∗ Q )) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iLeft. iDestruct "H" as "($&$)". Qed.
  Lemma oblG_inv_alloc_discharged E N k q P Q R :
    (▷ (oblG_discharged k ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iRight. iDestruct "H" as "($&$)". Qed.

End oinv.
