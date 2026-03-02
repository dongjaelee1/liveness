From iris.algebra Require Import gmap_view gset coPset reservation_map dfrac_agree mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Import bank.
From liris.algebra Require Export ordinal_wfocm layer.
From liris.base_logic Require Export osat invariants.

(* Each obligation has this variant as an invariant: P until (Q and always R). *)
Definition oblG_variant `{SI : indexT} `{!osatGS.osatGS Σ}
  (k : oid) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  (oblG_assigned k q ∗ P) ∨ (oblG_fulfilled k ∗ (Q ∨ oblG_expired k) ∗ R).

Definition oblG_inv `{SI : indexT} `{!osatGS.osatGS Σ} `{!invGS Σ}
  (N : namespace) (k : oid) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  inv N (oblG_variant k q P Q R).

(** Properties *)
Section oinv.
  Context `{SI : indexT} `{!osatGS.osatGS Σ} `{!invGS Σ} `{OMF : !ord_mono_fun_class}.

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

  Lemma oblG_inv_acc_assigned E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_assigned k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_assigned k q2 ∗ (oblG_assigned k q1 ∗ P))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[#Gf _]".
      iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
  Qed.

  Lemma oblG_inv_acc_fulfilled E N k q P Q R :
    ↑N ⊆ E →
    oblG_inv N k q P Q R -∗ oblG_fulfilled k
    ={E,E ∖ ↑N}=∗
    (▷ ((Q ∨ oblG_expired k) ∗ R)) ∗
    (▷ oblG_variant k q P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU #Gf". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC"; last done.
      iNext. iDestruct "H" as "[H _]". iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    - iModIntro. iSplitR "ACC"; iFrame. iNext. iDestruct "H" as "[_ $]".
  Qed.

  Lemma oblG_inv_acc_alive E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_alive k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_alive k q2 ∗ ((oblG_assigned k q1 ∗ P) ∨ (oblG_fulfilled k ∗ Q ∗ R)))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "(#Gf& [HQ | #Gx]& HR)".
      { iFrame. iRight. iFrame. eauto. }
      { iPoseProof (oblG_alive_expired_false with "[$]") as "%". done. }
  Qed.

  Lemma oblG_inv_acc_fulfilled_alive E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_fulfilled k -∗ oblG_alive k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_alive k q2 ∗ (Q ∗ R))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU #Gf GV". iMod (oblG_inv_acc_fulfilled with "GU Gf") as "[H ACC]"; first auto.
    iModIntro. iSplitR "ACC"; last done. iNext. iDestruct "H" as "[[$ | #Gx] $]"; first eauto.
    iPoseProof (oblG_alive_expired_false with "[$]") as "%". done.
  Qed.

  (* Allocations *)
  Lemma oblG_inv_alloc_assigned E N k q P Q R :
    (▷ (oblG_assigned k q ∗ P)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma oblG_inv_alloc_fulfilled E N k q P Q R :
    (▷ (oblG_fulfilled k ∗ Q ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.
  Lemma oblG_inv_alloc_expired E N k q P Q R :
    (▷ (oblG_fulfilled k ∗ oblG_expired k ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.

  (** Rules for oblG_inv and osat *)
  Lemma osat_variant_fulfill k q0 q1 E N P Q R :
    (q0 + q1 = 1/2 + 1/2/2)%Qp →
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R ∗ oblG_assigned k q1
    ⊢ |={E,E ∖ ↑N}=>
          (▷ (oblG_assigned k (1/2 + 1/2/2)%Qp ∗ P)) ∗
          (∀ Ω t, (osat Ω ∗ oblG_elem k ∗ oblG_assigned k (1/2 + 1/2/2)%Qp ∗ oblG_owner k t (1/2 + 1/2/2)%Qp) ==∗
                osat (<[k:=(obligation_fulfilled)]>Ω) ∗ oblG_fulfilled k) ∗
          ((▷ (oblG_fulfilled k ∗ Q ∗ R)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (Hq HE) "(#Gvar& Ga)".
    iMod (oblG_inv_acc_assigned with "Gvar Ga") as "[Ga ACC]". 1: auto.
    iModIntro. iSplitL "Ga".
    { iNext. iDestruct "Ga" as "(H1&H2&$)". iCombine "H2 H1" as "H". rewrite Hq. iFrame. }
    iSplitR "ACC".
    { iIntros "% % H". iMod (osat_fulfill with "H") as "($& $& _)". done. }
    iIntros "H". iApply "ACC". iNext. iRight. iDestruct "H" as "($&$&$)".
  Qed.

  Lemma osat_variant_expire k q0 E N P Q R :
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R ∗ oblG_fulfilled k ∗ oblG_alive k (1/2 + 1/2/2)%Qp
    ⊢ |={E,E ∖ ↑N}=>
          (▷ (oblG_alive k (1/2 + 1/2/2)%Qp ∗ Q ∗ R)) ∗
          (∀ Ω, (osat Ω ∗ oblG_elem k ∗ oblG_alive k (1/2 + 1/2/2)%Qp) ==∗
                osat (<[k:=(obligation_expired)]>Ω) ∗ oblG_expired k) ∗
          ((▷ (oblG_expired k ∗ R)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "(#Gvar& #Gf& Ga)".
    iMod (oblG_inv_acc_fulfilled_alive with "Gvar Gf Ga") as "[$ ACC]". 1: auto.
    iModIntro. iSplitR "ACC".
    { iIntros "% (H1& H2& H3)". iMod (osat_expire with "[$H1 $H2 $H3 $Gf]") as "($& $& _)". done. }
    iIntros "H". iApply "ACC". iNext. iRight. iDestruct "H" as "($&$)". auto.
  Qed.

End oinv.
