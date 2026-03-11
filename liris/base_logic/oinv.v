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
  (k : oid) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  (oblG_assigned k false q ∗ P) ∨
    ((oblG_assigned k true q ∨ oblG_fulfilled k) ∗ (Q ∨ oblG_expired k) ∗ R).

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

  Lemma oblG_inv_acc_assigned_false E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_assigned k false q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_assigned k false q2 ∗ (oblG_assigned k false q1 ∗ P))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[[Ga2 | #Gf] _]".
      + iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
      + iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
  Qed.

  Lemma oblG_inv_acc_assigned_true E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_assigned k true q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_assigned k true q2 ∗ (oblG_assigned k true q1 ∗ Q ∗ R))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[Ga _]".
      iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "([Ga2 | #Gf]& HQ& HR)".
      + iDestruct "HQ" as "[HQ | #GX]"; first iFrame. iPoseProof (oblG_assigned_expired_false with "[$]") as "%". done.
      + iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
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

  Lemma oblG_inv_acc_fulfilled_persistent E N k q P Q R :
    Persistent R →
    ↑N ⊆ E →
    oblG_inv N k q P Q R -∗ oblG_fulfilled k ={E}[E ∖ ↑N]▷=∗ R.
  Proof.
    iIntros (PR HE) "#GU #Gf". iMod (oblG_inv_acc_fulfilled with "GU Gf") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "[H #HR]". iFrame "HR". iApply "ACC".
    iRight. iFrame. eauto.
  Qed.

  Lemma oblG_inv_acc_alive E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_alive k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_alive k q2 ∗ ((oblG_assigned k false q1 ∗ P) ∨ ((oblG_assigned k true q1 ∨ oblG_fulfilled k) ∗ Q ∗ R)))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_inv_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "(Gf& [HQ | #Gx]& HR)".
      { iFrame. iRight. iFrame. }
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
  Lemma oblG_inv_alloc_assigned_false E N k q P Q R :
    (▷ (oblG_assigned k false q ∗ P)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma oblG_inv_alloc_assigned_true E N k q P Q R :
    (▷ (oblG_assigned k true q ∗ Q ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.
  Lemma oblG_inv_alloc_fulfilled E N k q P Q R :
    (▷ (oblG_fulfilled k ∗ Q ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.
  Lemma oblG_inv_alloc_expired E N k q P Q R :
    (▷ (oblG_expired k ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof.
    iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "(#Gx&$)".
    iPoseProof (oblG_expired_fulfilled with "Gx") as "#Gf". iSplitR; by iRight.
  Qed.

  (** Rules for oblG_inv and osat *)
  Lemma osat_variant_assigned_true k q0 E N P Q R :
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R
    ⊢ |={E,E ∖ ↑N}=>
          ∀ q1, (⌜(q0 + q1 = 1/2 + 1/2/2)%Qp⌝) → (oblG_assigned k false q1) -∗
                ((▷ (oblG_assigned k false (1/2 + 1/2/2)%Qp ∗ P)) ∗
                 (∀ Ω b, (osat Ω ∗ oblG_elem k ∗ oblG_assigned k b (1/2 + 1/2/2)%Qp) ==∗
                         osat Ω ∗ oblG_assigned k true (1/2 + 1/2/2)%Qp) ∗
                 ((▷ (oblG_assigned k true q0 ∗ Q ∗ R)) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#Gvar".
    iMod (oblG_inv_acc with "Gvar") as "[Gv ACC]". 1: auto.
    iModIntro. iIntros (q1 Hq) "Ga". iSplitL "Gv Ga".
    { iNext. iDestruct "Gv" as "[(Ga2& HP) | ([Ga2 | #Gf]& _)]".
      - iCombine "Ga2 Ga" as "Ga". rewrite Hq. iFrame.
      - iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
      - iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done. }
    iSplitR "ACC".
    { iIntros "% % H". iMod (osat_assigned_to_true with "H") as "($& $)". done. }
    iIntros "H". iApply "ACC". iNext. iRight. iDestruct "H" as "($&$&$)".
  Qed.

  Lemma osat_variant_fulfill k q0 E N P Q R :
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R
    ⊢ |={E,E ∖ ↑N}=>
          ∀ q1, ⌜(q0 + q1 = 1/2 + 1/2/2)%Qp⌝ → oblG_assigned k true q1 -∗
                ((▷ (oblG_assigned k true (1/2 + 1/2/2)%Qp ∗ Q ∗ R)) ∗
                 (∀ Ω b t, (osat Ω ∗ oblG_elem k ∗ oblG_assigned k b (1/2 + 1/2/2)%Qp ∗ oblG_owner k t (1/2 + 1/2/2)%Qp) ==∗
                           osat (<[k:=(obl_fulfilled)]>Ω) ∗ oblG_fulfilled k) ∗
                 ((▷ (oblG_fulfilled k ∗ Q ∗ R)) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#Gvar".
    iMod (oblG_inv_acc with "Gvar") as "[Gv ACC]". 1: auto.
    iModIntro. iIntros (q1 Hq) "Ga". iSplitL "Gv Ga".
    { iNext. iDestruct "Gv" as "[(Ga2& HP) | ([Ga2 | #Gf]& HQR)]".
      - iPoseProof (oblG_assigned_agree with "[$]") as "%". by destruct H0.
      - iCombine "Ga2 Ga" as "Ga". rewrite Hq. iDestruct "HQR" as "([HQ | #GX]& HR)"; first iFrame.
        iPoseProof (oblG_assigned_expired_false with "[$]") as "%". done.
      - iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done. }
    iSplitR "ACC".
    { iIntros "%%% H". iMod (osat_fulfill with "H") as "($& $& _)". done. }
    iIntros "H". iApply "ACC". iNext. iRight. iDestruct "H" as "($&$&$)".
  Qed.

  Lemma osat_variant_expire k q0 E N P Q R :
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R
    ⊢ |={E,E ∖ ↑N}=>
          oblG_fulfilled k -∗ oblG_alive k (1/2 + 1/2/2)%Qp -∗
          ((▷ (oblG_alive k (1/2 + 1/2/2)%Qp ∗ Q ∗ R)) ∗
           (∀ Ω, (osat Ω ∗ oblG_elem k ∗ oblG_alive k (1/2 + 1/2/2)%Qp) ==∗
                 osat (<[k:=(obl_expired)]>Ω) ∗ oblG_expired k) ∗
           ((▷ (oblG_expired k ∗ R)) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (HE) "#Gvar".
    iMod (oblG_inv_acc with "Gvar") as "[Gv ACC]". 1: auto.
    iModIntro. iIntros "#Gf Ga". iSplitL "Gv Ga".
    { iNext. iDestruct "Gv" as "[(Ga2& HP) | (Ga2& HQR)]".
      - iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
      - iDestruct "HQR" as "([HQ | #GX]& HR)"; first iFrame.
        iPoseProof (oblG_alive_expired_false with "[$]") as "%". done. }
    iSplitR "ACC".
    { iIntros "% (H1& H2& H3)". iMod (osat_expire with "[$H1 $H2 $H3 $Gf]") as "($& $& _)". done. }
    iIntros "H". iApply "ACC". iNext. iRight. iDestruct "H" as "($&$)". auto.
  Qed.

End oinv.
