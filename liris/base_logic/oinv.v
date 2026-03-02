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
  Global Instance oblG_variant_contractive_1 N k q Q R : Contractive (λ P, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.
  Global Instance oblG_variant_contractive_2 N k q P R : Contractive (λ Q, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.
  Global Instance oblG_variant_contractive_3 N k q P Q : Contractive (λ R, oblG_inv N k q P Q R).
  Proof. rewrite /oblG_inv /oblG_variant. solve_contractive. Qed.

  Global Instance oblG_variant_persistent N k q P Q R : Persistent (oblG_inv N k q P Q R).
  Proof. apply _. Qed.

  (** oblG_inv rules *)
  Lemma oblG_variant_acc E N k q P Q R :
    ↑N ⊆ E →
    oblG_inv N k q P Q R ={E,E ∖ ↑N}=∗
    ▷ oblG_variant k q P Q R ∗
    (▷ oblG_variant k q P Q R ={E ∖ ↑N,E}=∗ True).
  Proof. iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto. Qed.

  Lemma oblG_variant_acc_assigned E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_assigned k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_assigned k q2 ∗ (oblG_assigned k q1 ∗ P))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[#Gf _]".
      iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
  Qed.

  Lemma oblG_variant_acc_fulfilled E N k q P Q R :
    ↑N ⊆ E →
    oblG_inv N k q P Q R -∗ oblG_fulfilled k
    ={E,E ∖ ↑N}=∗
    (▷ ((Q ∨ oblG_expired k) ∗ R)) ∗
    (▷ oblG_variant k q P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU #Gf". iMod (oblG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC"; last done.
      iNext. iDestruct "H" as "[H _]". iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    - iModIntro. iSplitR "ACC"; iFrame. iNext. iDestruct "H" as "[_ $]".
  Qed.

  Lemma oblG_variant_acc_alive E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_alive k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_alive k q2 ∗ ((oblG_assigned k q1 ∗ P) ∨ (oblG_fulfilled k ∗ Q ∗ R)))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (oblG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "(#Gf& [HQ | #Gx]& HR)".
      { iFrame. iRight. iFrame. eauto. }
      { iPoseProof (oblG_alive_expired_false with "[$]") as "%". done. }
  Qed.

  Lemma oblG_variant_acc_fulfilled_alive E N k q1 q2 P Q R :
    ↑N ⊆ E →
    oblG_inv N k q1 P Q R -∗ oblG_fulfilled k -∗ oblG_alive k q2
    ={E,E ∖ ↑N}=∗
    (▷ (oblG_alive k q2 ∗ (Q ∗ R))) ∗
    (▷ oblG_variant k q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU #Gf GV". iMod (oblG_variant_acc_fulfilled with "GU Gf") as "[H ACC]"; first auto.
    iModIntro. iSplitR "ACC"; last done. iNext. iDestruct "H" as "[[$ | #Gx] $]"; first eauto.
    iPoseProof (oblG_alive_expired_false with "[$]") as "%". done.
  Qed.

  (* Allocations *)
  Lemma oblG_variant_alloc_assigned E N k q P Q R :
    (▷ (oblG_assigned k q ∗ P)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma oblG_variant_alloc_fulfilled E N k q P Q R :
    (▷ (oblG_fulfilled k ∗ Q ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.
  Lemma oblG_variant_alloc_expired E N k q P Q R :
    (▷ (oblG_fulfilled k ∗ oblG_expired k ∗ R)) ={E}=∗ oblG_inv N k q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iNext. iRight. iDestruct "H" as "($&$&$)". Qed.

  (** Rules for oblG_inv and osat *)
  Lemma osat_variant_acc_assigned Ω k q0 q1 E N P Q R :
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R ∗
    osat Ω ∗ oblG_elem k ∗ oblG_assigned k q1
    ⊢ |={E,E ∖ ↑N}=>
          ▷ (osat Ω ∗ oblG_assigned k q1 ∗ (oblG_assigned k q0 ∗ P)) ∗
          (▷ oblG_variant k q0 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "(#Gvar& G& #Ge& Gl)".
    iMod (oblG_variant_acc with "Gvar") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; first iFrame.
        iDestruct "H" as "[H _]". iPoseProof (oblG_assigned_fulfilled_false with "[$Gl $H]") as "%". done.
      + done.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "(_& #Gvd& _)".
      iPoseProof (osat_lookup_version_expired with "[$G $Ge $Gvd]") as "%". destruct H as (?&?&?&?).
      iPoseProof (osat_lookup_assigned with "[$G $Ge $Gl]") as "%". destruct H1 as (?&?&?).
      rewrite H in H1. inv H1. lia.
  Qed.

  Lemma osat_variant_unlock Ω k t q0 q1 E N P Q R :
    (q0 + q1 = 1/2 + 1/2/2)%Qp →
    ↑N ⊆ E →
    oblG_inv N k q0 P Q R ∗
    osat Ω ∗
    oblG_elem k ∗ oblG_assigned k q1 ∗ oblG_owner k t (1/2 + 1/2/2)%Qp
    ⊢ |={E,E ∖ ↑N}=>
          ▷ ((osat Ω ∗ oblG_assigned k (1/2 + 1/2/2)%Qp ∗ oblG_owner k t (1/2 + 1/2/2)%Qp ∗ P) ∗
             ((osat Ω ∗ oblG_assigned k (1/2 + 1/2/2)%Qp ∗ oblG_owner k t (1/2 + 1/2/2)%Qp ∗ ▷ Q)
              ={E ∖ ↑N,E}=∗
              osat (<[k:=(v, obligation_fulfilled)]>Ω) ∗
              oblG_fulfilled k ∗
              (⌜ ∀ a, obligation_step (v, obligation_assigned a t) (v, obligation_fulfilled) ⌝))).
  Proof.
    iIntros (Hq HE) "(#Gvar& G& #Ge& Gl& Go)".
    iMod (osat_variant_acc_assigned with "[$Gvar $G $Ge $Gl]") as "[H ACC]"; first auto.
    iModIntro. iNext. iDestruct "H" as "($& Gl1& Gl2& $)".
    iCombine "Gl2 Gl1" as "Gl". rewrite Hq. iFrame "Gl Go".
    iIntros "(G& Gl& Go& HQ)".
    iMod (osat_unlock with "[$G $Ge $Gl $Go]") as "($& #Gu& $)". iFrame "Gu".
    iApply "ACC". iNext. iLeft. iRight. iFrame. eauto.
  Qed.

  Lemma osat_variant_lock Ω k1 v2 ℓ μ t q0 q1 E N (P1 Q1 R1 P2 Q2 R2 : iProp Σ) :
    (q0 + q1 = 1/2 + 1/2/2)%Qp →
    v1 < v2 →
    ↑N ⊆ E →
    oblG_inv N k1 q0 P1 Q1 R1 ∗
    osat Ω ∗
    oblG_layer k ℓ ∗ oblG_fulfilled k1 ∗ oblG_version k1 (1/2 + 1/2/2)%Qp
    ⊢ |={E,E ∖ ↑N}=>
          ▷ ((osat Ω ∗ oblG_version k1 (1/2 + 1/2/2)%Qp ∗ Q1) ∗
             ((osat Ω ∗ oblG_version k1 (1/2 + 1/2/2)%Qp ∗ (▷ R1) ∗ (▷ P2))
              ={E ∖ ↑N,E}=∗
              ∃ μ', osat (<[k:=(v2, obligation_assigned (measure (ℓ v2) (μ')%M) t)]>Ω) ∗
              oblG_assigned k2 q1 ∗
              oblG_version k2 (1/2 + 1/2/2)%Qp ∗
              oblG_fuel k (measure (ℓ v2) μ) ∗
              oblG_owner k t (1/2 + 1/2/2)%Qp ∗
              ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), oblG_version_lb k u ∗ oblG_fulfilled k u) ∗
              (⌜ obligation_step (v1, obligation_fulfilled) (v2, obligation_assigned (measure (ℓ v2) (μ')%M) t) ⌝) ∗
              oblG_inv N k2 q0 P2 Q2 R2)).
  Proof.
    iIntros (Hq Hv HE) "(#Gvar& G& #Gwf& #Gu& Gv)".
    iPoseProof (oblG_layer_elem with "Gwf") as "#Ge".
    iMod (oblG_variant_acc_fulfilled with "Gvar Gu") as "[H ACC]"; first auto.
    iModIntro. iNext. iDestruct "H" as "[$ | (_& #Gvd& _)]"; cycle 1.
    { iPoseProof (oblG_version_expired_valid with "[$Gv $Gvd]") as "%". lia. }
    iFrame "G Gv". iIntros "(G& Gv& HR& HP)".
    iMod (osat_lock _ _ v1 v2 ℓ μ t with "[$G $Gwf $Gu $Gv]") as "(%& $& Gl& Gv& $& $& #Gus& $)"; first auto.
    iPoseProof (oblG_version_get_lb _ _ v2 with "Gv") as "#Gvl"; first lia.
    iPoseProof (oblG_version_get_expired _ _ v1 with "Gvl") as "#Gvd"; first lia.
    iFrame "Gv".
    rewrite -!Hq. iDestruct "Gl" as "[Gl1 Gl2]". iFrame "Gl2 Gus".
    iMod ("ACC" with "[HR]") as "_".
    { iNext. iRight. iFrame. auto. }
    iApply oblG_variant_alloc_assigned. iFrame.
  Qed.

End oinv.
