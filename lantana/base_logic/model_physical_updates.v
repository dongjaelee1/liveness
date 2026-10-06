(** * Model rounds of physical steps

    The model rounds taken by the program logic at a physical step: [mprog] for the step of a
    thread (progress of its obligations, credits for witnesses) and [mphys] for the change of
    the physical state and thread pool (forked threads). *)

From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.base_logic Require Export mupd.
Import uPred.

(** [mprog n Θ i P]: the model round of a step of thread [i]. The obligations of [i] make
    progress and the assigned witnesses make progress. *)
Definition mprog `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ i : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω1 W1,
     (model_interp h a Ω1 W1 n Θ) ={∅}=∗
     ∃ Ω2, (⌜(Ω1 ↪ₚ Ω2 | obl_cond_owner i)⌝) ∗
     ∀ W2, (⌜(W1 ↓ₚ W2 | wit_cond_assigned) ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗
           (model_interp (h ++ [(n, Ω2)]) (S a) Ω2 W2 n Θ) ∗ P)%I.

Notation "'@={' n , Θ , i '}=↓' P" := (mprog n Θ i P)
  (at level 99, P at level 200, format "@={ n , Θ , i }=↓  P").

Section mprog.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Global Instance mprog_ne n Θ i : NonExpansive (mprog n Θ i).
  Proof. intros ? P1 P2 HP. rewrite /mprog. do 20 (f_equiv || done). Qed.
  Global Instance mprog_proper n Θ i : Proper ((≡) ==> (≡)) (mprog n Θ i).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mprog_ne. apply equiv_dist. done. Qed.

  Lemma mprog_mono n Θ i P Q : (P ⊢ Q) → (mprog n Θ i P) ⊢ (mprog n Θ i Q).
  Proof.
    intros Hent. rewrite /mprog. iIntros "P %%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply Hent.
  Qed.
  Lemma mprog_wand_l n Θ i P Q : (P -∗ Q) ∗ (mprog n Θ i P) ⊢ (mprog n Θ i Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /mprog. iIntros "%%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply "PQ".
  Qed.

  Global Instance mprog_ent_proper n Θ i : Proper ((⊢) ==> (⊢)) (mprog n Θ i).
  Proof. intros P Q PQ. by apply mprog_mono. Qed.
  Global Instance mprog_flip_ent_proper n Θ i : Proper (flip (⊢) ==> flip (⊢)) (mprog n Θ i).
  Proof. intros P Q PQ; by apply mprog_mono. Qed.
  Global Instance mprog_equiv_proper n Θ i : Proper ((≡) ==> (≡)) (mprog n Θ i) := ne_proper _.

  Global Instance elim_mprog (p : bool) n Θ i P Q :
    ElimModal True p false (mprog n Θ i P) P (mprog n Θ i Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (mprog_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_mprog n Θ i P : (|={∅}=> mprog n Θ i P) ⊢ mprog n Θ i P.
  Proof.
    rewrite /mprog. iIntros "H %%%% IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_mprog (p : bool) n Θ i P Q :
    ElimModal True p false (|={∅}=> P) P (mprog n Θ i Q) (mprog n Θ i Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mprog. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

End mprog.

(** [mphys n1 n2 Θ1 Θ2 P]: a model round without change of the obligations, from the
    physical state [n1] with thread pool [Θ1] to [n2] with [Θ2]. *)
Definition mphys `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class} n1 n2 Θ1 Θ2 : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω W,
     (model_interp h a Ω W n1 Θ1) ={∅}=∗
     (model_interp (h ++ [(n2, Ω)]) (S a) Ω W n2 Θ2) ∗ P)%I.

Notation "'@={' n1 , n2 , Θ1 , Θ2 '}=>' P" := (mphys n1 n2 Θ1 Θ2 P)
  (at level 99, P at level 200, format "@={ n1 , n2 , Θ1 , Θ2 }=>  P").

Section mphys.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Global Instance mphys_ne n1 n2 Θ1 Θ2 : NonExpansive (mphys n1 n2 Θ1 Θ2).
  Proof. intros ? P1 P2 HP. rewrite /mphys. do 20 (f_equiv || done). Qed.
  Global Instance mphys_proper n1 n2 Θ1 Θ2 : Proper ((≡) ==> (≡)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mphys_ne. apply equiv_dist. done. Qed.

  Lemma mphys_mono n1 n2 Θ1 Θ2 P Q : (P ⊢ Q) → (mphys n1 n2 Θ1 Θ2 P) ⊢ (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    intros Hent. rewrite /mphys. iIntros "P %%%% I".
    iMod ("P" with "I") as "[$ P]". iModIntro.
    by iApply Hent.
  Qed.
  Lemma mphys_wand_l n1 n2 Θ1 Θ2 P Q : (P -∗ Q) ∗ (mphys n1 n2 Θ1 Θ2 P) ⊢ (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /mphys. iIntros "%%%% I".
    iMod ("P" with "I") as "($& P)". iModIntro.
    by iApply "PQ".
  Qed.

  Global Instance mphys_ent_proper n1 n2 Θ1 Θ2 : Proper ((⊢) ==> (⊢)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P Q PQ. by apply mphys_mono. Qed.
  Global Instance mphys_flip_ent_proper n1 n2 Θ1 Θ2 : Proper (flip (⊢) ==> flip (⊢)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P Q PQ; by apply mphys_mono. Qed.
  Global Instance mphys_equiv_propern1 n1 n2 Θ1 Θ2 : Proper ((≡) ==> (≡)) (mphys n1 n2 Θ1 Θ2) := ne_proper _.

  Global Instance elim_mphys (p : bool) n1 n2 Θ1 Θ2 P Q :
    ElimModal True p false (mphys n1 n2 Θ1 Θ2 P) P (mphys n1 n2 Θ1 Θ2 Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (mphys_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_mphys n1 n2 Θ1 Θ2 P : (|={∅}=> mphys n1 n2 Θ1 Θ2 P) ⊢ mphys n1 n2 Θ1 Θ2 P.
  Proof.
    rewrite /mphys. iIntros "H %%%% IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_mphys (p : bool) n1 n2 Θ1 Θ2 P Q :
    ElimModal True p false (|={∅}=> P) P (mphys n1 n2 Θ1 Θ2 Q) (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mphys. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.


End mphys.