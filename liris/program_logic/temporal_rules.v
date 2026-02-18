From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.base_logic Require Export fancy_updates gupd.
From liris.temporal Require Export temporal_logic.
From liris.program_logic Require Export weakestpre.
(* From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg. *)

Section sfgupd.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  (** Update rules *)
  Lemma gl_alloc_obl_gen E1 i G q ℓs μ v :
    Proper (le ==> layer_leibniz_le) ℓs →
    th_obls i G q -∗
    |={E1}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                  th_obls i (<[k:=v]>G) q ∗
                  gl_current k v (1/2)%Qp ∗
                  gl_layers k ℓs ∗ gl k v ∗ gl_fuel k (ℓs v) μ ∗
                  wit_layer k v (ℓs v) ∗
                  ([∗ set] u ∈ set_seq 0 v, gl_done k u) ∗
                  (∀ E2 N (P Q R : iProp Σ), ▷ P ={E2}=∗ gl_variant N k v P Q R).
  Proof.
    iIntros (MONO) "Tb %%% $". iMod (gl_alloc_obl_0 with "Tb") as "(%& $& $& $& $& $& $& $& $& H)". by iModIntro.
  Qed.
  Lemma gl_alloc_obl E i G q ℓs μ N v P Q R :
    Proper (le ==> layer_leibniz_le) ℓs →
    th_obls i G q -∗
    (▷ P) -∗
    |={E}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                 th_obls i (<[k:=v]>G) q ∗
                 gl_current k v (1/2)%Qp ∗
                 gl_layers k ℓs ∗ gl k v ∗ gl_fuel k (ℓs v) μ ∗
                 gl_variant N k v P Q R ∗
                 wit_layer k v (ℓs v) ∗
                 ([∗ set] u ∈ set_seq 0 v, gl_done k u).
  Proof.
    iIntros (MONO) "Tb HP %%% $". iApply (gl_alloc_obl_1 with "Tb HP").
  Qed.

  Lemma gl_alloc_done_gen E1 ℓs μ v :
    Proper (le ==> layer_leibniz_le) ℓs →
    ⊢ |={E1}=>g ∃ k, gl_layers k ℓs ∗ gl k v ∗ gl_current k v 1 ∗ gl_done k v ∗ gl_fuel k (ℓs v) μ ∗
                    wit_layer k v (ℓs v) ∗
                    ([∗ set] u ∈ set_seq 0 (S v), gl_done k u) ∗
                    (∀ E2 N (P Q R : iProp Σ), ▷ Q ={E2}=∗ gl_variant N k v P Q R).
  Proof.
    iIntros (MONO) "%%% $". iMod (gl_alloc_done_0) as "(%& $& $& $& $& $& $& $& H)". by iModIntro.
  Qed.
  Lemma gl_alloc_done E ℓs μ N v P Q R :
    Proper (le ==> layer_leibniz_le) ℓs →
    (▷ Q) -∗
    |={E}=>g ∃ k, gl_layers k ℓs ∗ gl k v ∗ gl_current k v 1 ∗ gl_done k v ∗ gl_fuel k (ℓs v) μ ∗
                 gl_variant N k v P Q R ∗
                 wit_layer k v (ℓs v) ∗
                 ([∗ set] u ∈ set_seq 0 (S v), gl_done k u).
  Proof.
    iIntros (MONO) "HQ %%% $". iApply (gl_alloc_done_1 with "HQ").
  Qed.

  Lemma gl_lock E qc k v1 N (P1 Q1 R1 : iProp Σ) :
    ↑N ⊆ E →
    gl_current k v1 qc -∗
    gl_done k v1 -∗
    gl_variant N k v1 P1 Q1 R1 -∗
    |={E,E ∖ ↑N}=> (▷ (gl_current k v1 qc ∗ Q1)) ∗
                  (∀ i G q ℓs,
                     th_obls i G q -∗
                     gl_current k v1 1 -∗
                     gl_layers k ℓs -∗
                     ∀ v2 μ, (⌜ v1 < v2 ⌝) →
                             ∀ E0, |={E0}=>g (th_obls i (<[k:=v2]>G) q ∗ ⌜ G !! k = None ⌝ ∗
                                             gl_current k v2 (1/2)%Qp ∗
                                             gl k v2 ∗ gl_fuel k (ℓs v2) μ ∗
                                             wit_layer k v2 (ℓs v2) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit_layer k u (ℓs u)) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u)) ∗
                                          (∀ E1 (P2 Q2 R2 : iProp Σ), (▷ P2) ={E1}=∗ gl_variant N k v2 P2 Q2 R2) ∗
                                          ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (Mask) "Gc Gd Gv". iMod (gl_lock_0 with "Gc Gd Gv") as "[$ H]". 1: eauto.
    iIntros "!> %%%% Tb Gc Gw %%%". iPoseProof ("H" with "Tb Gc Gw [//]") as "H".
    iIntros "% %%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
  Qed.

  Lemma gl_unlock E i G q N k v P Q R :
    ↑N ⊆ E →
    G !! k = Some v →
    th_obls i G q -∗
    gl_variant N k v P Q R -∗
    |={E,E ∖ ↑N}=> (▷ (th_obls i G q ∗ gl_locked k v ∗ P)) ∗
                  (th_obls i G q -∗
                   gl_locked k v -∗
                   ∀ E0, |={E0}=>g (th_obls i (delete k G) q ∗ gl_current k v (1/2)%Qp ∗ gl_done k v) ∗
                                (▷ Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (Mask LUGk) "Tb Gv". iMod (gl_unlock_0 with "Tb Gv") as "[$ H]". 1,2: eauto.
    iIntros "!> Tb Gl". iPoseProof ("H" with "Tb Gl") as "H".
    iIntros "% %%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
  Qed.

  Lemma gl_new_version E k qc v1 N (P1 Q1 R1 : iProp Σ) :
    ↑N ⊆ E →
    gl_current k v1 qc -∗
    gl_done k v1 -∗
    gl_variant N k v1 P1 Q1 R1 -∗
    |={E,E ∖ ↑N}=> (▷ (gl_current k v1 qc ∗ Q1)) ∗
                  (gl_current k v1 1 -∗
                   ∀ v2, (⌜ v1 < v2 ⌝) →
                         ∀ E0, |={E0}=>g (gl k v2 ∗ gl_done k v2 ∗ gl_current k v2 1 ∗
                                         ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u)) ∗
                                      (∀ E0 (P2 Q2 R2 : iProp Σ), (▷ Q2) ={E0}=∗ gl_variant N k v2 P2 Q2 R2) ∗
                                      ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (Mask) "Gc Gd Gv". iMod (gl_new_version_0 with "Gc Gd Gv") as "[$ H]". 1: eauto.
    iIntros "!> Gc %%". iPoseProof ("H" with "Gc [//]") as "H".
    iIntros "% %%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
  Qed.

  Lemma gl_change_owner E i1 i2 G1 G2 q1 q2 k v ℓ0 :
    G1 !! k = Some v →
    th_obls i1 G1 q1 -∗
    th_obls i2 G2 q2 -∗
    gl_fuel k ℓ0 1 -∗
    |={E}=>g th_obls i1 (delete k G1) q1 ∗ th_obls i2 (<[k:=v]>G2) q2 ∗ ⌜ G2 !! k = None ⌝.
  Proof.
    iIntros (LUG1) "Tb1 Tb2 Gf %%% $".
    iMod (gl_change_owner_0 with "Tb1 Tb2 Gf") as "H". 1: eauto.
    by iModIntro.
  Qed.

  Lemma gl_terminate E i :
    th_obls i ∅ 1 -∗ |={E}=>g th_term i.
  Proof.
    iIntros "Tb %%% $". iMod (gl_terminate_0 with "Tb") as "#Tt". auto.
  Qed.

  Lemma gl_check_witnesses E R :
    ([∗ map] r ↦ v ∈ R, gl r v) -∗
    |={E}=>g ([∗ map] r ↦ v ∈ R, wit r v Ord.O ∨ gl_done r v).
  Proof.
    iIntros "Rs %%% $". iMod (gl_check_witnesses_0 with "Rs") as "H". auto.
  Qed.

End sfgupd.

Section temporal.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  (** Always *)
  Lemma gl_always_alloc E :
    ⊢ |={E}=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P : iProp Σ), (▷ P) ={E}=∗ gl_always N k P).
  Proof.
    iIntros "%%% $". iMod (gl_always_alloc_0) as "H". eauto.
  Qed.

  (** Until *)
  Lemma gl_until_alloc E i G q ℓ μ :
    th_obls i G q -∗
    |={E}=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ gl_current k 0 (1 / 2) ∗ 
                 gl_layers k (λ _, ℓ) ∗ gl k 0 ∗ gl_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 ∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ gl_until N k P Q.
  Proof.
    iIntros "TG %%% $". iMod (gl_until_alloc_0 with "TG") as "(%& $& $& $& $& $& $& $& _& $)". eauto.
  Qed.

  Lemma gl_until_done_alloc E :
    ⊢ |={E}=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ Q ={E}=∗ gl_until N k P Q).
  Proof.
    iIntros "%%% $". iMod (gl_until_done_alloc_0) as "$". eauto.
  Qed.

  Lemma gl_until_fulfill E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ gl_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     gl_locked k 0 -∗
     ∀ E0, |={E0}=>g (th_obls i (delete k G) q ∗ gl_current k 0 (1 / 2) ∗ gl_done k 0) ∗
                  (▷ Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (MASK Lu) "TG GV". iMod (gl_until_fulfill_0 with "TG GV") as "[$ H]". 1,2: auto.
    iIntros "!> TG GL %". iPoseProof ("H" with "TG GL") as "H".
    iIntros "%%% $". iMod ("H" $! _) as "$". eauto.
  Qed.

  Lemma gl_until_retrieve E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ Q)) ∗
    (gl_current k 0 1 -∗
     ∀ E0, |={E0}=>g (|={E ∖ ↑N,E}=> True)).
  Proof.
    iIntros (MASK) "Gc #Gd #GV". iMod (gl_until_retrieve_0 with "Gc Gd GV") as "[$ H]". 1: eauto.
    iIntros "!> Gc % %%% $". iPoseProof ("H" with "Gc") as "H". iMod ("H" $! Θ) as "(_& _& $)". eauto.
  Qed.

  (** Weak Until *)
  Lemma gl_weakuntil_alloc E i G q ℓ μ :
    th_obls i G q -∗
    |={E}=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ gl_current k 0 (1 / 2) ∗ 
                 gl_layers k (λ _, ℓ) ∗ gl k 0 ∗ gl_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 (∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ gl_weakuntil N k P Q).
  Proof.
    iIntros "TG %%% $". iMod (gl_weakuntil_alloc_0 with "TG") as "(%& $& $& $& $& $& $& $& _& $)". eauto.
  Qed.

  Lemma gl_weakuntil_done_alloc E :
    ⊢ |={E}=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ (Q ∨ ∃ k', gl_always N k' P) ={E}=∗ gl_weakuntil N k P Q).
  Proof.
    iIntros "%%% $". iMod (gl_weakuntil_done_alloc_0) as "$". eauto.
  Qed.

  Lemma gl_weakuntil_fulfill E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ gl_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     gl_locked k 0 -∗
     ∀ E0, |={E0}=>g (th_obls i (delete k G) q ∗ gl_current k 0 (1 / 2) ∗ gl_done k 0) ∗
                  (▷ (Q ∨ ∃ k', gl_always N k' P) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    iIntros (MASK LU) "TG GV". iMod (gl_weakuntil_fulfill_0 with "TG GV") as "[$ H]". 1,2: auto.
    iIntros "!> TG GL % %%% $". iPoseProof ("H" with "TG GL") as "H". iMod ("H" $! _) as "$". eauto.
  Qed.

  Lemma gl_weakuntil_retrieve E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ (Q ∨ ∃ k', gl_always N k' P))) ∗
    (gl_current k 0 1 -∗
     ∀ E0, |={E0}=>g (|={E ∖ ↑N,E}=> True)).
  Proof.
    iIntros (MASK) "Gc Gd GV". iMod (gl_weakuntil_retrieve_0 with "Gc Gd GV") as "[$ H]". 1: auto.
    iIntros "!> Gc % %%% $". iPoseProof ("H" with "Gc") as "H". iMod ("H" $! _) as "(_& _& $)". eauto.
  Qed.

End temporal.
