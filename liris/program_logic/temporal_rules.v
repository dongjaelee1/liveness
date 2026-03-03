From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.base_logic Require Export fancy_updates gupd.
From liris.temporal Require Export temporal_logic.
From liris.program_logic Require Export weakestpre.
(* From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg. *)

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
