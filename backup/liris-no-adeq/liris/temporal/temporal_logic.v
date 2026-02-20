From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.prelude Require Import options.
From liris.temporal Require Export temporal_formula.
From liris.base_logic Require Export gupd.

(* FIXME: more to somewhere else. *)
Section aux.
  Context `{SI : indexT}.

  Global Instance big_opL_proper_eq {M : ofe} (o : M → M → M) `{!Monoid o} {A : Type} :
    Proper (pointwise_relation nat (pointwise_relation A eq) ==> eq ==> eq) (big_opL o).
  Proof.
    repeat intro. subst y0. revert x y H. rename x0 into l. induction l; intros f1 f2 Hf; simpl; auto.
    f_equal.
    - rewrite Hf. auto.
    - eapply IHl. repeat intro. rewrite Hf. auto.
  Qed.

End aux.

(** Part 1. Define some useful patterns corresponding to temporal properties. *)
(* Always P *)
Local Definition gl_always_def `{SI : indexT} `{@gupdGS SI Σ} N k (P : iProp Σ) : iProp Σ :=
  (gl_variant N k 0 ⌜ False ⌝ P ⌜ False ⌝)%I.
Local Definition gl_always_aux : seal (@gl_always_def). Proof. by eexists. Qed.
Definition gl_always := gl_always_aux.(unseal).
Local Definition gl_always_unseal :
  @gl_always = @gl_always_def := gl_always_aux.(seal_eq).
Global Arguments gl_always {SI Σ _}.

(* P Until Q *)
Local Definition gl_until_def `{SI : indexT} `{@gupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (gl_variant N k 0 P Q ⌜ True ⌝)%I.
Local Definition gl_until_aux : seal (@gl_until_def). Proof. by eexists. Qed.
Definition gl_until := gl_until_aux.(unseal).
Local Definition gl_until_unseal :
  @gl_until = @gl_until_def := gl_until_aux.(seal_eq).
Global Arguments gl_until {SI Σ _}.

(* Eventually P *)
Definition gl_eventually `{SI : indexT} `{@gupdGS SI Σ} N k (P : iProp Σ) : iProp Σ :=
  (gl_until N k ⌜ True ⌝ P)%I.
Global Arguments gl_eventually {SI Σ _}.

(* Local Definition gl_eventually_def `{SI : indexT} `{@gupdGS SI Σ} N k v (P : iProp Σ) : iProp Σ := *)
(*   (gl_until N k v ⌜ True ⌝ P)%I. *)
(* Local Definition gl_eventually_aux : seal (@gl_eventually_def). Proof. by eexists. Qed. *)
(* Definition gl_eventually := gl_eventually_aux.(unseal). *)
(* Local Definition gl_eventually_unseal : *)
(*   @gl_eventually = @gl_eventually_def := gl_eventually_aux.(seal_eq). *)
(* Global Arguments gl_eventually {SI Σ _}. *)

(* P Weak until Q *)
Local Definition gl_weakuntil_def `{SI : indexT} `{@gupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (gl_until N k P (Q ∨ ∃ k', gl_always N k' P))%I.
Local Definition gl_weakuntil_aux : seal (@gl_weakuntil_def). Proof. by eexists. Qed.
Definition gl_weakuntil := gl_weakuntil_aux.(unseal).
Local Definition gl_weakuntil_unseal :
  @gl_weakuntil = @gl_weakuntil_def := gl_weakuntil_aux.(seal_eq).
Global Arguments gl_weakuntil {SI Σ _}.

(* P Release Q *)
Definition gl_release `{SI : indexT} `{@gupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (gl_weakuntil N k Q (Q ∗ P))%I.
Global Arguments gl_release {SI Σ _}.

(* Local Definition gl_release_def `{SI : indexT} `{@gupdGS SI Σ} N k v (P Q : iProp Σ) : iProp Σ := *)
(*   (gl_weakuntil N k v Q (Q ∗ P))%I. *)
(* Local Definition gl_release_aux : seal (@gl_release_def). Proof. by eexists. Qed. *)
(* Definition gl_release := gl_release_aux.(unseal). *)
(* Local Definition gl_release_unseal : *)
(*   @gl_release = @gl_release_def := gl_release_aux.(seal_eq). *)
(* Global Arguments gl_release {SI Σ _}. *)

(* P Strong release Q *)
Definition gl_strongrelease `{SI : indexT} `{@gupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (gl_until N k Q (Q ∗ P))%I.
Global Arguments gl_strongrelease {SI Σ _}.

(* Local Definition gl_strongrelease_def `{SI : indexT} `{@gupdGS SI Σ} N k v (P Q : iProp Σ) : iProp Σ := *)
(*   (gl_until N k v Q (Q ∗ P))%I. *)
(* Local Definition gl_strongrelease_aux : seal (@gl_strongrelease_def). Proof. by eexists. Qed. *)
(* Definition gl_strongrelease := gl_strongrelease_aux.(unseal). *)
(* Local Definition gl_strongrelease_unseal : *)
(*   @gl_strongrelease = @gl_strongrelease_def := gl_strongrelease_aux.(seal_eq). *)
(* Global Arguments gl_strongrelease {SI Σ _}. *)

Section proof.
  Context `{SI : indexT} `{!gupdGS Σ}.

  Local Ltac unfold_temps :=
    try rewrite gl_always_unseal /gl_always_def;
    try rewrite gl_until_unseal /gl_until_def;
    try rewrite /gl_eventually;
    try rewrite gl_weakuntil_unseal /gl_weakuntil_def;
    try rewrite /gl_release;
    try rewrite /gl_strongrelease.

  Lemma gl_always_unfold N k (P : iProp Σ) :
    gl_always N k P = (gl_variant N k 0 ⌜ False ⌝ P ⌜ False ⌝)%I.
  Proof. rewrite gl_always_unseal. done. Qed.
  Lemma gl_until_unfold N k (P Q : iProp Σ) :
    gl_until N k P Q = (gl_variant N k 0 P Q ⌜ True ⌝)%I.
  Proof. rewrite gl_until_unseal. done. Qed.
  Lemma gl_eventually_unfold N k (P : iProp Σ) :
    gl_eventually N k P = (gl_until N k ⌜ True ⌝ P)%I.
  Proof. done. Qed.
  Lemma gl_weakuntil_unfold N k (P Q : iProp Σ) :
    gl_weakuntil N k P Q = (gl_until N k P (Q ∨ ∃ k', gl_always N k' P))%I.
  Proof. rewrite gl_weakuntil_unseal. done. Qed.
  Lemma gl_release_unfold N k (P Q : iProp Σ) :
    gl_release N k P Q = (gl_weakuntil N k Q (Q ∗ P))%I.
  Proof. done. Qed.
  Lemma gl_strongrelease_unfold N k (P Q : iProp Σ) :
    gl_strongrelease N k P Q = (gl_until N k Q (Q ∗ P))%I.
  Proof. done. Qed.

  (** Always *)
  Global Instance gl_always_persistent N k P : Persistent (gl_always N k P).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_always_contractive N k : Contractive (gl_always N k).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_always_ne N k : NonExpansive (gl_always N k).
  Proof. apply _. Qed.

  Lemma gl_always_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P : iProp Σ), (▷ P) ={E}=∗ gl_always N k P).
  Proof.
    unfold_temps.
    iMod (gl_alloc_done_0 _ (λ _, 0%ordi) 0%M 0) as "(%& _& $& $& #Gd& _& _& _& H)".
    iModIntro. iFrame "Gd". iIntros (???). iApply "H".
  Qed.

  Lemma gl_always_acc E N k P :
    ↑N ⊆ E →
    gl_done k 0 -∗
    gl_always N k P ={E,E ∖ ↑N}=∗
    (▷ (P)) ∗ ((▷ (P)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "#Gd #GV". iMod (gl_variant_acc with "GV") as "[H ACC]". 1: auto.
    iDestruct "H" as "[[>(_& %) | H] | >(_& %)]"; [done | | done].
    iModIntro. iSplitL "H".
    { iNext. iDestruct "H" as "[_ $]". }
    iIntros "HP". iApply "ACC". iNext. iApply gl_variant_cases_unfold. iLeft; iRight. eauto.
  Qed.

  (** Until *)
  Global Instance gl_until_persistent N k P Q : Persistent (gl_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_until_contractive_1 N k Q : Contractive (λ P, gl_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_until_contractive_2 N k P : Contractive (λ Q, gl_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_until_ne_1 N k Q : NonExpansive (λ P, gl_until N k P Q).
  Proof. apply _. Qed.
  Global Instance gl_until_ne_2 N k P : NonExpansive (λ Q, gl_until N k P Q).
  Proof. apply _. Qed.

  Lemma gl_until_alloc_0 Θ i G q ℓ μ :
    th_obls i G q -∗
    |=[Θ]=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ gl_current k 0 (1 / 2) ∗ 
                 gl_layers k (λ _, ℓ) ∗ gl k 0 ∗ gl_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 ([∗ set] u ∈ set_seq 0 0, gl_done k u) ∗
                 ∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ gl_until N k P Q.
  Proof.
    unfold_temps.
    iIntros "TG". iMod (gl_alloc_obl_0 _ _ _ _ (λ _, ℓ) μ 0 with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma gl_until_done_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ Q ={E}=∗ gl_until N k P Q).
  Proof.
    unfold_temps.
    iMod (gl_alloc_done_0 _ (λ _, 0%ordi) 0%M 0) as "(%& _& $& $& $& _& _& _& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma gl_until_fulfill_0 E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ gl_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     gl_locked k 0 -∗
     ∀ Θ, |=[Θ]=>g (th_obls i (delete k G) q ∗ gl_current k 0 (1 / 2) ∗ gl_done k 0) ∗
                (▷ Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    unfold_temps.
    iIntros (MASK LU) "TG #GV". iMod (gl_unlock_0 with "TG GV") as "[$ ACC]". 1,2: auto.
    eauto.
  Qed.

  Lemma gl_until_retrieve_0 E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ Q)) ∗
    (gl_current k 0 1 -∗
     ∀ Θ, |=[Θ]=>g (gl k (S 0) ∗ gl_done k (S 0) ∗ gl_current k (S 0) 1) ∗
                (∀ E0, |={E0}=> gl_variant N k (S 0) ⌜ False ⌝ ⌜ True ⌝ ⌜ False ⌝) ∗
                (|={E ∖ ↑N,E}=> True)).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #Gd #GV". iMod (gl_new_version_0 with "Gc Gd GV") as "[$ H]". 1: eauto.
    iIntros "!> Gc %". iPoseProof ("H" with "Gc") as "H". iPoseProof ("H" $! (S 0) with "[]") as "H".
    1: iPureIntro; lia.
    iMod ("H" $! _) as "(($& $& $& _)& A& B)". iModIntro. iSplitL "A".
    - iIntros (?). by iApply "A".
    - by iApply "B".
  Qed.

  Lemma gl_until_acc_own E i G q N k P Q :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    ▷ (th_obls i G q ∗ gl_locked k 0 ∗ P) ∗
    (▷ gl_variant_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK Lu) "TG #GV". iMod (gl_variant_acc_own with "TG GV") as "[$ $]". all: auto.
  Qed.

  Lemma gl_until_acc_current E N k q P Q :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ (gl_locked k 0 ∗ P ∨ gl_done k 0 ∗ Q))) ∗
    (▷ gl_variant_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #GV". iMod (gl_variant_acc_current_timeless with "Gc GV") as "[$ $]". all: auto.
  Qed.

  Lemma gl_until_acc_current_done E N k q P Q :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ Q)) ∗
    (▷ gl_variant_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #Gd #GV". iMod (gl_variant_acc_current_done_timeless with "Gc Gd GV") as "[$ $]". all: auto.
  Qed.

  (** Weak Until *)
  Global Instance gl_weakuntil_persistent N k P Q : Persistent (gl_weakuntil N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance gl_weakuntil_contractive_1 N k Q : Contractive (λ P, gl_weakuntil N k P Q).
  Proof.
    (* FIXME: better proof? *)
    unfold_temps. repeat intro. rewrite gl_until_contractive_1; last eauto.
    apply gl_until_contractive_2. econstructor. intros. inv H. specialize (dist_later_lt _ H0).
    solve_proper.
  Qed.
  Global Instance gl_weakuntil_contractive_2 N k P : Contractive (λ Q, gl_weakuntil N k P Q).
  Proof.
    (* FIXME: better proof? *)
    unfold_temps. repeat intro.
    apply gl_until_contractive_2. econstructor. intros. inv H. specialize (dist_later_lt _ H0).
    solve_proper.
  Qed.
  Global Instance gl_weakuntil_ne_1 N k Q : NonExpansive (λ P, gl_weakuntil N k P Q).
  Proof. apply _. Qed.
  Global Instance gl_weakuntil_ne_2 N k P : NonExpansive (λ Q, gl_weakuntil N k P Q).
  Proof. apply _. Qed.

  Lemma gl_weakuntil_alloc_0 Θ i G q ℓ μ :
    th_obls i G q -∗
    |=[Θ]=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ gl_current k 0 (1 / 2) ∗ 
                 gl_layers k (λ _, ℓ) ∗ gl k 0 ∗ gl_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 ([∗ set] u ∈ set_seq 0 0, gl_done k u) ∗
                 (∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ gl_weakuntil N k P Q).
  Proof.
    unfold_temps.
    iIntros "TG". iMod (gl_until_alloc_0 _ _ _ _ ℓ μ with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma gl_weakuntil_done_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ gl_current k 0 1 ∗ gl_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ (Q ∨ ∃ k', gl_always N k' P) ={E}=∗ gl_weakuntil N k P Q).
  Proof.
    iMod (gl_until_done_alloc_0) as "(%& $& $& $& H)".
    iIntros "!> %%%%". rewrite gl_weakuntil_unfold. iApply "H".
  Qed.

  Lemma gl_weakuntil_fulfill_0 E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ gl_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     gl_locked k 0 -∗
     ∀ Θ, |=[Θ]=>g (th_obls i (delete k G) q ∗ gl_current k 0 (1 / 2) ∗ gl_done k 0) ∗
                (▷ (Q ∨ ∃ k', gl_always N k' P) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    rewrite gl_weakuntil_unfold.
    iIntros (MASK LU) "TG #GV". iMod (gl_until_fulfill_0 with "TG GV") as "[$ ACC]". 1,2: auto.
    eauto.
  Qed.

  Lemma gl_weakuntil_retrieve_0 E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ (Q ∨ ∃ k', gl_always N k' P))) ∗
    (gl_current k 0 1 -∗
     ∀ Θ, |=[Θ]=>g (gl k (S 0) ∗ gl_done k (S 0) ∗ gl_current k (S 0) 1) ∗
                (∀ E0, |={E0}=> gl_variant N k (S 0) ⌜ False ⌝ ⌜ True ⌝ ⌜ False ⌝) ∗
                (|={E ∖ ↑N,E}=> True)).
  Proof.
    rewrite gl_weakuntil_unfold.
    iIntros (MASK) "Gc #Gd #GV". iMod (gl_until_retrieve_0 with "Gc Gd GV") as "[$ H]". 1: eauto.
    eauto.
  Qed.

  Lemma gl_weakuntil_acc_own E i G q N k P Q :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    ▷ (th_obls i G q ∗ gl_locked k 0 ∗ P) ∗
    (▷ gl_variant_cases k 0 P (Q ∨ ∃ k', gl_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite gl_weakuntil_unfold.
    iIntros (MASK Lu) "TG #GV". iMod (gl_until_acc_own with "TG GV") as "[$ $]". all: auto.
  Qed.

  Lemma gl_weakuntil_acc_current E N k q P Q :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ (gl_locked k 0 ∗ P ∨ gl_done k 0 ∗ (Q ∨ ∃ k', gl_always N k' P)))) ∗
    (▷ gl_variant_cases k 0 P (Q ∨ ∃ k', gl_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite gl_weakuntil_unfold.
    iIntros (MASK) "Gc #GV". iMod (gl_until_acc_current with "Gc GV") as "[$ $]". all: auto.
  Qed.

  Lemma gl_weakuntil_acc_current_done E N k q P Q :
    ↑N ⊆ E →
    gl_current k 0 q -∗
    gl_done k 0 -∗
    gl_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (gl_current k 0 q ∗ (Q ∨ ∃ k', gl_always N k' P))) ∗
    (▷ gl_variant_cases k 0 P (Q ∨ ∃ k', gl_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite gl_weakuntil_unfold.
    iIntros (MASK) "Gc #Gd #GV". iMod (gl_until_acc_current_done with "Gc Gd GV") as "[$ $]". all: auto.
  Qed.

End proof.

(** Part 2. Interpretation of tf to iProp. *)
(* Defined by the programming language. *)
Class tf_atomic_interp_logic_class `{SI : indexT} (Σ : gFunctors) (Π : Type) :=
  tfa_atomic_interp_logic : Π → iProp Σ.

(** Interpretation of tf to iProp. *)
Fixpoint tf_interp_logic `{SI : indexT} `{@tf_atomic_interp_logic_class SI Σ Π} `{@gupdGS SI Σ} (Φ : tf) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic π => tfa_atomic_interp_logic π
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => p
  | tf_and P Q => (tf_interp_logic P ∧ tf_interp_logic Q)%I
  | tf_or P Q => (tf_interp_logic P ∨ tf_interp_logic Q)%I
  | tf_impl P Q => (tf_interp_logic P → tf_interp_logic Q)%I
  | tf_forall A P => (∀ (a : A), tf_interp_logic (P a))%I
  | tf_exist A P => (∃ (a : A), tf_interp_logic (P a))%I
  | tf_sep P Q => (tf_interp_logic P ∗ tf_interp_logic Q)%I
  | tf_wand P Q => (tf_interp_logic P -∗ tf_interp_logic Q)%I
  | tf_variant N k v P Q R => gl_variant N k v (tf_interp_logic P) (tf_interp_logic Q) (tf_interp_logic R)
  end.

Global Arguments tf_interp_logic {SI Σ Π _ _}.

(** Notations *)
Notation "'⟦' Φ '⟧ₗ'" := (tf_interp_logic Φ%F).

Section reduction.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ}.

  Lemma tf_emp_interp_logic :
    ⟦tf_emp⟧ₗ = emp%I.
  Proof. done. Qed.
  Lemma tf_atomic_interp_logic π :
    ⟦tf_atomic π⟧ₗ = tfa_atomic_interp_logic π.
  Proof. done. Qed.
  Lemma tf_pure_interp_logic P :
    ⟦⌜P⌝⟧ₗ = (⌜P⌝)%I.
  Proof. done. Qed.
  Lemma tf_ghost_interp_logic P :
    ⟦⟨P⟩⟧ₗ = (P)%I.
  Proof. done. Qed.
  Lemma tf_and_interp_logic P Q :
    ⟦P ∧ Q⟧ₗ = (⟦P⟧ₗ ∧ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_or_interp_logic P Q :
    ⟦P ∨ Q⟧ₗ = (⟦P⟧ₗ ∨ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_impl_interp_logic P Q :
    ⟦P → Q⟧ₗ = (⟦P⟧ₗ → ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_forall_interp_logic A (P : A → tf) :
    ⟦∀ a, P a⟧ₗ = (∀ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_exist_interp_logic A (P : A → tf) :
    ⟦∃ a, P a⟧ₗ = (∃ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_sep_interp_logic P Q :
    ⟦P ∗ Q⟧ₗ = (⟦P⟧ₗ ∗ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_wand_interp_logic P Q :
    ⟦P -∗ Q⟧ₗ = (⟦P⟧ₗ -∗ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_variant_interp_logic N k v P Q R :
    ⟦tf_variant N k v P Q R⟧ₗ = (gl_variant N k v ⟦P⟧ₗ ⟦Q⟧ₗ ⟦R⟧ₗ)%I.
  Proof. done. Qed.

  Lemma tf_always_interp_logic N k P :
    ⟦tf_always N k P⟧ₗ = gl_always N k ⟦P⟧ₗ.
  Proof. rewrite tf_always_unfold gl_always_unfold. done. Qed.
  Lemma tf_until_interp_logic N k P Q :
    ⟦tf_until N k P Q⟧ₗ = gl_until N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_until_unfold gl_until_unfold. done. Qed.
  Lemma tf_eventually_interp_logic N k P :
    ⟦tf_eventually N k P⟧ₗ = gl_eventually N k ⟦P⟧ₗ.
  Proof. rewrite tf_eventually_unfold gl_eventually_unfold tf_until_interp_logic. done. Qed.
  Lemma tf_weakuntil_interp_logic N k P Q :
    ⟦tf_weakuntil N k P Q⟧ₗ = gl_weakuntil N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof.
    rewrite tf_weakuntil_unfold gl_weakuntil_unfold tf_until_interp_logic. simpl.
    rewrite temporal_formula.tf_always_unseal /temporal_formula.tf_always_def.
    rewrite gl_always_unseal /gl_always_def. simpl. done.
  Qed.
  Lemma tf_release_interp_logic N k P Q :
    ⟦tf_release N k P Q⟧ₗ = gl_release N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_release_unfold gl_release_unfold tf_weakuntil_interp_logic. done. Qed.
  Lemma tf_strongrelease_interp_logic N k P Q :
    ⟦tf_strongrelease N k P Q⟧ₗ = gl_strongrelease N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_strongrelease_unfold gl_strongrelease_unfold tf_until_interp_logic. done. Qed.

End reduction.
(* Making this opaque is reasonable only if we have a better reduction tactic than simpl. *)
(* Global Opaque tf_interp. *)

(** Ofe and Monoid structure. *)
Global Instance tf_equiv `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ} : Equiv tf :=
  λ Φ1 Φ2, ⟦Φ1⟧ₗ ≡ ⟦Φ2⟧ₗ.
Global Instance tf_equiv_Equivalence `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ} : Equivalence tf_equiv.
Proof.
  unfold tf_equiv. econstructor.
  - repeat intro. done.
  - repeat intro. rewrite H. done.
  - repeat intro. etrans; eauto.
Qed.
Canonical Structure tfO `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ} : ofe :=
  (Ofe tf (discrete_ofe_mixin tf_equiv_Equivalence)).

Class tf_op_interp_comm `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{@gupdGS SI Σ}
  (tf_o : tf → tf → tf) (iProp_o : iProp Σ → iProp Σ → iProp Σ) :=
  tf_op_interp_comm_intro : ∀ (P Q : tf), ⟦tf_o P Q⟧ₗ = (iProp_o ⟦P⟧ₗ ⟦Q⟧ₗ)%I.

Class tf_monoid_unit_interp_eq `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ}
  (tf_o : tf → tf → tf) `{!Monoid tf_o} (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o} :=
  tf_monoid_unit_interp_eq_intro : ⟦ monoid_unit ⟧ₗ = monoid_unit.

Section instances.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ}.

  Global Instance tf_and_interp_comm : tf_op_interp_comm tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_interp_comm : tf_op_interp_comm tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_impl_interp_comm : tf_op_interp_comm tf_impl bi_impl.
  Proof. econstructor. Qed.
  Global Instance tf_sep_interp_comm : tf_op_interp_comm tf_sep bi_sep.
  Proof. econstructor. Qed.
  Global Instance tf_wand_interp_comm : tf_op_interp_comm tf_wand bi_wand.
  Proof. econstructor. Qed.

  Program Global Instance tf_and_monoid : Monoid tf_and := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_and_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic tf_emp_interp_logic left_id. done. Qed.

  Program Global Instance tf_or_monoid : Monoid tf_or := Build_Monoid _ _ _ (⌜ False ⌝)%F _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_or_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic tf_pure_interp_logic left_id. done. Qed.

  Program Global Instance tf_sep_monoid : Monoid tf_sep := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_sep_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic tf_emp_interp_logic left_id. done. Qed.

  Global Instance tf_and_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_sep_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_sep bi_sep.
  Proof. econstructor. Qed.

End instances.

Section big_op.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!gupdGS Σ}.

  Lemma tf_big_opL_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A (P : nat → A → tf) (l : list A) :
    ⟦[^tf_o list] n ↦ a ∈ l, P n a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P n a⟧ₗ))%I.
  Proof.
    cut (∀ m, ⟦[^tf_o list] n ↦ a ∈ l, P (m + n) a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P (m + n) a⟧ₗ))%I).
    { intros. specialize (H 0). simpl in H. auto. }
    induction l; intros; simpl; auto.
    rewrite (tf_op_interp_comm0). f_equal.
    erewrite (big_opL_proper_eq tf_o).
    - erewrite (IHl (S m)). apply big_opL_proper_eq; auto.
      repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - auto.
  Qed.

  Lemma tf_big_opM_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    K `{!EqDecision K} `{!Countable K} A
    (P : K → A → tf) (m : gmap K A) :
    ⟦[^tf_o map] k ↦ a ∈ m, P k a⟧ₗ = ([^iProp_o map] k ↦ a ∈ m, (⟦P k a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opM_unseal /big_op.big_opM_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x.1 x.2)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x.1 x.2⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + repeat intro. unfold uncurry. destruct a0. done.
    - repeat intro. unfold uncurry. destruct a0. done.
  Qed.

  Lemma tf_big_opS_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A `{!EqDecision A} `{!Countable A}
    (P : A → tf) (s : gset A) :
    ⟦[^tf_o set] a ∈ s, P a⟧ₗ = ([^iProp_o set] a ∈ s, (⟦P a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opS_unseal /big_op.big_opS_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + done.
    - done.
  Qed.

End big_op.
