From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.prelude Require Import options.
From liris.base_logic Require Export gupd.
From transfinite.base_logic.lib Require Import ghost_map.

(** Simple syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} `{Σ : gFunctors} :=
| tf_atomic (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
| tf_impl (P Q : tf)
| tf_forall {A : Type} (P : A → tf)
| tf_exist {A : Type} (P : A → tf)
| tf_sep (P Q : tf)
| tf_wand (P Q : tf)
| tf_variant (N : namespace) (k : gl_id) (v : ghost_lock_version) (P Q R : tf).

(** Interpretation. *)
Fixpoint tf_interp `{SI : indexT} `{@gupdGS SI Σ} (Φ : tf) : iProp Σ :=
  match Φ with
  | tf_atomic p => p
  | tf_and P Q => (tf_interp P ∧ tf_interp Q)%I
  | tf_or P Q => (tf_interp P ∨ tf_interp Q)%I
  | tf_impl P Q => (tf_interp P → tf_interp Q)%I
  | @tf_forall _ _ A P => (∀ (a : A), tf_interp (P a))%I
  | @tf_exist _ _ A P => (∃ (a : A), tf_interp (P a))%I
  | tf_sep P Q => (tf_interp P ∗ tf_interp Q)%I
  | tf_wand P Q => (tf_interp P -∗ tf_interp Q)%I
  | tf_variant N k v P Q R => gl_variant N k v (tf_interp P) (tf_interp Q) (tf_interp R)
  end.

Section proof.
  Context `{SI : indexT} `{!gupdGS Σ}.

End proof.

(** Defines some useful patterns which corresponds to temporal properties. *)
(* Always *)
Local Definition tf_always_def `{SI : indexT} `{@gupdGS SI Σ}
  (N : namespace) (P : tf) : tf :=
  tf_exist (λ (k : gl_id),
              tf_exist (λ (v : ghost_lock_version),
                          tf_sep
                            (tf_atomic (gl_done k v))
                            (tf_variant N k v (tf_atomic False) P (tf_atomic False)))).
Local Definition tf_always_aux : seal (@tf_always_def). Proof. by eexists. Qed.
Definition tf_always := tf_always_aux.(unseal).
Local Definition tf_always_unseal :
  @tf_always = @tf_always_def := tf_always_aux.(seal_eq).
Global Arguments tf_always {SI Σ _}.

Class testG `{SI : indexT} Σ :=
  TestG {
      #[local] test_gmG :: ghost_mapG Σ nat bool;
    }.

Definition testΣ `{SI : indexT} : gFunctors :=
  #[(ghost_mapΣ nat bool)].

Global Instance subG_testΣ `{SI : indexT} {Σ} : subG testΣ Σ → testG Σ.
Proof. solve_inG. Qed.

Section test.
  Context `{SI : indexT} `{!gupdGS Σ, !testG Σ}.

  Definition tf_always_test N γ n b : tf (Σ:=Σ) :=
    tf_always_def N (tf_atomic (ghost_map_elem γ n DfracDiscarded b)).

End test.




Local Definition tf_always_def `{SI : indexT} `{Σ : gFunctors}
  (N : namespace) (P : tf) : iProp Σ :=
  ∃ κ v, gl_done κ v ∗ gl_variant N κ v False P False.
Local Definition gl_always_aux : seal (@gl_always_def). Proof. by eexists. Qed.
Definition gl_always := gl_always_aux.(unseal).
Local Definition gl_always_unseal :
  @gl_always = @gl_always_def := gl_always_aux.(seal_eq).
Global Arguments gl_always {SI Σ _}.

Local Ltac unfold_gl_always :=
  try rewrite !gl_always_unseal /gl_always_def.

Section proof.
  Context `{SI : indexT} `{!gupdGS Σ}.

  Global Instance gl_always_persistent N P : Persistent (gl_always N P).
  Proof. unfold_gl_always. apply _. Qed.

  Lemma gl_always_alloc_0 E Θ N (P : iProp Σ) :
    (▷ P) -∗ |={E:Θ}=>g gl_always N P.
  Proof.
    unfold_gl_always.
    iIntros "HP". iMod (gl_alloc_done_0 _ _ (λ _, 0%ordi) 0%M N 0 False P False with "HP") as "(%& _& _& _& #Gd& _& #GV& _)".
    iModIntro. eauto.
  Qed.

  Lemma gl_always_acc E N P :
    ↑N ⊆ E →
    gl_always N P ={E,E ∖ ↑N}=∗ (▷ P) ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_gl_always.
    iIntros (MASK) "(%&%& #Gd& #GV)". iMod (gl_variant_acc_done with "Gd GV") as "[H ACC]". 1: auto.
    iDestruct "H" as "[$ | H]".
    - iIntros "!> HP". iApply "ACC". iNext. iApply gl_variant_cases_unfold. iLeft; iRight. eauto.
    - iDestruct "H" as ">(_& %)". done.
  Qed.

End proof.



Local Definition heldT : Type := (bool).
Local Definition wonT : Type := (gl_id * bool).

Class ticket_lockG Σ :=
  TLockG {
      #[local] tlock_heldG :: ghost_mapG Σ Z heldT;
      #[local] tlock_wonG :: ghost_mapG Σ Z wonT;
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z heldT); (ghost_mapΣ Z wonT)].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

End proof.
