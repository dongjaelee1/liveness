From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export opreds.
From iris.prelude Require Import options.

(** * Depth arithmetic in natural-number form

  Specifications charge one unit of carrier fuel at depth [d + 1], where [d]
  bounds the depth of the callees; a proof then converts that unit to
  whatever it needs one depth down. The lemmas of [opreds] state this with
  ordinal depths; these are the forms used by the case studies, where depths
  are naturals. *)

Section depth.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Lemma crP_dfuel_depth_extend_nat k ℓ (n : nat) μ :
    crP_dfuel k ℓ (S n) 1 ⊢ |==> crP_dfuel k ℓ n μ.
  Proof. apply crP_dfuel_depth_extend. apply ordArith.lt_from_nat. lia. Qed.

  Lemma crP_dfuel_depth_extend_nat_set K ℓ (n : nat) μ :
    ([∗ set] k ∈ K, crP_dfuel k ℓ (S n) 1) ⊢ |==> ([∗ set] k ∈ K, crP_dfuel k ℓ n μ).
  Proof. apply crP_dfuel_depth_extend_set. apply ordArith.lt_from_nat. lia. Qed.

  (** Lower the depth without converting: a unit at depth [d] is also a unit
      at any smaller depth (take [μ := 1]). *)
  Lemma crP_dfuel_depth_mon_nat k ℓ (n m : nat) :
    (n ≤ m)%nat →
    crP_dfuel k ℓ m 1 ⊢ |==> crP_dfuel k ℓ n 1.
  Proof.
    intros Hle. apply Nat.lt_eq_cases in Hle. destruct Hle as [Hlt | ->].
    - apply crP_dfuel_depth_extend. apply ordArith.lt_from_nat. lia.
    - eauto.
  Qed.

  Lemma crP_dfuel_depth_mon_nat_set K ℓ (n m : nat) :
    (n ≤ m)%nat →
    ([∗ set] k ∈ K, crP_dfuel k ℓ m 1) ⊢ |==> ([∗ set] k ∈ K, crP_dfuel k ℓ n 1).
  Proof.
    intros. rewrite -big_sepS_bupd. apply big_sepS_mono. intros. by apply crP_dfuel_depth_mon_nat.
  Qed.

End depth.
