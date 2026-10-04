From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(** * Integers extended with [±∞], as heap_lang values, and the spec of their comparison *)

Module Int.

(** Integers extended with ±∞. *)
Inductive t := NegInf | Fin (z : Z) | PosInf.

Definition into_val (x : t) : val :=
  match x with
  | NegInf => (#0, #())%V
  | Fin z  => (#1, #z)%V
  | PosInf => (#2, #())%V
  end.

Definition lt_rel (x y : t) : Prop :=
  match x, y with
  | NegInf, NegInf => False
  | NegInf, _      => True
  | Fin _,  NegInf => False
  | Fin a,  Fin b  => (a < b)%Z
  | Fin _,  PosInf => True
  | PosInf, _      => False
  end.

Global Instance lt_rel_dec x y : Decision (lt_rel x y).
Proof. destruct x, y; simpl; apply _. Defined.

Definition lt : val :=
  λ: "a" "b",
    let: "ta" := Fst "a" in
    let: "tb" := Fst "b" in
    if: "ta" < "tb" then #true
    else if: "tb" < "ta" then #false
    else if: "ta" = #1 then Snd "a" < Snd "b"
    else #false.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_wp :=
    iFrame; iExists ∅, 0; iSplitR; [by eauto | iIntros "Hg Hfuel _ _ TE"; iModIntro; simpl].

  Ltac lwp_pures := repeat (lwp_pure; post_wp).

  Lemma lwp_lt :
    ⊢ ∃ m, ∀ x y i G C,
    l{{{ thread_expr i C (lt (into_val x) (into_val y)) ∗
         thP_kids i G ∗ oblP_fuels G m }}}
      lt (into_val x) (into_val y) @ i
    l{{{ RET #(bool_decide (lt_rel x y));
         thread_expr i C #(bool_decide (lt_rel x y)) ∗ thP_kids i G }}}.
  Proof.
    iExists 100. iIntros. iIntros (?) "!# (TE& Htg& Hfuel) HΦ".

    lwp_lam. post_wp.
    lwp_pures.

    destruct x as [|a|], y as [|b|]; simpl; lwp_pures; lwp_finish; iModIntro;
      rewrite ?bool_decide_decide;
      repeat destruct decide; (try by iApply "HΦ"; iFrame); lia.
  Qed.

End proof.

End Int.

#[global] Coercion Int.Fin : Z >-> Int.t.

Notation "-∞" := Int.NegInf.
Notation "+∞" := Int.PosInf.
