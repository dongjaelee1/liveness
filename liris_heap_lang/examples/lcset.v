From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.

From liris.heap_lang.examples Require Import ticket_lock extended_int.

Module LockCouplingSet.
  (** https://www.cs.toronto.edu/~azadeh/resources/papers/tada-live.pdf
      Fig 27 and 28

      Each node is a contiguous block of three cells:
        offset 0: lock      (a [TicketLock] value)
        offset 1: value     (NONE for the tail sentinel = +∞, SOME z otherwise)
        offset 2: next      (location of the successor; unused on the tail)

      The set is represented by a pointer to its head sentinel.  The head's
      value is never compared, so we pick an arbitrary placeholder. *)

  Definition getLock : val := λ: "x", !("x" +ₗ #0).
  Definition getVal : val := λ: "x", !("x" +ₗ #1).
  Definition nextRef : val := λ: "x", "x" +ₗ #2.

  Definition lockNode : val :=
    λ: "x", TicketLock.acquire (getLock "x").

  Definition unlockNode : val :=
    λ: "x", TicketLock.release (getLock "x").

  Definition newNode : val :=
    λ: "value" "next",
      let: "lk" := TicketLock.init #() in
      ref ("lk", "value", "next").

  Definition makeSet : val :=
    λ: <>,
      let: "tail" := newNode (Int.into_val +∞) #(Loc 0) in
      let: "head" := newNode (Int.into_val -∞) "tail" in
      "head".

  (** Traverse the list hand-over-hand, starting from a locked [curr], until
      we find a successor [next] with value ≥ v.  Returns the locked pair
      (curr, next) where curr.next = next. *)
  Definition locate : val :=
    λ: "x" "e",
      lockNode "x";;
      (rec: "loop" "curr" :=
         let: "next" := !(nextRef "curr") in
         lockNode "next";;
         if: Int.lt (getVal "next") "e" then
           unlockNode "curr";;
           "locate" "next" "e"
         else ("curr", "next")) "x".

  Definition member : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      let: "contains" := ~ (Int.lt "v" (getVal "next")) in
      unlockNode "curr";;
      unlockNode "next";;
      "contains".

  Definition add : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      (if: Int.lt "v" (getVal "next") then
         nextRef "curr" <- newNode "v" "next"
       else #());;
      unlockNode "curr";;
      unlockNode "next".

  Definition remove : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      (if: Int.lt "v" (getVal "next") then #() else
         nextRef "curr" <- !(nextRef "next"));;
      unlockNode "curr";;
      unlockNode "next".

End LockCouplingSet.

Section ticket_lock.
  Context `{!heapGS Σ} `{!ticket_lockG Σ}.
  (* FIXME: extremely messy. *)
  Global Instance is_fair_lock_ne lk γlk ℓ : NonExpansive (is_fair_lock lk γlk ℓ).
  Proof.
    intros ??. intros.
    rewrite /is_fair_lock.
    solve_proper_prepare.
    clean_flip.
    do 5 f_equiv.
    f_equiv.
    rewrite /ticket_lock.lock_proto.
    rewrite /tf_eventually.
    setoid_rewrite tf_until_logic.
    setoid_rewrite tf_fulfilled_unfold.

    do 10 f_equiv.
    do 4 f_equiv.
    f_equiv.
    2:{ repeat f_equiv; assumption. }
    do 7 f_equiv.

    unfold_opreds.
    f_equiv.
    rewrite /oblG_inv.
    f_contractive.
    rewrite /oblG_variant.
    f_equiv.
    rewrite /oblG_assigned.
    f_equiv.
    { f_equiv. tf_red. f_equiv. eapply dist_lt; last eassumption. done. }
    do 15 f_equiv.
    Transparent tf_intuit. simpl. Opaque tf_intuit.
    f_equiv.
  Qed.

End ticket_lock.

Class lcsG Σ :=
  {
    lcs_lockG :: ticket_lockG Σ;
  }.

Record lcs_names :=
  {
    set_gn : gname;
  }.


Section proof.
  Context `{!heapGS Σ} `{!lcsG Σ}.

  Axiom ℓ : ord.t.

  Definition is_node_pre
      (is_node : loc -d> lcs_names -d> iPropO Σ) :
      loc -d> lcs_names -d> iPropO Σ :=
    λ n γ,
      (∃ lk γlk v,
          (n +ₗ 0) ↦□ lk ∗
          (n +ₗ 1) ↦□ (Int.into_val v) ∗
          is_fair_lock lk γlk ℓ (
              ∃ (next : loc),
                (n +ₗ 2) ↦ #next ∗ ▷ is_node next γ
      ))%I.

  Ltac solve_contractive :=
    solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv | (eapply dist_lt; last eassumption)]).

  Local Instance is_node_pre_contractive : Contractive is_node_pre.
  Proof.
    solve_contractive.
  Qed.

  Definition is_node : loc → lcs_names → iProp Σ := fixpoint is_node_pre.

  Lemma is_node_unfold n γ : is_node n γ ⊣⊢ is_node_pre is_node n γ.
  Proof. apply (fixpoint_unfold is_node_pre n γ). Qed.

  Definition is_lcsSet (root : loc) γ : iProp Σ :=
    is_node root γ.

  (* Lemma wp_makeSet : *)
  (*   l{{{ True }}} *)
  (*    makeSet *)
  (*   l{{{ RET #(); True }}}. *)
End proof.
