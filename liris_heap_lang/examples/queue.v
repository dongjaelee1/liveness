From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat mono_list.
From transfinite.base_logic.lib Require Import ghost_map.

From liris.heap_lang.examples Require Import ticket_lock.

(** References:
    Iron (https://gitlab.mpi-sws.org/iris/iron/-/blob/master/theories/heap_lang/lib/queue.v)
    Transfinite Iris (https://gitlab.mpi-sws.org/iris/transfinite/-/blob/master/theories/examples/termination/eventloop.v)
 *)

(** Use a ticket lock. *)
Definition new_queue : val :=
  λ: <>,
    let: "node" := ref NONE in
    let: "lock" := TicketLock.init #() in
    (ref "node", ref "node", "lock").

Definition enqueue : val :=
  λ: "q" "x",
    let: "lock" := Snd "q" in
    TicketLock.acquire "lock";;
    let: "tptr" := Snd (Fst "q") in
    let: "t" := !"tptr"  in
    let: "newt" := ref NONE in
    "t" <- SOME ("x", "newt");;
    "tptr" <- "newt";;
    TicketLock.release "lock".

Definition dequeue : val :=
  λ: "q",
    let: "lock" := Snd "q" in
    TicketLock.acquire "lock";;
    let: "hptr" := Fst (Fst "q") in
    let: "h" := !"hptr" in
    match: !"h" with
      NONE =>
        (* Empty queue. *)
        TicketLock.release "lock";;
        NONE
    | SOME "node" =>
        let: "newh" := Snd "node" in
        "hptr" <- "newh";;
        Free "h";;
        TicketLock.release "lock";;
        SOME (Fst "node")
    end.

Definition put_task : val :=
  λ: "q" "f" "a",
    enqueue "q" ("f", "a").

Definition run_task : val :=
  λ: "q",
    match: dequeue "q" with
      NONE => #()
    | SOME "fa" =>
        let: "f" := Fst "fa" in
        let: "a" := Snd "fa" in
        "f" "a"
    end.

(** A queue's spec with a liveness guarantee:
    any enqueued element is eventually dequeued.
 *)
Fixpoint queue_contents `{heapGS Σ} (lh lt : loc) (vs : list val) (φ : val → iProp Σ) : iProp Σ :=
  match vs with
  | [] => ⌜lh = lt⌝
  | v :: vs => ∃ l : loc, lh ↦ SOMEV (v, #l) ∗ φ v ∗ queue_contents l lt vs φ
end%I.

Definition local_version : Set := (positive * nat).

Variant queue_op : Set :=
  | op_enq (v : val)
  | op_deq (v : option val) (t : local_version)
.

Canonical Structure queue_opO : ofe := leibnizO queue_op.

(** The CMRA we need. *)
Class lqueueGpreS (Σ : gFunctors) : Set :=
  LqueueGpreS {
      lqueueGpreS_log : inG Σ (mono_listUR (queue_opO));
    }.

Class lqueueG Σ :=
  LqueueG {
      #[local] lqueue_inG :: lqueueGpreS Σ;
      #[local] lqueue_workerG :: ghost_mapG Σ positive (oid);
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z (oid)); (ghost_mapΣ Z (bool))].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

  Class lqueueGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    LqueueGpreS {
        lqueueGpreS_layer : inG Σ (gmap_viewR oid (agreeR (layerO)));
        lqueueGpreS_state : inG Σ (reservation_mapUR (mono_natUR));
        lqueueGpreS_fuel : inG Σ (reservation_mapUR bankUR);
        (* Keep track of the current owner of each obl, if an owner exists *)
        lqueueGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO obl_owner)));
      }.

  Class lqueueGS `{SI : indexT} (Σ : gFunctors) : Set :=
    LqueueG {
        lqueue_inG : lqueueGpreS Σ;
        layer_name : gname;
        state_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition lqueueΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (gmap_viewR oid (agreeR (layerO)));
      GFunctor (reservation_mapUR (mono_natUR));
      GFunctor (reservation_mapUR bankUR);
      GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO obl_owner)))
      ].

  Global Instance subG_lqueueΣ `{SI : indexT} {Σ} : subG (lqueueΣ) Σ → (lqueueGpreS Σ).
  Proof. solve_inG. Qed.


TODO

(**
  - lock invariant holds queue_contents
  - the problem: when a client enqueues a task,
    it needs to get some obligation that can eventually lead to
    fulfilling whatever obligation client specifies with the task.
    1. the queue makes progress and eventually the task is dequeued by some worker
    2. the worker runs the task, and the task requires some obligation to fulfill P as a precondition
    3. so the client waits on "eventually (eventually P)"
       - no one knows which worker will take the task, so a client waits for "eventually (# > my task #)"
         + no one worker thread is responsible for this, but concurrent workers have their local views
         + need to ensure that to dequeue a task, worker must also increase its view.
         + when the queue is empty, all task # until know should have been dequeued.
       - we need "always (task with # is done ∨ eventually (task with # starts ∧ eventually P))"

worker proto: always (∃ k, eventually k (queue is empty ∨ pop and run a task))

 *) 

Class queueG Σ := {
  queueG_inG :: inG Σ (prodR fracR (agreeR (listO valO)));
  queueG_dequeue_inG :: inG Σ (exclR unitO);
  queueG_enqueue_inG :: inG Σ (authR (optionUR (exclR locO)))
}.

Record queue_name := QueueName {
  queue_fcinv_name : fcinv_name;
  queue_own_name : gname;
  queue_dequeue_name : gname;
  queue_enqueue_name : gname;
}.

(*
Definition queueΣ : gFunctors := #[GFunctor queueCmra; GFunctor fracR;
  GFunctor (exclR unitO); fcinvΣ].

Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.
*)

Definition queue_own_def `{queueG Σ} (γ : queue_name)
    (q : Qp) (xs : list val) : ironProp Σ :=
  (<affine> ⎡ own (queue_own_name γ) (q, to_agree xs) ⎤)%I.
Definition queue_own_aux `{queueG Σ} : seal (queue_own_def). by eexists. Qed.
Definition queue_own `{queueG Σ} := unseal queue_own_aux.
Definition queue_own_eq `{queueG Σ} : queue_own = _ := seal_eq queue_own_aux.

Notation "γ ⤇{ q } xs" := (queue_own γ q xs)
  (at level 20, q at level 50, format "γ  ⤇{ q }  xs") : bi_scope.

Definition queue_inv `{heapGS Σ, queueG Σ} (γ : queue_name)
    (lhptr ltptr : loc) : ironProp Σ :=
  (∃ (lh lt : loc) (vs : list val),
    γ ⤇{1/2} vs ∗
    lhptr ↦{1/2} #lh ∗
    <affine> ⎡ own (queue_enqueue_name γ) (● (Excl' lt)) ⎤ ∗
    match vs with
    | [] => <affine> ⌜ lh = lt ⌝
    | v :: vs => ∃ l : loc,
       (lh ↦{1} SOMEV (v, #l)
        ∨ <affine> ⎡ own (queue_dequeue_name γ) (Excl ()) ⎤ ∗
        lh ↦{1/2} SOMEV (v, #l)) ∗
       queue_contents l lt vs
    end ∗
    lt ↦ NONEV)%I.

Definition is_queue `{heapGS Σ, queueG Σ} (N : namespace)
    (γ : queue_name) (q : val) : ironProp Σ :=
  (∃ lhptr ltptr : loc,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv N (queue_fcinv_name γ) (queue_inv γ lhptr ltptr))%I.

Definition queue_cancel_own `{heapGS Σ, queueG Σ}
    (γ : queue_name) (p : frac) : ironProp Σ :=
  fcinv_cancel_own (queue_fcinv_name γ) p.

Definition enqueue_handle `{heapGS Σ, queueG Σ}
    (γ : queue_name) (q : val) : ironProp Σ :=
  (∃ lhptr ltptr lt : loc,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv_own (queue_fcinv_name γ) (1/2) ∗
    <affine> ⎡ own (queue_enqueue_name γ) (◯ (Excl' lt)) ⎤ ∗
    ltptr ↦ #lt)%I.

Definition dequeue_handle `{heapGS Σ, queueG Σ}
    (γ: queue_name) (q : val) : ironProp Σ :=
  (∃ (lhptr ltptr : loc) v,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv_own (queue_fcinv_name γ) (1/2) ∗
    lhptr ↦{1/2} v ∗
    <affine> ⎡ own (queue_dequeue_name γ) (Excl ()) ⎤)%I.

Section queue_own.
  Context `{!queueG Σ}.

  Global Instance queue_own_affine γ q vs : Affine (queue_own γ q vs).
  Proof. rewrite queue_own_eq. apply _. Qed.
  Global Instance queue_own_uniform `{heapGS Σ} γ q vs : Uniform (queue_own γ q vs).
  Proof. apply affine_uniform, _. Qed.

  Global Instance queue_own_fractional γ vs : Fractional (λ q, queue_own γ q vs).
  Proof.
    rewrite queue_own_eq /queue_own_def=> p q; iSplit.
    - iIntros "[$$]".
    - iIntros "[H1 H2]". by iSplitL "H1".
  Qed.
  Global Instance makeElem_as_fractional γ vs q :
    AsFractional (γ ⤇{q} vs) (λ q, queue_own γ q vs) q.
  Proof. split. done. apply _. Qed.

  Global Instance queue_own_timeless γ p vs : Timeless (γ ⤇{p} vs).
  Proof. rewrite queue_own_eq. apply fracPred_at_timeless_alt. apply _. Qed.

  Lemma queue_own_agree γ p q vs ws : γ ⤇{p} vs -∗ γ ⤇{q} ws -∗ ⌜vs = ws⌝.
  Proof.
    rewrite queue_own_eq /queue_own_def; iIntros "H1 H2".
    by iCombine "H1 H2" gives %[_ ?%to_agree_op_inv_L].
  Qed.
  Lemma queue_own_update γ vs vs' : γ ⤇{1} vs ==∗ γ ⤇{1} vs'.
  Proof.
    rewrite queue_own_eq /queue_own_def. iIntros "H".
    iMod (own_update with "H") as "$"; last by auto.
    by apply cmra_update_exclusive.
  Qed.
  Lemma queue_own_update_2 γ vs vs' vs'' :
    γ ⤇{1/2} vs -∗ γ ⤇{1/2} vs' ==∗ γ ⤇{1} vs''.
  Proof.
    iIntros "H1 H2". iDestruct (queue_own_agree with "H1 H2") as %->.
    iCombine "H1 H2" as "H". by iApply queue_own_update.
  Qed.
End queue_own.

Section queue_spec.
  Context `{!heapGS Σ, !queueG Σ} (N : namespace).
  Implicit Types E : coPset.
  Implicit Types P Q : ironProp Σ.

  Instance queue_contents_uniform lh lt vs : Uniform (queue_contents lh lt vs).
  Proof. revert lh. induction vs; apply _. Qed.
  Instance queue_inv_uniform γ lhptr ltptr :
    Uniform (queue_inv γ lhptr ltptr).
  Proof. repeat (apply exist_uniform=> ?); case_match; apply _. Qed.

  Global Instance is_queue_persistent γ q : Persistent (is_queue N γ q).
  Proof. apply _. Qed.
  Global Instance is_queue_affine γ q : Affine (is_queue N γ q).
  Proof. apply _. Qed.
  Global Instance is_queue_uniform γ q : Uniform (is_queue N γ q).
  Proof. apply affine_uniform, _. Qed.

  Global Instance enqueue_handle_uniform γ q : Uniform (enqueue_handle γ q).
  Proof. apply _. Qed.
  Global Instance dequeue_handle_uniform γ q : Uniform (dequeue_handle γ q).
  Proof. apply _. Qed.

  Lemma new_queue_spec E :
    ↑N ⊆ E →
    {{{ emp }}}
      new_queue #() @ E
    {{{ q γ, RET q; <affine> is_queue N γ q ∗ queue_cancel_own γ 1 ∗
          enqueue_handle γ q ∗ dequeue_handle γ q ∗ γ ⤇{1/2} [] }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". iApply iron_wp_fupd. wp_lam. wp_alloc l as "Hl"; wp_let.
    wp_alloc ltptr as "Hltptr". wp_alloc lhptr as "Hlhptr". 
    iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
    iMod (own_alloc (1%Qp, to_agree [])) as (γ) "[Hγ Hγ']"; first done.
    iMod (own_alloc (Excl ())) as (γd) "Hγd"; first done.
    iMod (own_alloc (● (Excl' l) ⋅ ◯ (Excl' l))) as (γe) "[Hγe Hγe']";
      first by apply auth_both_valid_discrete.
    iMod (fcinv_alloc_named _ N (λ γinv, queue_inv (QueueName γinv γ γd γe) lhptr ltptr)
      with "[Hlhptr' Hγ' Hl Hγe]") as (γinv) "(#? & Hγc & [Hγinv Hγinv'])".
    { iIntros "!>" (γinv).
      iExists l, l, []. rewrite queue_own_eq /=. iFrame; auto. }
    wp_pures. iModIntro. iApply ("HΦ" $! _ (QueueName γinv γ γd γe)). iSplitR.
    { iExists lhptr, ltptr; auto. }
    iFrame "Hγc". iSplitL "Hγinv Hltptr Hγe'".
    { iExists lhptr, ltptr, l. iFrame; auto. }
    iSplitL "Hγinv' Hlhptr Hγd".
    { iExists lhptr, ltptr. iFrame; auto. }
    by rewrite queue_own_eq.
  Qed.

  Lemma dequeue_spec E Φ q γ :
    ↑N ⊆ E →
    is_queue N γ q -∗ dequeue_handle γ q -∗
    (∀ vs, γ ⤇{1/2} vs ={E∖↑N}=∗
       match vs with
       | [] => γ ⤇{1/2} [] ∗ ▷ (dequeue_handle γ q -∗ Φ NONEV)
       | v :: vs' => γ ⤇{1/2} vs' ∗ ▷ (dequeue_handle γ q -∗ Φ (SOMEV v))
       end) -∗
    WP dequeue q @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hh Hupd".
    iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Hh" as (?? l ?%eq_sym) "(Hγinv & Hlhptr & Hγd)"; simplify_eq.
    wp_lam. wp_load. wp_let. wp_bind (! _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh lt vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %->; simpl.
    destruct vs as [|v vs'].
    { iDestruct "Hlist" as ">->".
      wp_load. iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
      iMod ("Hclose" with "[Hvs Hlhptr' Hlt Hγe]") as "_".
      { iExists lt, lt, []. iFrame; auto. }
      iModIntro. wp_pures. iApply "HΦ". iExists lhptr, ltptr. eauto with iFrame. }
    iDestruct "Hlist" as (l') "[>[[Hlh Hlh']|[Hγd' ?]] Hlist]"; last first.
    { iCombine "Hγd Hγd'" gives %[]. }
    wp_load.
    iMod ("Hclose" with "[Hvs Hlhptr' Hlh' Hγd Hlt Hlist Hγe]") as "_".
    { iExists lh, lt, (v :: vs'). iNext. iFrame "Hvs Hlhptr' Hlt Hγe".
      iExists l'. auto with iFrame. }
    clear vs'. iModIntro. wp_match. wp_proj. wp_let. wp_bind (_ <- _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh' lt' vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %?%eq_sym; simplify_eq.
    destruct vs as [|v' vs'].
    { iDestruct "Hlist" as ">->".
      iDestruct (pointsto_agree with "Hlh Hlt") as %[=]. }
    iDestruct "Hlist" as (lh') "[>[Hlh'|[Hγd Hlh']] Hlist]".
    { by iCombine "Hlh Hlh'" gives %[]. }
    iDestruct (pointsto_agree with "Hlh Hlh'") as %?; simplify_eq.
    iCombine "Hlh Hlh'" as "Hlh"; iCombine "Hlhptr Hlhptr'" as "Hlhptr".
    wp_store. iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
    iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
    iMod ("Hclose" with "[Hvs Hlhptr' Hlt Hγe Hlist]") as "_".
    { iExists lh', lt', vs'. iNext. iFrame "Hvs Hlhptr' Hlt Hγe".
      destruct vs' as [|v'' vs'']=> //=.
      iDestruct "Hlist" as (l) "[Hlh Hlist]". auto with iFrame. }
    iModIntro. wp_seq. wp_apply (iron_wp_free with "Hlh"). iIntros "_"; wp_seq.
    wp_pures. iApply "HΦ". iExists lhptr, ltptr. eauto with iFrame.
  Qed.

  Lemma enqueue_spec E Φ q v γ :
    ↑N ⊆ E →
    is_queue N γ q -∗ enqueue_handle γ q -∗
    (∀ vs,
      γ ⤇{1/2} vs ={E∖↑N}=∗
      γ ⤇{1/2} (vs ++ [v]) ∗ ▷ (enqueue_handle γ q -∗ Φ #())) -∗
    WP enqueue q v @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hh Hupd". iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Hh" as (?? lt ?%eq_sym)
      "(Hγinv & Hγe' & Hltptr)"; simplify_eq.
    wp_lam. wp_load. wp_alloc ltn as "Hltn"; wp_let. wp_pures. wp_bind (_ <- _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh lt' vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt')".
    iCombine "Hγe Hγe'"
      gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hγe Hγe'") as "[Hγe Hγe']".
    { by apply auth_update, option_local_update,
        (exclusive_local_update _ (Excl ltn)). }
    wp_store. iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
    iMod ("Hclose" with "[Hvs Hlhptr' Hγe Hlist Hlt' Hltn]") as "_".
    { iNext. iExists lh, ltn, (vs ++ [v]). iFrame "Hvs Hlhptr' Hγe Hltn".
      destruct vs as [|v' vs]; simpl.
      { iDestruct "Hlist" as "->". eauto with iFrame. }
      iDestruct "Hlist" as (l) "[Hlh Hlist]". iExists l; iFrame "Hlh".
      iInduction vs as [|w ws] "IH" forall (l); simpl.
      { iDestruct "Hlist" as "->". eauto with iFrame. }
      iDestruct "Hlist" as (l') "[Hl Hlist]". iExists l'. iFrame "Hl".
      by iApply ("IH" with "[$]"). }
    iModIntro. wp_seq. wp_store. iApply "HΦ".
    iExists lhptr, ltptr, ltn. iFrame; auto.
  Qed.

  Lemma delete_spec E Φ q γ :
    ↑N ⊆ E →
    is_queue N γ q -∗
    queue_cancel_own γ 1 -∗
    enqueue_handle γ q -∗ dequeue_handle γ q -∗
    γ ⤇{1/2} [] -∗
    (γ ⤇{1} [] ={E}=∗ ▷ Φ #()) -∗
    WP delete q @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hγc Heh Hdh Hvs HΦ". iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Heh" as (?? lt ?%eq_sym) "(Hγinv & Hγe' & Hltptr)"; simplify_eq.
    iDestruct "Hdh" as (?? v' ?%eq_sym) "(Hγinv' & Hlhptr & Hγd)"; simplify_eq.
    iMod (fcinv_cancel with "[$] Hγc [$Hγinv $Hγinv']") as "H"; first done.
    iDestruct "H" as (lh lt' vs) "(>Hvs' & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iCombine "Hγe Hγe'"
      gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %?; simplify_eq.
    iCombine "Hlhptr Hlhptr'" as "Hlhptr".
    iDestruct (queue_own_agree with "Hvs Hvs'") as %<-; iCombine "Hvs Hvs'" as "Hvs".
    iDestruct "Hlist" as ">->".
    iMod ("HΦ" with "Hvs") as "HQ".
    wp_lam. wp_load. by do 3 wp_free.
  Qed.

  Lemma delete_all_spec E Φ Ψ (f : val) q γ (vs : list val) :
    ↑N ⊆ E →
    is_queue N γ q -∗
    queue_cancel_own γ 1 -∗
    enqueue_handle γ q -∗ dequeue_handle γ q -∗
    γ ⤇{1/2} vs -∗
    ▷ ([∗ list] v ∈ vs, WP f (of_val v) @ E {{ _, Ψ v }}) -∗
    ▷ (γ ⤇{1} [] -∗ ([∗ list] v ∈ vs, Ψ v) ={E}=∗ Φ #()) -∗
    WP delete_all f q @ E {{ Φ }}.
  Proof.
    iIntros (?) "#Hq Hγc Heh Hdh Hvs Hf HΦ".
    iInduction vs as [|v vs] "IH"; wp_lam; wp_pures.
    - wp_apply (dequeue_spec _ with "Hq Hdh"); first done.
      iIntros (vs) "Hvs'". iDestruct (queue_own_agree with "Hvs' Hvs") as %->.
      iIntros "!> {$Hvs'} !> Hdh /=". wp_let. wp_match.
      wp_apply (delete_spec with "Hq Hγc Heh Hdh Hvs"); first done.
      iIntros "Hvs". iMod ("HΦ" with "Hvs [//]") as "$"; auto.
    - iDestruct "Hf" as "[Hfv Hf]".
      wp_apply (dequeue_spec _ with "Hq Hdh"); first done.
      iIntros (vs') "Hvs'". iDestruct (queue_own_agree with "Hvs' Hvs") as %->.
      iMod (queue_own_update_2 _ _ _ vs with "Hvs Hvs'") as "[Hvs $]".
      iIntros "!> !> Hdh". wp_let. wp_match.
      wp_apply (iron_wp_wand with "Hfv"); iIntros (w) "HΨ"; wp_seq.
      iApply ("IH" with "Hγc Heh Hdh Hvs Hf"). iNext. iIntros "Hvs HΨs".
      iApply ("HΦ" with "[$]"). iFrame.
  Qed.
End queue_spec.
