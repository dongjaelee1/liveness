From iris.algebra Require Import gmap_view reservation_map mono_list mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Export osat sched_fair_interp.
From liveness Require Import language ordinal_wfocm.

(** Enable thread local management of obligations.
    Also connects scheduler fairness with obligations to enable liveness induction. *)
Module threadoblGS.
  Class threadoblGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblGpreS {
        threadoblGpreS_state : inG Σ (reservation_mapUR (mono_listUR obl_id));
        (* threadoblGpreS_state : inG Σ (gmap_viewR thread_id (mono_listUR obl_id)); *)
        threadoblGpreS_live : inG Σ (gmap_viewR thread_id (agreeR (list obl_id)));
      }.

  Class threadoblGS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblG {
        threadobl_inG : threadoblGpreS Σ;
        state_name : gname;
        live_name : gname;
      }.

  Definition threadoblΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (mono_listUR obl_id));
      (* GFunctor (gmap_viewTRF thread_id (mono_listUR obl_id)); *)
      GFunctor (gmap_viewTRF thread_id (agreeTRF (listO obl_id)))
      ].

  Global Instance subG_threadoblΣ `{SI : indexT} {Σ} : subG threadoblΣ Σ → (threadoblGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End threadoblGS.
Import threadoblGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances threadobl_inG threadoblGpreS_state threadoblGpreS_live.
Local Existing Instances osatGS.osat_inG osatGS.osatGpreS_goal osatGS.osatGpreS_state.
Local Existing Instances schedfairGS.schedfair_inG schedfairGS.schedfairGpreS_state.

(* list l logs every obligation ever allocated to thread i *)
Definition toS_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  own state_name (reservation_map_data i (●ML l)).
Global Typeclasses Opaque toS_thread.
Global Instance: Params (@toS_thread) 4 := {}.

(* list l is a snapshot of the log of obligations ever allocated to thread i *)
Definition toS_snapshot `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  own state_name (reservation_map_data i (◯ML l)).
Global Typeclasses Opaque toS_snapshot.
Global Instance: Params (@toS_snapshot) 4 := {}.

Definition toS_assigned `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (κ : obl_id) : iProp Σ :=
  (∃ l, ⌜ κ ∈ l ⌝ ∗ toS_snapshot i l)%I.
Global Typeclasses Opaque toS_assigned.
Global Instance: Params (@toS_assigned) 4 := {}.

(* thread i is currently executing, with live obligations l. *)
Definition toL_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  own live_name (gmap_view_frag i (DfracOwn 1) (to_agree l)).
Global Typeclasses Opaque toL_thread.
Global Instance: Params (@toL_thread) 4 := {}.

(* thread i terminated, with no live obligation []. *)
Definition toL_term `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) : iProp Σ :=
  own live_name (gmap_view_frag i DfracDiscarded (to_agree [])).
Global Typeclasses Opaque toL_term.
Global Instance: Params (@toL_term) 4 := {}.

(* thread fork cases: sched fuel for new threads? *)
Definition toI `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} {ps} {Σ}
  `{@osatGS.osatGS SI Ord.t _ ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ}
  `{!threadoblGS Σ}
  (γ : gmap thread_id (list obl_id))
  : iProp Σ :=
  locked
    (∃ (Ψ : gmap thread_id (list obl_id)),
        (⌜ map_Forall2 (λ _ l1 l2, l1 ⊆ l2) γ Ψ ⌝) ∗
        (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗
        (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
        ([∗ map] i ↦ W ∈ Ψ,
           toS_thread i W ∗
           ∃ (f : A), sfS_fuel_bound i f 1 ∗
                      (∃ L, ⌜ γ !! i = Some L ⌝ ∗
                            ([∗ list] k ∈ W, ⌜k ∈ L⌝ ∨ oblS_done k) ∗
                            ([∗ list] k ∈ L,
                               oblS_live k (1/2/2) ∗
                               ((oblS_idle k (1/2/2) ∗ oblS_credit k (Ord.from_wf_set (WFOCM.lt_wf)))
                                ∨ (oblS_active k ∗ ∃ a, ⌜ (Ord.from_wf (WFOCM.lt_wf) f <= a)%ord ⌝ ∗ oblS_credit k a)))
                      )
        )
    )%I.

Definition oftI `{SI : indexT} {T : Type} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class obl_ps (T * A)%type} `{!threadoblGS Σ}
  (Ω : obl_states) (δ : gmap thread_id A) (γ : gmap thread_id (list obl_id)) : iProp Σ :=
  (([∗ set] κ ∈ dom Ω, ∃ i, toS_assigned i κ) ∗
   ([∗ map] f; L ∈ δ; γ, [∗ list] k ∈ L, ⌜ ∃ c, Ω !! k = Some (obl_live c) ∧ leR f c.2 ⌝))%I.
