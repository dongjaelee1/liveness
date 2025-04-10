From iris.algebra Require Import gmap_view mono_list gmap gset.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import language.
From liveness Require Export osat sched_fair_interp obligation_fuel.
From Ordinal Require Import Ordinal.

(** Enable thread local management of obligations.
    Also connects scheduler fairness with obligations to enable liveness induction. *)
Module threadoblGS.
  Class threadoblGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblGpreS {
        threadoblGpreS_state : inG Σ (gmap_viewR thread_id (mono_listUR obl_id));
        threadoblGpreS_live : inG Σ (gmap_viewR thread_id (agreeR (list obl_id)));
      }.

  Class threadoblGS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblG {
        threadobl_inG : threadoblGpreS Σ;
        state_name : gname;
        live_name : gname;
      }.

  Definition threadoblΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (gmap_viewTRF thread_id (mono_listUR obl_id));
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
Local Existing Instances ofuelGS.ofuel_inG ofuelGS.ofuelGpreS_state.

Definition toS_snapshot `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  own state_name (gmap_view_frag i DfracDiscarded (◯ML l)).
Global Typeclasses Opaque toS_snapshot.
Global Instance: Params (@toS_snapshot) 4 := {}.

Definition toL_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  own live_name (gmap_view_frag i (DfracOwn 1) (to_agree l)).
Global Typeclasses Opaque toL_thread.
Global Instance: Params (@toL_thread) 4 := {}.

(* thread fork cases: sched fuel for new threads? *)
Definition toI `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} {Π} {Σ}
  `{@osatGS.osatGS SI Ord.t _ _ _ _ Π Σ} `{@schedfairGS.schedfairGS SI A _ _ _ WF Σ} `{@ofuelGS.ofuelGS SI Σ} `{!threadoblGS Σ}
  (γ : gmap thread_id (list obl_id))
  : iProp Σ :=
  locked
    (∃ (Ψ : gmap thread_id (list obl_id)),
       (⌜map_Forall2 (λ _ l1 l2, l1 ⊆ l2) γ Ψ⌝) ∗
       (own state_name (gmap_view_auth (DfracOwn 1) ((mono_list_auth (DfracOwn 1)) <$> Ψ))) ∗
       (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
       ([∗ map] i ↦ W ∈ Ψ,
          (sfS_exec i (1/2) ∗
           ∃ (f : A), sfS_fuel_bound i f 1 ∗
                      (∃ L, ⌜γ !! i = Some L⌝ ∗
                            ([∗ list] k ∈ L, oblS_live k 1 ∗ ∃ a, ⌜(Ord.from_wf (WFOrderedCM.lt_wf) f <= a)%ord⌝ ∗ ofuelS_fuel k a) ∗
                            ([∗ list] k ∈ W, ⌜k ∈ L⌝ ∨ oblS_done k)
          ))
          ∨
            (sfS_term i ∗ toL_thread i [] ∗ [∗ list] k ∈ W, oblS_done k)))%I.
