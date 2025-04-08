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
        (* threadoblGpreS_state : inG Σ (gmap_viewR thread_id (gmap_viewR obl_id unitUR)); *)
        (* threadoblGpreS_live : inG Σ (gmap_viewR thread_id (gsetUR obl_id)); *)
        (* threadoblGpreS_state : inG Σ (gmap_viewR thread_id (gset_disjUR obl_id)); *)
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
  (* #[GFunctor (gmap_viewTRF thread_id (gset_disjUR obl_id)) *)

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
Definition toI `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{obl_ps} {Σ}
  `{@osatGS.osatGS SI Ord.t _ _ _ _ _ Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{@ofuelGS.ofuelGS SI Σ} `{!threadoblGS Σ}
  : iProp Σ :=
  locked
    (∃ (Ψ γ : gmap thread_id (list obl_id)),
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

(* Definition sfofI `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{obl_ps} {Σ} *)
(*   `{!threadoblGS Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{@ofuelGS.ofuelGS SI Σ} *)
(*   (ϕ : gmap thread_id (option A)) (O : obl_states) : iProp Σ := *)
(*   locked *)
(*     (∃ (Ψ : gmap thread_id (gset obl_id)), *)
(*         (⌜dom Ψ ≡ dom ϕ⌝) ∗ *)
(*         (* allow some obligations to be not tied to any thread or be tied to many threads. *) *)
(*         (⌜map_Forall (λ _ K, K ⊆ dom O) Ψ⌝) ∗ *)
(*         (* (⌜map_fold (λ _ k K, k ∪ K) ∅ Ψ ≡ dom O⌝) ∗ *) *)
(*         (own state_name (gmap_view_auth (DfracOwn 1) Ψ)) ∗ *)
(*         (* (own state_name (gmap_view_auth (DfracOwn 1) (GSet <$> Ψ))) *) *)
(*         ([∗ map] i ↦ oF ∈ ϕ, *)
(*            match oF with *)
(*            | Some _ => *)
(*                (sfS_exec i (1/2) ∗ *)
(*                 ∃ (f : A), sfS_fuel_bound i f 1 ∗ *)
(*                            ∃ K, ⌜Ψ !! i = Some K⌝ ∗ *)
(*                                 ([∗ set] k ∈ K, *)
(*                                    ∃ o, ⌜(Ord.from_wf (WFOrderedCM.lt_wf) f <= o)%ord⌝ ∗ *)
(*                                         ofuelS_fuel k o) *)
(*                ) *)
(*            | None => *)
(*                ((* return frag *) sfS_term i) *)
(*            end *)
(*         ) *)
(*     )%I. *)

gset_disj_valid_op:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y : gset K),
    ✓ (GSet X ⋅ GSet Y) ↔ X ## Y
gmap_view_both_valid:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {SI : indexT} 
    {V : cmra} (m : gmap K V) (dp : dfrac) (k : K) (v : V),
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k (DfracOwn 1) v) ↔ ✓ dp ∧ ✓ v ∧ m !! k ≡ Some v
gmap_view_replace:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {SI : indexT} 
    {V : cmra} (m : gmap K V) (k : K) (v v' : V),
    ✓ v'
    → gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
      gmap_view_auth (DfracOwn 1) (<[k:=v']> m) ⋅ gmap_view_frag k (DfracOwn 1) v'
gmap_view_alloc:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {SI : indexT} 
    {V : cmra} (m : gmap K V) (k : K) (dq : dfrac) (v : V),
    m !! k = None
    → ✓ dq
      → ✓ v
        → gmap_view_auth (DfracOwn 1) m ~~>
          gmap_view_auth (DfracOwn 1) (<[k:=v]> m) ⋅ gmap_view_frag k dq v

Definition osat `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{obl_ps} `{!osatGS Σ}
  (O : obl_states) : iProp Σ :=
  locked
    (∃ (Obls : gmap positive (obl_state * (obl_ps_prop * iProp Σ))%type),
        (⌜O = fst <$> Obls⌝) ∗
        (own goal_name
           (gmap_view_auth (DfracOwn 1)
              ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> (snd <$> Obls)))) ∗
        ([∗ map] i ↦ oQ ∈ Obls,
           match oQ with
           | (obl_init a, _) =>
               (∃ a', ⌜leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_idle i 1%Qp ∗ oblS_live i 1)
           | (obl_live a, _) =>
               (∃ a', ⌜leR a' a⌝ ∗ oblS_bound i a' ∗ oblS_active_auth i ∗ oblS_live i 1)
           | (obl_done P1, (P2, R)) =>
               (⌜P1 = P2⌝ ∗ ▷ R ∗ oblS_active_auth i ∗ oblS_done_auth i)
           end)
    )%I.
Definition schedfairI `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ}
  (ϕ : gmap thread_id (option A)) : iProp Σ :=
  locked
    (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom ϕ))) ∗
     [∗ map] i ↦ oF ∈ ϕ,
       match oF with
       | Some f =>
           (∃ f', ⌜leR f f'⌝ ∗ sfS_fuel_credit i f' ∗ sfS_exec i (1/2)%Qp)
       | None =>
           (∃ f', sfS_fuel_bound i f' 1 ∗ sfS_term_auth i)
       end
    )%I.

Definition ofuelI `{SI : indexT} `{obl_ps} `{!ofuelGS Σ}
  (c : Ord.t) (O : obl_states) : iProp Σ :=
  locked
    (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom O))) ∗
     [∗ map] i ↦ o ∈ O,
       match o with
       | obl_init a =>
           (∃ a', ⌜ (a <= a')%ord ⌝ ∗ ofuelS_fuel i (c × a')%ord)
       | obl_live a =>
           (∃ a', ⌜ (a <= a')%ord ⌝ ∗ ofuelS_fuel i (c × a')%ord)
       | obl_done _ =>
           (⌜ True ⌝)
       end
    )%I.
