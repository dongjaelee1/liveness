From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.base_logic Require Import osat.

(** The ghost state for thread obligations *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_state : inG Σ (reservation_mapUR (gmap_viewR obl_id (agreeR (leibnizO bool))));
        othreadGpreS_thread : inG Σ (gmap_viewR positive (gset_disjUR obl_id));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        state_name : gname;
        thread_name : gname;
        exec_name : gname;
      }.

  Definition othreadΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id (agreeR (leibnizO bool))));
      GFunctor (gmap_viewR positive (gset_disjUR obl_id));
      GFunctor (reservation_mapUR mono_natUR)
      ].

  Global Instance subG_othreadΣ `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (othreadGpreS Σ).
  Proof. solve_inG. Qed.

End othreadGS.
Import othreadGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances othread_inG othreadGpreS_state othreadGpreS_thread othreadGpreS_exec.

(* States: thread currently has this obl or not *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : obl_id) (b : bool) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) (to_agree $ b))).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 5 := {}.

(* Thread: live obligations that this thread knows, also fix to empty when thread terminates *)
Definition othreadG_knows `{SI : indexT} `{!othreadGS Σ} (i : positive) (Θ : gset obl_id) (q : Qp) : iProp Σ :=
  own thread_name (gmap_view_frag i (DfracOwn q) (GSet Θ)).
Global Typeclasses Opaque othreadG_knows.
Global Instance: Params (@othreadG_knows) 4 := {}.

(* Exec: tracks whether thread is executing or terminated *)
Definition othreadG_exec `{SI : indexT} `{!othreadGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN{#q} 0)).
Global Typeclasses Opaque othreadG_exec.
Global Instance: Params (@othreadG_exec) 4 := {}.

Definition othreadG_term_auth `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN 1)).
Global Typeclasses Opaque othreadG_term_auth.
Global Instance: Params (@othreadG_term_auth) 4 := {}.

Definition othreadG_term `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (◯MN 1)).
Global Typeclasses Opaque othreadG_term.
Global Instance: Params (@othreadG_term) 4 := {}.

(* Global invariant for the thread obligations state. *)
Definition othread `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (OThread : gmap positive (gmap obl_id bool)),
        (⌜ dom OThread = TP ⌝) ∗
        (own state_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset TP))) ∗
        (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))) ∗
        (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
        ([∗ map] i ↦ B ∈ OThread,
           (othreadG_exec i (1/2)%Qp ∨ (othreadG_term_auth i ∗ ⌜ B = ∅ ⌝)) ∗
           (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> B)))) ∗
           ([∗ map] k ↦ b ∈ B, oblG_live k (1/2)%Qp ∗
                               (match b with | true => oblG_owner k i (1/2/2)%Qp | _ => emp end))
        )
    )%I.

Section othread.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!othreadGS Σ}.

  (* Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ). *)
  (* Proof. solve_contractive. Qed. *)
  (* Global Instance oblG_goal_contractive i P : Contractive (@oblG_goal SI _ WFA ps T Σ _ i P). *)
  (* Proof. solve_contractive. Qed. *)
  (* Global Instance oblG_goal_persistent i P R : Persistent (oblG_goal i P R). *)
  (* Proof. rewrite /oblG_goal. apply _. Qed. *)
  (* Global Instance oblG_elem_persistent i : Persistent (oblG_elem i). *)
  (* Proof. rewrite /oblG_elem. apply _. Qed. *)
  (* Global Instance oblG_meta_persistent i m : Persistent (oblG_meta i m). *)
  (* Proof. rewrite /oblG_meta. apply _. Qed. *)
  (* Global Instance oblG_done_persistent i : Persistent (oblG_done i). *)
  (* Proof. rewrite /oblG_done. apply _. Qed. *)

  (* Goal rules *)

End othread.

(* Allocation of an initial obligation protocol. *)
(* Lemma othread_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!othreadGpreS ps T Σ} `{obl_class A ps T} : *)
(*   ⊢ |==> ∃ _ : othreadGS ps T Σ, othread ∅. *)
(* Proof. *)
(*   iIntros. *)
(*   iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (prodR _ _))) as (γG) "HG"; *)
(*     first by apply gmap_view_auth_valid. *)
(*   iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (agreeR $ metaO))) as (γM) "HM"; *)
(*     first by apply gmap_view_auth_valid. *)
(*   iMod (own_alloc (ε : gmap positive mono_natUR)) as (γS) "HS"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive bankUR)) as (γT) "HT"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive (dfrac_agreeR (leibnizO T)))) as (γO) "HO"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive bankUR)) as (γC) "HC"; *)
(*     first done. *)
(*   iModIntro; iExists (OthreadG SI _ WFA _ _ _ _ γG γM γS γT γO γC). *)
(*   rewrite /othread -lock. *)
(*   iSplitL "HG"; first (iExists ∅; by iFrame). *)
(*   iSplitL "HM"; first (iExists ∅; by iFrame). *)
(*   by iFrame. *)
(* Qed. *)
