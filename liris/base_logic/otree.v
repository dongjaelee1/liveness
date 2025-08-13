From iris.algebra Require Import agree gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.algebra Require Export tree.
From liris.base_logic Require Import osat othread.

(** The ghost state for liveness obligation forest *)
Module otreeGS.

  Class otreeGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OtreeGpreS {
        otreeGpreS_edge : inG Σ (reservation_mapUR (gmap_viewR obl_id unitUR));
        (* Data for suspending an obligation: returning thread_id, blocking parent id *)
        otreeGpreS_suspend : inG Σ (reservation_mapUR (gmap_viewR positive (agreeR (prodO positiveO obl_idO))));
        otreeGpreS_wait : inG Σ (reservation_mapUR (gmapUR positive mono_natUR));
        otreeGpreS_elem : inG Σ (gmap_viewR obl_id unitUR);
      }.

  Class otreeGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OtreeG {
        otree_inG : otreeGpreS Σ;
        edge_name : gname;
        suspend_name : gname;
        wait_name : gname;
        elem_name : gname;
      }.

  Definition otreeΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id unitUR));
      GFunctor (reservation_mapUR (gmap_viewR positive (agreeR (prodO positiveO obl_idO))));
      GFunctor (reservation_mapUR (gmapUR positive mono_natUR));
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_otreeΣ `{SI : indexT} {Σ} : subG (otreeΣ) Σ → (otreeGpreS Σ).
  Proof. solve_inG. Qed.

End otreeGS.
Import otreeGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances otree_inG
  otreeGpreS_edge otreeGpreS_suspend otreeGpreS_wait otreeGpreS_elem.

(* Edge *)
Definition otreeG_edge `{SI : indexT} `{!otreeGS Σ} (π k : obl_id) (q : Qp) : iProp Σ :=
  own edge_name (reservation_map_data π (gmap_view_frag k (DfracOwn q) ())).
Global Typeclasses Opaque otreeG_edge.
Global Instance: Params (@otreeG_edge) 6 := {}.

(* Suspend knowledge *)
Definition otreeG_suspend `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) (θ : positive) (π : obl_id) : iProp Σ :=
  own suspend_name (reservation_map_data k (gmap_view_frag x DfracDiscarded (to_agree (θ, π)))).
Global Typeclasses Opaque otreeG_suspend.
Global Instance: Params (@otreeG_suspend) 6 := {}.

(* Wait token *)
Definition otreeG_wait `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) (q : Qp) : iProp Σ :=
  own wait_name (reservation_map_data k {[x := ●MN{#q} 0]}).
Global Typeclasses Opaque otreeG_wait.
Global Instance: Params (@otreeG_wait) 6 := {}.

Definition otreeG_free `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) : iProp Σ :=
  own wait_name (reservation_map_data k {[x := ●MN 1]}).
Global Typeclasses Opaque otreeG_free.
Global Instance: Params (@otreeG_free) 6 := {}.

(* Elem: keeps the fact that a key is inside a map *)
Definition otreeG_elem `{SI : indexT} `{!otreeGS Σ} (k : obl_id) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded ()).
Global Typeclasses Opaque otreeG_elem.
Global Instance: Params (@otreeG_elem) 4 := {}.

(* Global invariant for suspending obligations and waiting. *)
Definition osuspend `{SI : indexT} `{WF : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WF ps T Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OSus : gmap obl_id (gmap positive (prod positive obl_id))),
        (⌜ dom OSus = D ⌝) ∗
        (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset D))) ∗
        (own wait_name (reservation_map_token (A:=gmapUR positive mono_natUR) (⊤ ∖ gset_to_coPset D))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OSus))) ∗
        ([∗ map] k ↦ M ∈ OSus,
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> M)))) ∗
           ([∗ map] x ↦ '(θ, π) ∈ M,
              ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
                 (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π)) ∨
                otreeG_free k x)
        )
    )%I.

(* Global invariant for the obligation forest state. *)
Definition otree `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OTree : cgraph obl_id unitO) (OOwner : gmap obl_id positive),
        (⌜ dom OTree = D ∧ dom OOwner = D ∧ cgraph_wf OTree ⌝) ∗
        (⌜ ∀ π k, descendant OTree π k → OOwner !! π = OOwner !! k ⌝) ∗
        (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
        ([∗ map] k ↦ C ∈ OTree,
           (own edge_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) C))) ∗
           ((* This obligation is live and has enough transfer and progress credits for chiledren and... *)
             ((∃ α β, oblG_transfer_supply k α (1/2)%Qp ∗ oblG_progress_supply k β (1/2)%Qp ∗
                      ([∗ set] c ∈ (dom C),
                         ∃ α' β', ⌜ WFOCM.leR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
              ) ∗
              (* is a root or... *)
              (∃ θ, ⌜ root OTree k ∧ OOwner !! k = Some θ ⌝ ∗
                    oblG_owner k θ (1/2/2)%Qp ∗
                    othreadG_owns θ k true (1/2)%Qp) ∨
                (* is an internal node, and is suspended *)
                (∃ τ π, ⌜ parent OTree k π ∧ OOwner !! k = Some τ ⌝ ∗
                        oblG_owner k τ (1/2)%Qp ∗
                        ∃ θ, othreadG_owns θ k false (1/2)%Qp ∗
                             (∃ x, otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp))
             ) ∨
               (* Or this obligation is done *)
               (oblG_done k ∗ ⌜ root OTree k ∧ C = ∅ ⌝)
        ))
    )%I.

Section otree.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{obl_class A ps T}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}.

  Global Instance otreeG_suspend_persistent k x θ π : Persistent (otreeG_suspend k x θ π).
  Proof. rewrite /otreeG_suspend. apply _. Qed.
  Global Instance otreeG_elem_persistent k : Persistent (otreeG_elem k).
  Proof. rewrite /otreeG_elem. apply _. Qed.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

End otree.

(* Allocation of an initial obligation protocol. *)
(* Lemma otree_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!otreeGpreS ps T Σ} `{obl_class A ps T} : *)
(*   ⊢ |==> ∃ _ : otreeGS ps T Σ, otree ∅. *)
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
(*   iModIntro; iExists (OtreeG SI _ WFA _ _ _ _ γG γM γS γT γO γC). *)
(*   rewrite /otree -lock. *)
(*   iSplitL "HG"; first (iExists ∅; by iFrame). *)
(*   iSplitL "HM"; first (iExists ∅; by iFrame). *)
(*   by iFrame. *)
(* Qed. *)
