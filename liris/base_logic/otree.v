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
      }.

  Class otreeGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OtreeG {
        otree_inG : otreeGpreS Σ;
        edge_name : gname;
        suspend_name : gname;
        wait_name : gname;
      }.

  Definition otreeΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id unitUR));
      GFunctor (reservation_mapUR (gmap_viewR positive (agreeR (prodO positiveO obl_idO))));
      GFunctor (reservation_mapUR (gmapUR positive mono_natUR))
      ].

  Global Instance subG_otreeΣ `{SI : indexT} {Σ} : subG (otreeΣ) Σ → (otreeGpreS Σ).
  Proof. solve_inG. Qed.

End otreeGS.
Import otreeGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances otree_inG otreeGpreS_edge otreeGpreS_suspend otreeGpreS_wait.

(* Edge *)
Definition otreeG_edge `{SI : indexT} `{!otreeGS Σ} (i j : obl_id) (q : Qp) : iProp Σ :=
  own edge_name (reservation_map_data i (gmap_view_frag j (DfracOwn q) ())).
Global Typeclasses Opaque otreeG_edge.
Global Instance: Params (@otreeG_edge) 6 := {}.

(* Suspend knowledge *)
Definition otreeG_suspend `{SI : indexT} `{!otreeGS Σ} (i : obl_id) (u : positive) (τ : positive) (π : obl_id) : iProp Σ :=
  own suspend_name (reservation_map_data i (gmap_view_frag u DfracDiscarded (to_agree (τ, π)))).
Global Typeclasses Opaque otreeG_suspend.
Global Instance: Params (@otreeG_suspend) 6 := {}.

(* Wait token *)
Definition otreeG_wait `{SI : indexT} `{!otreeGS Σ} (i : obl_id) (u : positive) (q : Qp) : iProp Σ :=
  own wait_name (reservation_map_data i {[u := ●MN{#q} 0]}).
Global Typeclasses Opaque otreeG_wait.
Global Instance: Params (@otreeG_wait) 6 := {}.

Definition otreeG_free `{SI : indexT} `{!otreeGS Σ} (i : obl_id) (u : positive) : iProp Σ :=
  own wait_name (reservation_map_data i {[u := ●MN 1]}).
Global Typeclasses Opaque otreeG_free.
Global Instance: Params (@otreeG_free) 6 := {}.

(* Global invariant for suspending obligations and waiting. *)
Definition osuspend `{SI : indexT} `{WF : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WF ps T Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OSus : gmap obl_id (gmap positive (prod positive obl_id))),
        (⌜ dom OSus = D ⌝) ∗
        (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset D))) ∗
        (own wait_name (reservation_map_token (A:=gmapUR positive mono_natUR) (⊤ ∖ gset_to_coPset D))) ∗
        ([∗ map] i ↦ M ∈ OSus,
           (own suspend_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> M)))) ∗
           ([∗ map] u ↦ '(τ, π) ∈ M,
              ((othreadG_owns τ i false (1/2)%Qp ∗ otreeG_edge π i 1) ∨
                 (othreadG_owns τ i true (1/2)%Qp ∗ otreeG_wait i u (1/2)%Qp ∗ oblG_done π)) ∨
                otreeG_free i u)
        )
    )%I.

(* Global invariant for the obligation forest state. *)
Definition otree `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OTree : cgraph obl_id unitO) (OOwner : gmap obl_id positive),
        (⌜ dom OTree = D ∧ dom OOwner = dom OTree ⌝) ∗
        (⌜ ∀ v u, descendant OTree v u → OOwner !! v = OOwner !! u ⌝) ∗
        (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
        ([∗ map] i ↦ C ∈ OTree,
           (own edge_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) C))) ∗
           ((* This obligation is live with enough transfer and credits for chiledren and... *)
             ((∃ l c, oblG_transfer_supply i l (1/2)%Qp ∗ oblG_credit_supply i c (1/2)%Qp ∗
                      ([∗ set] j ∈ (dom C), ∃ l' c', ⌜ WFOCM.leR l l' ∧ WFOCM.leR c c' ⌝ ∗ oblG_transfer j l' ∗ oblG_credit j c')
              ) ∗
              (* is a root or... *)
              (∃ τ, ⌜ root OTree i ∧ OOwner !! i = Some τ ⌝ ∗
                    oblG_owner i τ (1/2/2)%Qp ∗ othreadG_owns τ i true (1/2)%Qp) ∨
                (* is an internal node, and is suspended *)
                (∃ τ π, ⌜ internal OTree i ∧ OOwner !! i = Some τ ∧ parent OTree i π ⌝ ∗
                        oblG_owner i τ (1/2)%Qp ∗ othreadG_owns τ i false (1/2)%Qp ∗
                        (∃ x, otreeG_suspend i x τ π ∗ otreeG_wait i x (1/2)%Qp))
             ) ∨
               (* Or this obligation is done *)
               (oblG_done i ∗ ⌜ in_labels OTree i ≡ ε ∧ C = ∅ ⌝)
        ))
    )%I.

Section otree.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{obl_class A ps T}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}.

  Global Instance otreeG_suspend_persistent i u τ π : Persistent (otreeG_suspend i u τ π).
  Proof. rewrite /otreeG_suspend. apply _. Qed.

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
