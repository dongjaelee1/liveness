From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Export wfocm.
From liris.base_logic Require Export obligation.
From liris.algebra Require Import bank.

Definition obl_idO `{SI : indexT} := leibnizO obl_id.

(** The ghost state for liveness obligations *)
Module osatGS.

  Class osatGpreS `{SI : indexT} `{WF : WFOCM.pack A} (ps T : Type) (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_goal : inG Σ (gmap_viewR obl_id (prodR (agreeR $ (prop_ofO ps)) (agreeR $ (laterO (iPropO Σ)))));
        osatGpreS_status : inG Σ (reservation_mapUR mono_natUR);
        osatGpreS_transfer : inG Σ (reservation_mapUR bankUR);
        osatGpreS_tbound : inG Σ (reservation_mapUR (agreeR (leibnizO A)));
        osatGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO T)));
        osatGpreS_progress : inG Σ (reservation_mapUR bankUR);
      }.

  Class osatGS `{SI : indexT} `{WF : WFOCM.pack A} (ps T : Type) (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS ps T Σ;
        goal_name : gname;
        status_name : gname;
        transfer_name : gname;
        tbound_name : gname;
        owner_name : gname;
        progress_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOCM.pack A} (ps T : Type) : gFunctors :=
    #[GFunctor (gmap_viewTRF obl_id (prodTRF (agreeTRF $ (prop_ofO ps)) (agreeTRF $ (laterTF idTF))));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (reservation_mapUR bankUR);
      GFunctor (reservation_mapUR (agreeR $ (leibnizO A)));
      GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO T)));
      GFunctor (reservation_mapUR bankUR)
      ].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOCM.pack A} {ps T : Type} {Σ} : subG (osatΣ ps T) Σ → (osatGpreS ps T Σ).
  Proof. solve_inG. Qed.

End osatGS.
Import osatGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG
  osatGpreS_goal osatGpreS_status osatGpreS_transfer osatGpreS_tbound osatGpreS_owner osatGpreS_progress.

(* Goals *)
Definition goal_unfold `{SI : indexT} {Σ} (R : iProp Σ) : later (iProp Σ) := Next R.
Definition oblG_goal `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (P : prop_of ps) (R : iProp Σ) : iProp Σ :=
  own goal_name (gmap_view_frag k DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)).
Global Typeclasses Opaque oblG_goal.
Global Instance: Params (@goal_unfold) 2 := {}.
Global Instance: Params (@oblG_goal) 8 := {}.

Definition oblG_elem `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) : iProp Σ :=
  ∃ P R, oblG_goal k P R.
Global Typeclasses Opaque oblG_elem.
Global Instance: Params (@oblG_elem) 8 := {}.

(* Status: live or done *)
Definition oblG_live `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (q : Qp) : iProp Σ :=
  own status_name (reservation_map_data k (●MN{#q} 0)).
Global Typeclasses Opaque oblG_live.
Global Instance: Params (@oblG_live) 8 := {}.

Definition oblG_done_auth `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) : iProp Σ :=
  own status_name (reservation_map_data k (●MN 1)).
Global Typeclasses Opaque oblG_done_auth.
Global Instance: Params (@oblG_done_auth) 8 := {}.

Definition oblG_done `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) : iProp Σ :=
  own status_name (reservation_map_data k (◯MN 1)).
Global Typeclasses Opaque oblG_done.
Global Instance: Params (@oblG_done) 8 := {}.

(* Transfer: manage credits for transfer *)
Definition oblG_transfer `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (α : A) : iProp Σ :=
  own transfer_name (reservation_map_data k (cash α)).
Global Typeclasses Opaque oblG_transfer.
Global Instance: Params (@oblG_transfer) 8 := {}.

Definition oblG_transfer_supply `{SI : indexT} `{WF : WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (α : A) (q : Qp) : iProp Σ :=
  own transfer_name (reservation_map_data k (debt α q)).
Global Typeclasses Opaque oblG_transfer_supply.
Global Instance: Params (@oblG_transfer_supply) 8 := {}.

(* Fixed bound for transfer credits *)
Definition oblG_transfer_bound `{SI : indexT} `{WF : WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (ℵ : A) : iProp Σ :=
  own tbound_name (reservation_map_data k (to_agree $ ℵ : agreeR (leibnizO _))).
Global Typeclasses Opaque oblG_transfer_bound.
Global Instance: Params (@oblG_transfer_bound) 8 := {}.

(* Owner: tracks the owner thread of this obligation *)
Definition oblG_owner `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (τ : T) (q : Qp) : iProp Σ :=
  own owner_name (reservation_map_data k (to_frac_agree q (τ : leibnizO T))).
Global Typeclasses Opaque oblG_owner.
Global Instance: Params (@oblG_owner) 8 := {}.

(* Progress: manage credits for logical progress *)
Definition oblG_progress `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (β : A) : iProp Σ :=
  own progress_name (reservation_map_data k (cash β)).
Global Typeclasses Opaque oblG_progress.
Global Instance: Params (@oblG_progress) 8 := {}.

Definition oblG_progress_supply `{SI : indexT} `{WF : WFOCM.pack A} `{!osatGS ps T Σ} (k : obl_id) (β : A) (q : Qp) : iProp Σ :=
  own progress_name (reservation_map_data k (debt β q)).
Global Typeclasses Opaque oblG_progress_supply.
Global Instance: Params (@oblG_progress_supply) 8 := {}.

(* Global invariant for the obligation ghost state. *)
Definition osat `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps T Σ} `{obl_class A ps T} (Ω : obl_states) : iProp Σ :=
  locked
    ((∃ (OProp : gmap obl_id (prop_of ps * iProp Σ)),
         (⌜ dom OProp = dom Ω ⌝) ∗
         own goal_name
           (gmap_view_auth (DfracOwn 1)
              ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> OProp))) ∗
     (own status_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own transfer_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own tbound_name (reservation_map_token (A:=agreeR (leibnizO A)) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T))(⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own progress_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     ([∗ map] k ↦ o ∈ Ω,
        match o with
        | obl_live d =>
            oblG_live k (1/2)%Qp ∗
            (∃ α, ⌜ WFOCM.leR α (obl_transfer d) ⌝ ∗ oblG_transfer_supply k α (1/2)%Qp) ∗
            (∃ ℵ, ⌜ WFOCM.leR (obl_transfer d) ℵ ⌝ ∗ oblG_transfer_bound k ℵ) ∗
            (oblG_owner k (obl_owner d) (1/2)%Qp) ∗
            (∃ β, ⌜ WFOCM.leR β (obl_progress d) ⌝ ∗ oblG_progress_supply k β (1/2)%Qp)
        | obl_done P1 =>
            ∃ P2 R, oblG_goal k P2 R ∗ ⌜ P1 ≡ P2 ⌝ ∗ ▷ R ∗
                    oblG_done_auth k ∗
                    (∃ l, oblG_transfer_supply k l 1) ∗
                    (∃ t, oblG_owner k t 1) ∗
                    (∃ a, oblG_progress_supply k a 1)
      end)
    )%I.

Section osat.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps T Σ} `{obl_class A ps T}.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive k P : Contractive (@oblG_goal SI _ WFA ps T Σ _ k P).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_persistent k P R : Persistent (oblG_goal k P R).
  Proof. rewrite /oblG_goal. apply _. Qed.
  Global Instance oblG_elem_persistent k : Persistent (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_done_persistent k : Persistent (oblG_done k).
  Proof. rewrite /oblG_done. apply _. Qed.
  Global Instance oblG_transfer_bound_persistent k ℵ : Persistent (oblG_transfer_bound k ℵ).
  Proof. rewrite /oblG_transfer_bound. apply _. Qed.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  (* Goal rules *)

  Lemma oblG_goal_lookup (OProp : gmap positive (prop_of ps * iProp Σ)) k P R :
    own goal_name
      (gmap_view_auth (DfracOwn 1)
         ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> OProp)) ∗
    oblG_goal k P R
    ⊢ ∃ P' R', ⌜OProp !! k = Some (P', R')⌝ ∗ ⌜P' = P⌝ ∗ ▷ (R' ≡ R).
  Proof.
    rewrite /oblG_goal -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (OProp !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    destruct Q as (P'&R'). iDestruct "HQ'" as %[= <-]. iExists P', R'; iSplit; first done.
    rewrite prod_includedI !to_agree_includedI; simpl. iDestruct "Hincl" as "[H1 H2]".
    rewrite /goal_unfold -later_equivI. iSplit.
    - iPoseProof (internal_eq_sym with "H1") as "H1". iPoseProof (discrete_eq with "H1") as "%HG". done.
    - iPoseProof (internal_eq_sym with "H2") as "H2". done.
  Qed.

  Lemma oblG_elem_unfold k : oblG_elem k ⊣⊢ ∃ P R, oblG_goal k P R.
  Proof. done. Qed.

  (* Status rules *)

  Lemma oblG_live_done_false k q :
    oblG_live k q ∗ oblG_done k ⊢ False.
  Proof.
    rewrite /oblG_live /oblG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblG_done_auth_done k :
    oblG_done_auth k ⊢ oblG_done k.
  Proof.
    rewrite /oblG_done_auth /oblG_done.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

  Lemma oblG_live_to_done k :
    oblG_live k 1 ⊢ |==> oblG_done_auth k.
  Proof.
    rewrite /oblG_live /oblG_done_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.

  Lemma oblG_live_dfrac_op k q1 q2 q :
    q = (q1 + q2)%Qp →
    oblG_live k q1 ∗ oblG_live k q2 ⊣⊢ oblG_live k q.
  Proof.
    intros; subst. rewrite /oblG_live. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". done.
    - iDestruct "H" as "[H1 H2]". iFrame.
  Qed.

  Lemma oblG_live_div_2 k q :
    oblG_live k (q/2) ∗ oblG_live k (q/2) ⊣⊢ oblG_live k q.
  Proof. rewrite oblG_live_dfrac_op; first done. by rewrite Qp.div_2. Qed.

  Lemma oblG_live_valid k q :
    oblG_live k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_live. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  (* oblG_transfer rules *)

  (* TODO *)

  (* Lemma oblG_transfer_eq i a0 a1 : *)
  (*   a0 /= a1 → *)
  (*   oblG_transfer i a0 = oblG_transfer i a1. *)
  (* Proof. intros EQ. rewrite /oblG_transfer. by erewrite cash_eq. Qed. *)

  (* Lemma oblG_transfer_eq_list L a0 a1 : *)
  (*   a0 /= a1 → *)
  (*   ([∗ list] i ∈ L, oblG_transfer i a0)%I ≡ ([∗ list] i ∈ L, oblG_transfer i a1)%I. *)
  (* Proof. intros. apply big_opL_proper. intros. erewrite oblG_transfer_eq; eauto. Qed. *)

  (* Lemma oblG_transfer_mon i a0 a1 : *)
  (*   a0 /≤ a1 → *)
  (*   oblG_transfer i a1 ⊢ |==> oblG_transfer i a0. *)
  (* Proof. *)
  (*   intros LE. rewrite /oblG_transfer. apply own_update. *)
  (*   apply reservation_map_update. *)
  (*   apply prod_update; [simpl | reflexivity]. apply prod_update; [simpl | reflexivity]. *)
  (*   apply prod_update; [simpl | reflexivity]. *)
  (*   by apply cash_update. *)
  (* Qed. *)

  (* Lemma oblG_transfer_split i a0 a1 : *)
  (*   oblG_transfer i (a0 /+ a1) ⊣⊢ oblG_transfer i a0 ∗ oblG_transfer i a1. *)
  (* Proof. *)
  (*   rewrite /oblG_transfer. iSplit; [iIntros "H" | iIntros "[H1 H2]"]. *)
  (*   - iEval (rewrite -cash_add) in "H". iApply own_op. *)
  (*     iApply own_mono; [| iFrame]. rewrite reservation_map_data_op -!pair_op !left_id_L. done. *)
  (*   - iEval (rewrite -cash_add). iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame). *)
  (*     iEval (rewrite reservation_map_data_op -!pair_op left_id_L) in "H". done. *)
  (* Qed. *)

  (* Lemma oblG_transfer_split_list L a0 a1 : *)
  (*   ([∗ list] i ∈ L, oblG_transfer i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, oblG_transfer i a0) ∗ ([∗ list] i ∈ L, oblG_transfer i a1). *)
  (* Proof. *)
  (*   rewrite -big_sepL_sep. iSplit; iIntros "H". *)
  (*   - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblG_transfer_split. *)
  (*   - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblG_transfer_split. *)
  (* Qed. *)

  (* Lemma oblG_transfer_mon_split i a0 a1 a2 : *)
  (*   a0 /+ a1 /≤ a2 → *)
  (*   oblG_transfer i a2 ⊢ |==> oblG_transfer i a0 ∗ oblG_transfer i a1. *)
  (* Proof. *)
  (*   intros LE. iIntros "H". iApply oblG_transfer_split. iApply oblG_transfer_mon; done. *)
  (* Qed. *)

  (* Lemma oblG_transfer_mon_split_list L a0 a1 a2 : *)
  (*   a0 /+ a1 /≤ a2 → *)
  (*   ([∗ list] i ∈ L, oblG_transfer i a2) ⊢ |==> ([∗ list] i ∈ L, oblG_transfer i a0) ∗ ([∗ list] i ∈ L, oblG_transfer i a1). *)
  (* Proof. *)
  (*   iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H"). *)
  (*   iModIntro. iIntros. by iApply oblG_transfer_mon_split. *)
  (* Qed. *)

  (* Lemma oblG_transfer_supply_add i a0 a1 q0 q1 : *)
  (*   oblG_transfer_supply i a0 q0 ∗ oblG_transfer_supply i a1 q1 *)
  (*   ⊢ ∃ b, oblG_transfer_supply i b (q0 + q1) ∗ ⌜ b /≤ a0 ∧ b /≤ a1 ⌝. *)
  (* Proof. *)
  (*   rewrite /oblG_transfer_supply. iIntros "[H1 H2]". *)
  (*   iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame). *)
  (*   iEval (rewrite reservation_map_data_op -!pair_op left_id_L) in "H". *)
  (*   destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq. *)
  (*   iExists b. iSplitL; done. *)
  (* Qed. *)

  (* Lemma oblG_transfer_supply_split i a q0 q1 : *)
  (*   oblG_transfer_supply i a (q0 + q1) ⊢ oblG_transfer_supply i a q0 ∗ oblG_transfer_supply i a q1. *)
  (* Proof. *)
  (*   rewrite /oblG_transfer_supply. iIntros "H". *)
  (*   iApply own_op. iEval (rewrite reservation_map_data_op -!pair_op left_id_L). *)
  (*   rewrite debt_split. done. *)
  (* Qed. *)

  (* Lemma oblG_transfer_spend i a0 a1 q : *)
  (*   oblG_transfer_supply i a0 q ∗ oblG_transfer i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ oblG_transfer_supply i a2 q. *)
  (* Proof. *)
  (*   rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)". *)
  (*   { rewrite reservation_map_data_op -!pair_op. *)
  (*     eapply (reservation_map_updateP *)
  (*               (λ k, ∃ a2, (k = (debt a2 q, ε, ε, ε)) ∧ (a1 /+ a2 /≤ a0)) *)
  (*               (λ k, ∃ a2, (k = {[i := (debt a2 q, ε, ε, ε)]}) ∧ (a1 /+ a2 /≤ a0)) *)
  (*            ). *)
  (*     { eapply (prod_updateP (λ k, ∃ a2, (k = (debt a2 q, ε, ε)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)). *)
  (*       { eapply (prod_updateP (λ k, ∃ a2, (k = (debt a2 q, ε)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)). *)
  (*         { eapply (prod_updateP (λ k, ∃ a2, (k = debt a2 q) ∧ (a1 /+ a2 /≤ a0)) (eq ε)). *)
  (*           { eapply debt_pay. } *)
  (*           { eapply cmra_update_updateP. reflexivity. } *)
  (*           { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*         } *)
  (*         { eapply cmra_update_updateP. simpl. rewrite left_id. reflexivity. } *)
  (*         { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*       } *)
  (*       { eapply cmra_update_updateP. reflexivity. } *)
  (*       { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*     } *)
  (*     { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*   } *)
  (*   iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)". *)
  (*   iExists a2. subst. iModIntro. iSplitR; done. *)
  (* Qed. *)

  (* (* oblG_progress rules *) *)

  (* Lemma oblG_progress_eq i a0 a1 : *)
  (*   a0 /= a1 → *)
  (*   oblG_progress i a0 = oblG_progress i a1. *)
  (* Proof. intros EQ. rewrite /oblG_progress. by erewrite cash_eq. Qed. *)

  (* Lemma oblG_progress_eq_list L a0 a1 : *)
  (*   a0 /= a1 → *)
  (*   ([∗ list] i ∈ L, oblG_progress i a0)%I ≡ ([∗ list] i ∈ L, oblG_progress i a1)%I. *)
  (* Proof. intros. apply big_opL_proper. intros. erewrite oblG_progress_eq; eauto. Qed. *)

  (* Lemma oblG_progress_mon i a0 a1 : *)
  (*   a0 /≤ a1 → *)
  (*   oblG_progress i a1 ⊢ |==> oblG_progress i a0. *)
  (* Proof. *)
  (*   intros LE. rewrite /oblG_progress. apply own_update. *)
  (*   apply reservation_map_update. *)
  (*   apply prod_update; [simpl | reflexivity]. apply prod_update; [reflexivity | simpl]. *)
  (*   by apply cash_update. *)
  (* Qed. *)

  (* Lemma oblG_progress_split i a0 a1 : *)
  (*   oblG_progress i (a0 /+ a1) ⊣⊢ oblG_progress i a0 ∗ oblG_progress i a1. *)
  (* Proof. *)
  (*   rewrite /oblG_progress. iSplit; [iIntros "H" | iIntros "[H1 H2]"]. *)
  (*   - iEval (rewrite -cash_add) in "H". iApply own_op. *)
  (*     iApply own_mono; [| iFrame]. rewrite reservation_map_data_op -!pair_op !left_id_L. done. *)
  (*   - iEval (rewrite -cash_add). iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame). *)
  (*     iEval (rewrite reservation_map_data_op -!pair_op left_id_L) in "H". done. *)
  (* Qed. *)

  (* Lemma oblG_progress_split_list L a0 a1 : *)
  (*   ([∗ list] i ∈ L, oblG_progress i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, oblG_progress i a0) ∗ ([∗ list] i ∈ L, oblG_progress i a1). *)
  (* Proof. *)
  (*   rewrite -big_sepL_sep. iSplit; iIntros "H". *)
  (*   - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblG_progress_split. *)
  (*   - iApply (big_sepL_impl with "H"). iModIntro. iIntros. by iApply oblG_progress_split. *)
  (* Qed. *)

  (* Lemma oblG_progress_mon_split i a0 a1 a2 : *)
  (*   a0 /+ a1 /≤ a2 → *)
  (*   oblG_progress i a2 ⊢ |==> oblG_progress i a0 ∗ oblG_progress i a1. *)
  (* Proof. *)
  (*   intros LE. iIntros "H". iApply oblG_progress_split. iApply oblG_progress_mon; done. *)
  (* Qed. *)

  (* Lemma oblG_progress_mon_split_list L a0 a1 a2 : *)
  (*   a0 /+ a1 /≤ a2 → *)
  (*   ([∗ list] i ∈ L, oblG_progress i a2) ⊢ |==> ([∗ list] i ∈ L, oblG_progress i a0) ∗ ([∗ list] i ∈ L, oblG_progress i a1). *)
  (* Proof. *)
  (*   iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H"). *)
  (*   iModIntro. iIntros. by iApply oblG_progress_mon_split. *)
  (* Qed. *)

  (* Lemma oblG_progress_supply_add i a0 a1 q0 q1 : *)
  (*   oblG_progress_supply i a0 q0 ∗ oblG_progress_supply i a1 q1 *)
  (*   ⊢ ∃ b, oblG_progress_supply i b (q0 + q1) ∗ ⌜ b /≤ a0 ∧ b /≤ a1 ⌝. *)
  (* Proof. *)
  (*   rewrite /oblG_progress_supply. iIntros "[H1 H2]". *)
  (*   iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame). *)
  (*   iEval (rewrite reservation_map_data_op -!pair_op left_id_L) in "H". *)
  (*   destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq. *)
  (*   iExists b. iSplitL; done. *)
  (* Qed. *)

  (* Lemma oblG_progress_supply_split i a q0 q1 : *)
  (*   oblG_progress_supply i a (q0 + q1) ⊢ oblG_progress_supply i a q0 ∗ oblG_progress_supply i a q1. *)
  (* Proof. *)
  (*   rewrite /oblG_progress_supply. iIntros "H". *)
  (*   iApply own_op. iEval (rewrite reservation_map_data_op -!pair_op left_id_L). *)
  (*   rewrite debt_split. done. *)
  (* Qed. *)

  (* Lemma oblG_progress_supply_issue i a0 a1 : *)
  (*   oblG_progress_supply i a0 1 ⊢ |==> oblG_progress_supply i (a0 /+ a1) 1 ∗ oblG_progress i a1. *)
  (* Proof. *)
  (*   rewrite /oblG_progress_supply -own_op. apply own_update. *)
  (*   rewrite reservation_map_data_op. apply reservation_map_update. *)
  (*   apply prod_update; [simpl | reflexivity]. apply prod_update; simpl. *)
  (*   { by rewrite -pair_op left_id_L. } *)
  (*   apply debt_owe. *)
  (* Qed. *)

  (* Lemma oblG_progress_pay i a0 a1 q : *)
  (*   oblG_progress_supply i a0 q ∗ oblG_progress i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ oblG_progress_supply i a2 q. *)
  (* Proof. *)
  (*   rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)". *)
  (*   { rewrite reservation_map_data_op -!pair_op. *)
  (*     eapply (reservation_map_updateP *)
  (*               (λ k, ∃ a2, (k = (ε, ε, debt a2 q, ε)) ∧ (a1 /+ a2 /≤ a0)) *)
  (*               (λ k, ∃ a2, (k = {[i := (ε, ε, debt a2 q, ε)]}) ∧ (a1 /+ a2 /≤ a0)) *)
  (*            ). *)
  (*     { eapply (prod_updateP (λ k, ∃ a2, (k = (ε, ε, debt a2 q)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)). *)
  (*       { eapply (prod_updateP (eq (ε, ε)) (λ k, ∃ a2, (k = debt a2 q) ∧ (a1 /+ a2 /≤ a0))). *)
  (*         { eapply cmra_update_updateP. rewrite left_id. reflexivity. } *)
  (*         { eapply debt_pay. } *)
  (*         { intros. destruct H1 as (a2&A0&A1). exists a2. by subst. } *)
  (*       } *)
  (*       { eapply cmra_update_updateP. reflexivity. } *)
  (*       { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*     } *)
  (*     { intros. destruct H0 as (a2&A0&A1). exists a2. by subst. } *)
  (*   } *)
  (*   iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)". *)
  (*   iExists a2. subst. iModIntro. iSplitR; done. *)
  (* Qed. *)

  (* (* oblG_owner rules *) *)

  (* (* TODO *) *)

  (* (* osat rules *) *)

  (* Lemma osat_oblG_elem i Ω : *)
  (*   osat Ω ∗ oblG_elem i ⊢ ⌜i ∈ dom Ω⌝. *)
  (* Proof. *)
  (*   rewrite /osat -!lock. iIntros "(Ho & He)". iPoseProof (oblG_elem_unfold with "He") as "(%&%&Hg)". *)
  (*   iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   iPoseProof (oblG_goal_lookup with "[Hoa Hg]") as "(%&%&%&%&%&_)"; [iFrame; done |]. *)
  (*   iPureIntro. subst. apply elem_of_dom_2 in H0. set_solver. *)
  (* Qed. *)

  (* Lemma osat_obl_is_init Ω i q : *)
  (*   osat Ω ∗ oblG_elem i ∗ oblG_idle i q *)
  (*   ⊢ ∃ a, ⌜Ω !! i = Some (obl_init a)⌝. *)
  (* Proof. *)
  (*   iIntros "(Ho & #He & Hi)". *)
  (*   iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |]. *)
  (*   apply elem_of_dom in Hin; destruct Hin as [o LU]. *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   assert (LU2 : exists Q, Obls !! i = Some (o, Q)). *)
  (*   { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). *)
  (*     simpl in *. subst t. eauto. *)
  (*   } *)
  (*   destruct LU2 as (Q&LU2). *)
  (*   iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |]. *)
  (*   destruct o. *)
  (*   - iExists a. done. *)
  (*   - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & ACT & _)". *)
  (*     iPoseProof (oblG_idle_active_false with "[Hi ACT]") as "%F"; [iFrame | done]. *)
  (*     iPoseProof (oblG_active_auth_active with "ACT") as "#D". done. *)
  (*   - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & ACT & _)". *)
  (*     iPoseProof (oblG_idle_active_false with "[Hi ACT]") as "%F"; [iFrame | done]. *)
  (*     iPoseProof (oblG_active_auth_active with "ACT") as "#D". done. *)
  (* Qed. *)

  (* Lemma osat_obl_is_live Ω i q : *)
  (*   osat Ω ∗ oblG_elem i ∗ oblG_active i ∗ oblG_live i q *)
  (*   ⊢ ∃ a, ⌜Ω !! i = Some (obl_live a)⌝. *)
  (* Proof. *)
  (*   iIntros "(Ho & #He & #Ha & Hl)". *)
  (*   iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |]. *)
  (*   apply elem_of_dom in Hin; destruct Hin as [o LU]. *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   assert (LU2 : exists Q, Obls !! i = Some (o, Q)). *)
  (*   { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). *)
  (*     simpl in *. subst t. eauto. *)
  (*   } *)
  (*   destruct LU2 as (Q&LU2). *)
  (*   iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |]. *)
  (*   destruct o. *)
  (*   - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & IDLE & _)". *)
  (*     iPoseProof (oblG_idle_active_false with "[IDLE Ha]") as "%F"; [iFrame; done | done]. *)
  (*   - iExists a. done. *)
  (*   - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & _ & DONE)". *)
  (*     iPoseProof (oblG_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done]. *)
  (*     iPoseProof (oblG_done_auth_done with "DONE") as "#D". done. *)
  (* Qed. *)

  (* Lemma osat_obl_is_done Ω i (P : prop_of ps) R : *)
  (*   osat Ω ∗ oblG_goal i P R ∗ oblG_done i *)
  (*   ⊢ ∃ P', ⌜Ω !! i = Some (obl_done P') ∧ P' ≡ P⌝. *)
  (* Proof. *)
  (*   iIntros "(Ho & #He & #Hd)". *)
  (*   iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [rewrite /oblG_elem; iFrame; eauto |]. *)
  (*   apply elem_of_dom in Hin; destruct Hin as [o LU]. *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   assert (LU2 : exists Q, Obls !! i = Some (o, Q)). *)
  (*   { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). *)
  (*     simpl in *. subst t. eauto. *)
  (*   } *)
  (*   destruct LU2 as (Q&LU2). *)
  (*   iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |]. *)
  (*   destruct o. *)
  (*   - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & _ & LIVE)". *)
  (*     iPoseProof (oblG_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done]. *)
  (*   - iExFalso. subst. destruct a. iDestruct "LU" as "(% & _ & _ & _ & LIVE)". *)
  (*     iPoseProof (oblG_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done]. *)
  (*   - iPoseProof (oblG_goal_lookup with "[Hoa]") as "(%&%&%&%&%&_)"; [iFrame; done |]. *)
  (*     destruct Q. iDestruct "LU" as "[% _]". iPureIntro. subst. *)
  (*     rewrite LU2 in H. inv H. rewrite LU. exists P0. done. *)
  (* Qed. *)

  (* Lemma osat_obl_is_done_weak Ω i : *)
  (*   osat Ω ∗ oblG_elem i ∗ oblG_done i *)
  (*   ⊢ ∃ P, ⌜Ω !! i = Some (obl_done P)⌝. *)
  (* Proof. *)
  (*   rewrite /oblG_elem. iIntros "(Ho & #He & #Hd)". iDestruct "He" as "(%&%&#He)". *)
  (*   iPoseProof (osat_obl_is_done with "[$]") as "(%&%)". destruct H. by iExists P'. *)
  (* Qed. *)

  (* Lemma osat_obl_is_done_weak_set Ω D : *)
  (*   osat Ω ∗ ([∗ set] i ∈ D, oblG_done i ∗ oblG_elem i) *)
  (*   ⊢ [∗ set] i ∈ D, ⌜ ∃ P, Ω !! i = Some (obl_done P) ⌝. *)
  (* Proof. *)
  (*   revert Ω. pattern D. revert D. apply set_ind. *)
  (*   { solve_proper. } *)
  (*   { iIntros (Ω) "[HO Hs]". rewrite big_opS_empty. done. } *)
  (*   iIntros (i D NIN IH Ω) "[HO Hs]". rewrite !big_sepS_union; [|set_solver|set_solver]. *)
  (*   rewrite !big_sepS_singleton. iDestruct "Hs" as "[[Hi1 Hi2] Hs]". *)
  (*   iPoseProof (osat_obl_is_done_weak with "[HO Hi1 Hi2]") as "[% %]"; first iFrame. iSplitR. *)
  (*   - iPureIntro. exists P. done. *)
  (*   - iApply IH. iFrame. *)
  (* Qed. *)

  (* Lemma osat_alloc_obl Ω a b P R : *)
  (*   osat Ω *)
  (*   ⊢ |==> ∃ i, ⌜Ω !! i = None⌝ ∗ osat (<[i:=obl_init (a, b)]>Ω) ∗ *)
  (*               oblG_goal i P R ∗ oblG_idle i (1/2 + 1/2/2)%Qp ∗ oblG_live i (1/2 + 1/2/2)%Qp ∗ oblG_transfer i a ∗ oblG_transfer_supply i a. *)
  (* Proof. *)
  (*   rewrite /osat -!lock. *)
  (*   iIntros "Ho". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   iMod (@own_unit _ _ _ osatGpreS_state state_name) as "HU". *)
  (*   iMod ((@own_updateP _ _ _ osatGpreS_state _ state_name) with "HU") as "H". *)
  (*   { apply (alloc_updateP_cofinite' ∅ ((progress_bound a ⋅ progress a : bcred (H:=WFOCM.ocm)), ●MN 0, ●MN 0) (dom Ω)). *)
  (*     rewrite pair_valid. split; [| apply mono_nat_auth_valid]. *)
  (*     rewrite pair_valid. split; [| apply mono_nat_auth_valid]. *)
  (*     apply progress_bound_progress_valid_eq. *)
  (*   } *)
  (*   iSimpl. iDestruct "H" as (a' (i & NIN & Ha' & _)) "H". rewrite insert_empty in Ha'. subst a'. *)
  (*   iAssert (oblG_transfer_supply i a ∗ oblG_transfer i a ∗ oblG_idle i (1/2 + 1/2/2)%Qp ∗ oblG_idle i (1/2/2)%Qp ∗ oblG_live i (1/2 + 1/2/2)%Qp ∗ oblG_live i (1/2/2)%Qp)%I *)
  (*     with "[H]" as "(Sb & Sc & Si1 & Si2 & Sl1 & Sl2)". *)
  (*   { rewrite /oblG_transfer_supply /oblG_transfer /oblG_idle /oblG_live -!own_op !reservation_map_data_op -!pair_op. iSimpl. *)
  (*     iApply own_mono; [|done]. *)
  (*     apply reservation_map_data_mono, option_included. right. do 2 eexists. do 2 split; [eauto|]. *)
  (*     left. rewrite !left_id !right_id. rewrite -!mono_nat_auth_dfrac_op dfrac_op_own. *)
  (*     rewrite -!Qp.add_assoc !Qp.div_2. done. *)
  (*   } *)
  (*   iPoseProof "Sb" as "#Sb". iMod (own_update with "Hoa") as "Hoa". *)
  (*   { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); [| done | done]. *)
  (*     rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver]. *)
  (*   } *)
  (*   iDestruct "Hoa" as "[Hoa #Hg]". *)
  (*   iModIntro. iExists i. iFrame. iFrame "Sb". rewrite -!lock. iSplitR. *)
  (*   { iPureIntro. subst. apply not_elem_of_dom_1. set_solver. } *)
  (*   iSplit; [|done]. *)
  (*   { iClear "Hg". iExists (<[i:=(obl_init (a, b), (P, R))]>Obls). iSplit. *)
  (*     { iPureIntro. subst. by rewrite fmap_insert. } *)
  (*     iSplitL "Hoa". *)
  (*     { iEval (rewrite !fmap_insert). iFrame. } *)
  (*     { iApply big_sepM_insert. *)
  (*       { subst. apply not_elem_of_dom_1. set_solver. } *)
  (*       iFrame. eauto. *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  (* Lemma osat_step_one_obl_init_live Ω i a b : *)
  (*   Ω !! i = Some (obl_init (a, b)) → *)
  (*   osat Ω ∗ oblG_elem i ∗ oblG_idle i (1/2 + 1/2/2)%Qp *)
  (*   ⊢ |==> osat (<[i:=obl_live (a, b)]>Ω) ∗ oblG_active i. *)
  (* Proof. *)
  (*   iIntros (LU) "(Ho&He&Hi)". rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   assert (LU2 : exists Q, Obls !! i = Some (obl_init (a, b), Q)). *)
  (*   { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). simpl in *. subst t. eauto. } *)
  (*   destruct LU2 as (Q&LU2). iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |]. *)
  (*   iDestruct "LU" as "(%a' & %LE & BND & IDLE & LIVE)". *)
  (*   iMod (oblG_idle_to_active with "[Hi IDLE]") as "Ha". *)
  (*   { iApply oblG_idle_dfrac_op; [|iFrame]. by rewrite Qp.add_comm -Qp.add_assoc !Qp.div_2. } *)
  (*   iPoseProof (oblG_active_auth_active with "Ha") as "#Haa". *)
  (*   iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live (a, b), Q))  with "[Hom Ha LIVE BND]") as "Hom". *)
  (*   { apply lookup_delete. } *)
  (*   { iFrame. iExists a'. iFrame. done. } *)
  (*   iModIntro. iFrame. iSplit; [|done]. iSplit. *)
  (*   - iPureIntro. rewrite insert_delete_insert fmap_insert. simpl. by rewrite <- HO. *)
  (*   - assert (snd <$> Obls = (snd <$> <[i:=(obl_live (a, b), Q)]> (delete i Obls))). *)
  (*     { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete. rewrite lookup_fmap. by rewrite LU2. } *)
  (*     by rewrite H. *)
  (* Qed. *)

  (* Lemma osat_step_one_obl_live_live Ω i a b b' c : *)
  (*   (Ω !! i = Some (obl_live (a, b))) → *)
  (*   (/0 /< c) → *)
  (*   osat Ω ∗ oblG_transfer i c *)
  (*   ⊢ |==> ∃ a', osat (<[i:=obl_live (a', b')]>Ω) ∗ ∀ s, ⌜obl_state_step s (obl_live (a, b)) (obl_live (a', b'))⌝. *)
  (* Proof. *)
  (*   intros LU Hc. iIntros "(Ho & CR)". *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   assert (LU2 : exists Q, Obls !! i = Some (obl_live (a, b), Q)). *)
  (*   { subst. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU). simpl in *. subst t. eauto. } *)
  (*   destruct LU2 as (Q&LU2). *)
  (*   iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |]. *)
  (*   iDestruct "LU" as "(%a' & %LE & BND & ACTa & LIVE)". *)
  (*   iPoseProof (oblG_transfer_spend with "[BND CR]") as ">(%&%&BND)"; [by iFrame |]. *)
  (*   assert (LT : a2 /< a). *)
  (*   { apply WFOCM.lt_exists_right. exists c. split; [auto | etransitivity; eauto]. } *)
  (*   iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live (a2, b'), Q))  with "[Hom ACTa LIVE BND]") as "Hom". *)
  (*   { apply lookup_delete. } *)
  (*   { iFrame. iExists a2. iFrame. done. } *)
  (*   iModIntro. iFrame. iExists a2. iSplit. *)
  (*   - assert (snd <$> Obls = (snd <$> <[i:=(obl_live (a2, b'), Q)]> (delete i Obls))). *)
  (*     { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete. *)
  (*       rewrite lookup_fmap. rewrite LU2. done. *)
  (*     } *)
  (*     rewrite -lock. iExists _. iFrame. iSplit; [|by rewrite -!H0]. *)
  (*     { iPureIntro. rewrite fmap_insert fmap_delete. *)
  (*       rewrite -HO. simpl. symmetry. apply insert_delete_insert. *)
  (*     } *)
  (*   - iIntros. iPureIntro. simpl. by econstructor 1. *)
  (* Qed. *)

  (* Lemma osat_step_one_obl_live_done Ω i P R : *)
  (*   osat Ω ∗ oblG_active i ∗ oblG_live i (1/2 + 1/2/2) ∗ oblG_goal i P R ∗ ▷ R *)
  (*   ⊢ |==> osat (<[i:=obl_done P]>Ω) ∗ oblG_done i. *)
  (* Proof. *)
  (*   iIntros "(Ho & #Ha & Hl & #Hg & R)". *)
  (*   iPoseProof (osat_obl_is_live with "[Ho Hl]") as "[% %Hlive]". *)
  (*   { iFrame. rewrite /oblG_elem. iSplit; [|done]. by iExists P, R. } *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done| subst]. *)
  (*   iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]". *)
  (*   assert (o = obl_live a). *)
  (*   { rewrite lookup_fmap in Hlive. rewrite IN in Hlive. inv Hlive. done. } *)
  (*   subst o. *)
  (*   destruct a. iDestruct "Hc" as "(%&_&_&Haa&Hl2)". *)
  (*   iCombine "Hl Hl2" as "Hl". iPoseProof (oblG_live_dfrac_op _ _ _ 1 with "Hl") as "Hl". *)
  (*   { by rewrite -Qp.add_assoc !Qp.div_2. } *)
  (*   iMod (oblG_live_to_done with "[$]") as "Hda". *)
  (*   iPoseProof (oblG_done_auth_done with "[$]") as "#DONE". *)
  (*   iModIntro. iSplitL; [|done]. iExists (<[i := (obl_done P, (P, R'))]>Obls). iSplit. *)
  (*   { iPureIntro. by rewrite fmap_insert. } *)
  (*   iSplitL "Hoa". *)
  (*   { rewrite fmap_insert insert_id; [iFrame|]. rewrite lookup_fmap IN. done. } *)
  (*   iApply (big_sepM_delete _ _ i); [apply lookup_insert |]. *)
  (*   iFrame. iSplitL "R". *)
  (*   { iSplit; [done|]. iNext. by iRewrite "HPQ". } *)
  (*   rewrite delete_insert_delete. iFrame. *)
  (* Qed. *)

  (* Lemma osat_progress Ω (L : list obl_id) (F : obl_id → B → Prop) (R : obl_id → B → Prop) : *)
  (*   osat Ω ∗ ([∗ map] i ↦ o ∈ Ω, match o with *)
  (*                                | obl_live (a, b) => *)
  (*                                    (if decide (i ∈ L) *)
  (*                                     then (∃ c, ⌜ /0 /< c ⌝ ∧ oblG_transfer i c ∧ ⌜ ∃ b', F i b' ⌝) *)
  (*                                     else (⌜ ∃ b', RB b' b ∧ R i b' ⌝)) *)
  (*                                | _ => True *)
  (*                                end) *)
  (*   ⊢ |==> ∃ Ω', osat Ω' ∗ (⌜ obl_states_progress Ω Ω' ⌝) ∗ *)
  (*                (⌜ map_Forall (λ i o, match o with *)
  (*                                      | obl_live (a, b) => (if decide (i ∈ L) then F i b else R i b) | _ => True end) Ω' ⌝). *)
  (* Proof. *)
  (*   rewrite /osat -!lock. iIntros "[(%Obls & %HO & Hoa & Hom) HM]". *)
  (*   iEval (rewrite HO) in "HM". iPoseProof (big_sepM_fmap fst _ Obls with "HM") as "HM". *)
  (*   iCombine "Hom HM" as "HM". iPoseProof (big_sepM_sep with "HM") as "HM". *)
  (*   iAssert (|==> [∗ map] k↦x ∈ Obls, *)
  (*              (let (y, y0) := (x : obl_state * (prop_of ps * iProp Σ)) in *)
  (*               match y with *)
  (*               | obl_init (a, _) => *)
  (*                   (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblG_transfer_supply k a' ∗ oblG_idle k (1/2/2) ∗ oblG_live k (1/2/2)) *)
  (*               | obl_live (a, b) => *)
  (*                   (if decide (k ∈ L) *)
  (*                    then (∃ a0, ⌜ a0 /< a ⌝ ∗ ∃ a' : A, ⌜a' /≤ a0⌝ ∗ oblG_transfer_supply k a' ∗ oblG_active_auth k ∗ oblG_live k (1/2/2) ∧ ⌜ ∃ b', F k b' ⌝) *)
  (*                    else ((∃ a' : A, ⌜a' /≤ a⌝ ∗ oblG_transfer_supply k a' ∗ oblG_active_auth k ∗ oblG_live k (1/2/2)) ∗ ⌜ ∃ b', RB b' b ∧ R k b' ⌝)) *)
  (*               | obl_done P1 => (let (P2, R) := y0 in ⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblG_active_auth k ∗ oblG_done_auth k) *)
  (*               end))%I with "[HM]" as ">HM". *)
  (*   { iApply big_sepM_bupd. iApply (big_sepM_impl with "HM"). iIntros "!>" (?? ?) "[H1 H2]". *)
  (*     destruct x as (o&p&P). simpl. destruct o; [done | | done]. *)
  (*     destruct a as (a&b). iDestruct "H1" as "(%&%&Hb&Haa&Hl)". destruct (decide (k ∈ L)). *)
  (*     - iDestruct "H2" as "(%&%&Hc&HF)". *)
  (*       iMod (oblG_transfer_spend with "[Hb Hc]") as "(%&%&Hb)"; first iFrame. *)
  (*       iModIntro. iFrame. iExists a2. iSplit; [|done]. iPureIntro. *)
  (*       apply WFOCM.lt_exists_right. exists c. split; [auto|]. by etransitivity. *)
  (*     - iDestruct "H2" as %[b' Hb']. iModIntro. iFrame. iPureIntro. split; first done. eauto. *)
  (*   } *)
  (*   iAssert (|==> ∃ Obls', ([∗ map] k ↦ x ∈ (Obls' : gmap positive (obl_state * (prop_of ps * iProp Σ))), *)
  (*                             let (y, y0) := (x : obl_state * (prop_of ps * iProp Σ)) in *)
  (*                             match y with *)
  (*                             | obl_init (a, _) => *)
  (*                                 (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblG_transfer_supply k a' ∗ oblG_idle k (1/2/2) ∗ oblG_live k (1/2/2)) *)
  (*                             | obl_live (a, _) => *)
  (*                                 (∃ a' : A, ⌜a' /≤ a⌝ ∗ oblG_transfer_supply k a' ∗ oblG_active_auth k ∗ oblG_live k (1/2/2)) *)
  (*                             | obl_done P1 => (let (P2, R) := y0 in ⌜P1 ≡ P2⌝ ∗ ▷ R ∗ oblG_active_auth k ∗ oblG_done_auth k) *)
  (*                             end) ∗ *)
  (*                          (⌜ snd <$> Obls = snd <$> Obls' ⌝) ∗ *)
  (*                          (⌜ (fst <$> Obls) ↪ₚ (fst <$> Obls')⌝) ∗ *)
  (*                          (⌜ map_Forall (λ i o, match o with | obl_live (a, b) => (if decide (i ∈ L) then F i b else R i b) | _ => True end) (fst <$> Obls') ⌝) *)
  (*           )%I with "[HM]" as ">HM". *)
  (*   { clear Ω HO. iStopProof. pattern Obls. revert Obls. apply map_ind. *)
  (*     { iIntros "_". iExists ∅. rewrite big_sepM_empty. iPureIntro. split; first auto. split; first done. *)
  (*       rewrite !fmap_empty. split; [|done]. intros. apply map_Forall2_empty. *)
  (*     } *)
  (*     intros i (o&P&Q) Obls Hlu IH. iIntros "H". iDestruct (big_sepM_insert _ _ _ _ Hlu with "H") as "[H HM]". *)
  (*     iDestruct (IH with "HM") as ">(%&HM&%Hd&%Hp&%Hf)". clear IH. *)
  (*     assert (Hdom : dom Obls = dom Obls'). *)
  (*     { rewrite <- (dom_fmap_L snd Obls), <- (dom_fmap_L snd Obls'). by rewrite Hd. } *)
  (*     assert (Hlu2 : Obls' !! i = None). *)
  (*     { apply not_elem_of_dom. apply not_elem_of_dom in Hlu. set_solver. } *)
  (*     destruct o. *)
  (*     - iModIntro. iExists (<[i:=(obl_init a, (P, Q))]>Obls'). iSplitL. *)
  (*       + iApply big_sepM_insert; first done. iFrame. *)
  (*       + iPureIntro. repeat split. *)
  (*         * rewrite !fmap_insert. rewrite Hd. done. *)
  (*         * rewrite !fmap_insert. apply map_Forall2_insert. *)
  (*           { by rewrite lookup_fmap Hlu. } *)
  (*           { by rewrite lookup_fmap Hlu2. } *)
  (*           simpl. split; auto. *)
  (*         * rewrite fmap_insert. apply map_Forall_insert. *)
  (*           { by rewrite lookup_fmap Hlu2. } *)
  (*           split; auto. done. *)
  (*     - destruct a as [a b]. case_decide. *)
  (*       { iDestruct "H" as "(%&%&%&%&Hb&Hi&Hl&%)". destruct H2. *)
  (*         iMod (oblG_transfer_supply_mon _ _ _ H1 with "Hb") as "Hb". *)
  (*         iModIntro. iExists (<[i:=(obl_live (a0, x), (P, Q))]>Obls'). iSplitL. *)
  (*         - iApply big_sepM_insert; first done. by iFrame. *)
  (*         - iPureIntro. repeat split. *)
  (*           + rewrite !fmap_insert. by rewrite Hd. *)
  (*           + rewrite !fmap_insert. simpl. apply map_Forall2_insert. *)
  (*             { by rewrite lookup_fmap Hlu. } *)
  (*             { by rewrite lookup_fmap Hlu2. } *)
  (*             simpl; split; auto. by econstructor 1. *)
  (*           + rewrite fmap_insert. apply map_Forall_insert. *)
  (*             { by rewrite lookup_fmap Hlu2. } *)
  (*             split; auto. simpl. case_decide; auto. set_solver. *)
  (*       } *)
  (*       { iDestruct "H" as "((%&%&Hb&Ha&Hl)&%)". destruct H1 as [b1 Hb1]. *)
  (*         iModIntro. iExists (<[i:=(obl_live (a, b1), (P, Q))]>Obls'). iSplitL. *)
  (*         - iApply big_sepM_insert; first done. by iFrame. *)
  (*         - iPureIntro. repeat split. *)
  (*           + rewrite !fmap_insert. by rewrite Hd. *)
  (*           + rewrite !fmap_insert. simpl. apply map_Forall2_insert. *)
  (*             { by rewrite lookup_fmap Hlu. } *)
  (*             { by rewrite lookup_fmap Hlu2. } *)
  (*             simpl; split; auto. destruct Hb1. econstructor 2; auto. *)
  (*           + rewrite fmap_insert. apply map_Forall_insert. *)
  (*             { by rewrite lookup_fmap Hlu2. } *)
  (*             split; auto. simpl. destruct Hb1. case_decide; done. *)
  (*       } *)
  (*     - iModIntro. iExists (<[i:=(obl_done P0, (P, Q))]>Obls'). iSplitL. *)
  (*       + iApply big_sepM_insert; first done. iFrame. *)
  (*       + iPureIntro. repeat split. *)
  (*         * rewrite !fmap_insert. rewrite Hd. done. *)
  (*         * rewrite !fmap_insert. apply map_Forall2_insert. *)
  (*           { by rewrite lookup_fmap Hlu. } *)
  (*           { by rewrite lookup_fmap Hlu2. } *)
  (*           simpl. split; auto. *)
  (*         * rewrite fmap_insert. apply map_Forall_insert. *)
  (*           { by rewrite lookup_fmap Hlu2. } *)
  (*           split; auto. done. *)
  (*   } *)
  (*   iDestruct "HM" as "(%&HM&%&%&%)". iModIntro. iExists (fst <$> Obls'). rewrite -lock. iSplitL. *)
  (*   - iExists Obls'. iSplit; first done. rewrite <-H. iFrame. *)
  (*   - iPureIntro. split; simpl; auto. intros. subst Ω. done. *)
  (* Qed. *)

  (* Lemma osat_done_open Ω i P R : *)
  (*   osat Ω ∗ oblG_done i ∗ oblG_goal i P R *)
  (*   ⊢ (▷ R) ∗ (▷ R -∗ osat Ω). *)
  (* Proof. *)
  (*   iIntros "(Ho & #Hd & #Hg)". *)
  (*   iPoseProof (osat_obl_is_done with "[Ho]") as "%Hdone"; [iFrame; eauto|]. *)
  (*   rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)". *)
  (*   iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done|]. *)
  (*   iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]". *)
  (*   subst. assert (∃ P', o = obl_done P' ∧ P' ≡ P). *)
  (*   { rewrite lookup_fmap IN in Hdone. destruct Hdone as (?&?&?). inv H. exists x. done. } *)
  (*   destruct H as (P'&?&?). subst. *)
  (*   iDestruct "Hc" as "(HP&HQ&Haa&Hda)". iSplitL "HQ". *)
  (*   { iNext. by iRewrite "HPQ" in "HQ". } *)
  (*   { iIntros "HR". iExists Obls. iSplit; [iPureIntro; done |]. *)
  (*     iFrame. iApply (big_sepM_delete _ _ i); [eauto |]. *)
  (*     iFrame. iNext. by iRewrite "HPQ". *)
  (*   } *)
  (* Qed. *)

  (* Lemma osat_done_open_pers Ω i P R : *)
  (*   Persistent R → *)
  (*   osat Ω ∗ oblG_done i ∗ oblG_goal i P R *)
  (*   ⊢ osat Ω ∗ ▷ R. *)
  (* Proof. *)
  (*   iIntros (PP) "H". iPoseProof (osat_done_open with "H") as "[#HP Ho]". *)
  (*   iSplitL; [|done]. iApply "Ho". done. *)
  (* Qed. *)

End osat.

(* Allocation of an initial obligation protocol. *)
Lemma osat_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGpreS ps T Σ} `{obl_class A ps T} :
  ⊢ |==> ∃ _ : osatGS ps T Σ, osat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (prodR _ _))) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γT) "HT";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=agreeR (leibnizO A)) ⊤)) as (γB) "HB";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO T))⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (OsatG SI _ WFA _ _ _ _ γG γS γT γB γO γC).
  rewrite /osat -lock.
  iSplitL "HG"; first (iExists ∅; by iFrame).
  replace (⊤ ∖ gset_to_coPset (dom (∅ : obl_states' _))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
