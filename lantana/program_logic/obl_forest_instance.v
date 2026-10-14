(** * The instance [obl_forest_lantana] of the obligation-forest interface

    The only file that names the implementation: the model update of the program logic over
    the obligation model ([omodel], base_logic/opreds.v), the instance, the bridges from the
    projections to the model, and the facts about the model that the trace layer and the
    adequacy proofs read. *)

From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.base_logic Require Import opreds.
From lantana.program_logic Require Export obl_forest_rules.
Import uPred.

(** * The model update: a fancy model update that keeps the history interpretation *)
Local Definition sfmupd_model_def `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} `{!TemporalInterp Λ Σ}
  E1 E2 : iPropO Σ -d> iPropO Σ :=
  (λ P, ∀ h n σ Θ κs, history_tinterp h n σ Θ κs -∗
                      |={E1,E2:n,dom Θ}=>m history_tinterp h n σ Θ κs ∗ P)%I.
Local Definition sfmupd_model_aux : seal (@sfmupd_model_def). Proof. by eexists. Qed.
Local Definition sfmupd_model := sfmupd_model_aux.(unseal).
Global Arguments sfmupd_model {SI Λ Σ _ _ _ _}.
Local Lemma sfmupd_model_unseal `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} `{!TemporalInterp Λ Σ} :
  sfmupd_model = @sfmupd_model_def SI Λ Σ _ _ _ _.
Proof. rewrite -sfmupd_model_aux.(seal_eq) //. Qed.
Local Ltac unfold_sfmupd_model := rewrite sfmupd_model_unseal /sfmupd_model_def.

(** Its three core rules, and the model updates of the forest ([omodel.*_mupd]) under it. *)
Section model_update.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!TemporalInterp Λ Σ}.
  Implicit Types P Q : iProp Σ.

  Local Instance sfmupd_model_ne E1 E2 : NonExpansive (sfmupd_model E1 E2).
  Proof. intros n P1 P2 HP. unfold_sfmupd_model. do 14 (f_equiv || done). Qed.

  Local Lemma fupd_sfmupd_model E1 E2 P : (|={E1,E2}=> P) ⊢ sfmupd_model E1 E2 P.
  Proof. unfold_sfmupd_model. iIntros ">Hupd %%%%% SI". iModIntro. iFrame. Qed.

  Local Lemma sfmupd_model_bind E1 E2 E3 P Q :
    (P -∗ sfmupd_model E2 E3 Q) ⊢ sfmupd_model E1 E2 P -∗ sfmupd_model E1 E3 Q.
  Proof.
    iIntros "H HP". unfold_sfmupd_model. iIntros "%%%%% SI".
    iMod ("HP" with "SI") as "[SI HP]".
    iPoseProof ("H" with "HP SI") as "H". done.
  Qed.

  Local Lemma thread_terminate_model E i :
    omodel.parP_kids (PThread i) ∅ -∗ sfmupd_model E E (omodel.thP_done i).
  Proof.
    unfold_sfmupd_model. iIntros "T %%%%% $".
    iMod (omodel.thread_terminate_mupd with "T") as "$". auto.
  Qed.

  Local Lemma obl_new_model E p K ℓ μ :
    parent_le omodel.witP_layer p ℓ -∗
    omodel.parP_kids p K -∗
    sfmupd_model E E
      (∃ k, ⌜ k ∉ K ⌝ ∗ omodel.parP_kids p ({[k]} ∪ K) ∗ omodel.parP_kids (PObl k) ∅ ∗
            omodel.oblP_assigned k 1 ∗ omodel.oblP_fuel k ℓ μ ∗ omodel.witP_layer k ℓ).
  Proof.
    unfold_sfmupd_model. iIntros "B Kp %%%%% $".
    iMod (omodel.obl_new_mupd with "B Kp") as "$". auto.
  Qed.

  Local Lemma obl_new_discharged_model E ℓ :
    ⊢ sfmupd_model E E (∃ k, omodel.oblP_discharged k ∗ omodel.witP_layer k ℓ).
  Proof.
    unfold_sfmupd_model. iIntros "%%%%% $". iMod omodel.obl_new_discharged_mupd as "$". auto.
  Qed.

  Local Lemma obl_move_model E p1 p2 K1 K2 k ℓ :
    k ∈ K1 →
    parent_below omodel.witP_layer p2 ℓ -∗
    omodel.parP_kids p1 K1 -∗ omodel.parP_kids p2 K2 -∗ omodel.oblP_fuel k ℓ 1 -∗
    sfmupd_model E E
      (⌜ k ∉ K2 ⌝ ∗ omodel.parP_kids p1 (K1 ∖ {[k]}) ∗ omodel.parP_kids p2 ({[k]} ∪ K2)).
  Proof.
    unfold_sfmupd_model. iIntros (Hk) "B K1 K2 F %%%%% $".
    iMod (omodel.obl_move_mupd with "B K1 K2 F") as "$"; auto.
  Qed.

  Local Lemma obl_move_up_model E p K k Kk x :
    k ∈ K → x ∈ Kk →
    omodel.parP_kids p K -∗ omodel.parP_kids (PObl k) Kk -∗
    sfmupd_model E E
      (⌜ x ∉ K ⌝ ∗ omodel.parP_kids p ({[x]} ∪ K) ∗ omodel.parP_kids (PObl k) (Kk ∖ {[x]})).
  Proof.
    unfold_sfmupd_model. iIntros (Hk Hx) "Kp Kk %%%%% $".
    iMod (omodel.obl_move_up_mupd with "Kp Kk") as "$"; auto.
  Qed.

  Local Lemma obl_check_witness_model E r ℓ :
    omodel.witP_layer r ℓ -∗
    sfmupd_model E E (omodel.witP_cred r Ord.O ∨ omodel.oblP_discharged r).
  Proof.
    unfold_sfmupd_model. iIntros "#W %%%%% $".
    iMod (omodel.obl_check_witnesses_mupd _ _ {[r]} with "[]") as "H".
    { rewrite big_sepS_singleton. eauto. }
    rewrite big_sepS_singleton. by iModIntro.
  Qed.

  Local Lemma obl_discharge_leaf_model E p K k :
    k ∈ K →
    omodel.parP_kids p K -∗ omodel.parP_kids (PObl k) ∅ -∗ omodel.oblP_assigned k 1 -∗
    sfmupd_model E E (omodel.parP_kids p (K ∖ {[k]}) ∗ omodel.oblP_discharged k).
  Proof.
    unfold_sfmupd_model. iIntros (Hk) "Kp Kk Ga %%%%% $".
    iMod (omodel.obl_discharge_mupd with "Kp Kk Ga") as "[$ $]"; auto.
  Qed.
End model_update.

(** * The instance *)
Section instance.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.

  Global Instance obl_forest_lantana : oblf.obl_forest_interface := {|
    oblf.parP_kids := omodel.parP_kids;
    oblf.thP_done := omodel.thP_done;
    oblf.oblP_assigned := omodel.oblP_assigned;
    oblf.oblP_discharged := omodel.oblP_discharged;
    oblf.oblP_fuel := omodel.oblP_fuel;
    oblf.oblP_inv := omodel.oblP_inv;
    oblf.witP_layer := omodel.witP_layer;
    oblf.witP_cred := omodel.witP_cred;
    oblf.wit_fuels := omodel.wit_fuels;

    oblf.sfmupd TI := @sfmupd_model _ _ _ _ _ _ TI;
    oblf.sfmupd_ne TI := sfmupd_model_ne;
    oblf.fupd_sfmupd TI := fupd_sfmupd_model;
    oblf.sfmupd_bind TI := sfmupd_model_bind;

    oblf.parP_kids_timeless := omodel.parP_kids_timeless;
    oblf.thP_done_timeless := omodel.thP_done_timeless;
    oblf.thP_done_persistent := omodel.thP_done_persistent;
    oblf.oblP_assigned_timeless := omodel.oblP_assigned_timeless;
    oblf.oblP_assigned_fractional := omodel.oblP_assigned_fractional;
    oblf.oblP_discharged_timeless := omodel.oblP_discharged_timeless;
    oblf.oblP_discharged_persistent := omodel.oblP_discharged_persistent;
    oblf.oblP_fuel_timeless := omodel.oblP_fuel_timeless;
    oblf.oblP_inv_persistent := omodel.oblP_inv_persistent;
    oblf.oblP_inv_contractive_1 := omodel.oblP_inv_contractive_1;
    oblf.oblP_inv_contractive_2 := omodel.oblP_inv_contractive_2;
    oblf.witP_layer_timeless := omodel.witP_layer_timeless;
    oblf.witP_layer_persistent := omodel.witP_layer_persistent;
    oblf.witP_cred_timeless := omodel.witP_cred_timeless;
    oblf.wit_fuels_timeless := omodel.wit_fuels_timeless;
    oblf.wit_fuels_empty_persistent := omodel.wit_fuels_empty_persistent;

    oblf.oblP_assigned_discharged_false := omodel.oblP_assigned_discharged_false;
    oblf.oblP_kids_discharged_false := omodel.oblP_kids_discharged_false;
    oblf.parP_kids_discharged := omodel.parP_kids_discharged;
    oblf.oblP_fuel_proper := omodel.oblP_fuel_proper;
    oblf.oblP_fuel_mon_gen := omodel.oblP_fuel_mon_gen;
    oblf.oblP_fuel_add := omodel.oblP_fuel_add;
    oblf.oblP_fuel_extend := omodel.oblP_fuel_extend;
    oblf.witP_cred_proper := omodel.witP_cred_proper;
    oblf.witP_cred_mon := omodel.witP_cred_mon;
    oblf.witP_cred_split := omodel.witP_cred_split;

    oblf.oblP_inv_alloc_assigned := omodel.oblP_inv_alloc_assigned;
    oblf.oblP_inv_alloc_discharged := omodel.oblP_inv_alloc_discharged;
    oblf.oblP_inv_acc := omodel.oblP_inv_acc;

    oblf.wit_fuels_init := omodel.wit_fuels_init;
    oblf.wit_fuels_witP_layer := omodel.wit_fuels_witP_layer;
    oblf.wit_fuels_add := omodel.wit_fuels_add;
    oblf.wit_fuels_decr := omodel.wit_fuels_decr;

    oblf.thread_terminate TI := thread_terminate_model;
    oblf.obl_new TI := obl_new_model;
    oblf.obl_new_discharged TI := obl_new_discharged_model;
    oblf.obl_move TI := obl_move_model;
    oblf.obl_move_up TI := obl_move_up_model;
    oblf.obl_check_witness TI := obl_check_witness_model;
    oblf.obl_discharge_leaf TI := obl_discharge_leaf_model;

    oblf.step_progress := omodel.mprog_step_kids;
    oblf.step_fork := omodel.mphys_step_kids;
  |}.
End instance.

(** * Bridges from the projections at the instance to the model *)
Section bridges.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.

  Lemma parP_kids_lantana : @oblf.parP_kids _ _ _ _ _ _ obl_forest_lantana = omodel.parP_kids.
  Proof. done. Qed.
  Lemma thP_done_lantana : @oblf.thP_done _ _ _ _ _ _ obl_forest_lantana = omodel.thP_done.
  Proof. done. Qed.
  Lemma oblP_assigned_lantana :
    @oblf.oblP_assigned _ _ _ _ _ _ obl_forest_lantana = omodel.oblP_assigned.
  Proof. done. Qed.
  Lemma oblP_discharged_lantana :
    @oblf.oblP_discharged _ _ _ _ _ _ obl_forest_lantana = omodel.oblP_discharged.
  Proof. done. Qed.
  Lemma oblP_fuel_lantana : @oblf.oblP_fuel _ _ _ _ _ _ obl_forest_lantana = omodel.oblP_fuel.
  Proof. done. Qed.
  Lemma oblP_inv_lantana : @oblf.oblP_inv _ _ _ _ _ _ obl_forest_lantana = omodel.oblP_inv.
  Proof. done. Qed.
  Lemma witP_layer_lantana : @oblf.witP_layer _ _ _ _ _ _ obl_forest_lantana = omodel.witP_layer.
  Proof. done. Qed.
  Lemma witP_cred_lantana : @oblf.witP_cred _ _ _ _ _ _ obl_forest_lantana = omodel.witP_cred.
  Proof. done. Qed.
  Lemma wit_fuels_lantana : @oblf.wit_fuels _ _ _ _ _ _ obl_forest_lantana = omodel.wit_fuels.
  Proof. done. Qed.
  Lemma sfmupd_lantana :
    @oblf.sfmupd _ _ _ _ _ _ obl_forest_lantana = @sfmupd_model _ _ _ _ _ _.
  Proof. done. Qed.
End bridges.

(** Unfolding the predicates, and the model update, at the instance (for the proofs that read
    the model: the registry, the runs of the trace layer, adequacy). *)
Ltac unfold_opreds :=
  rewrite ?parP_kids_lantana ?thP_done_lantana ?oblP_assigned_lantana ?oblP_discharged_lantana
    ?oblP_fuel_lantana ?oblP_inv_lantana ?witP_layer_lantana ?witP_cred_lantana
    ?wit_fuels_lantana;
  omodel.unfold_opreds.
Ltac unfold_sfmupd := rewrite sfmupd_lantana sfmupd_model_unseal /sfmupd_model_def.

(** * Facts about the model at the instance *)
Section model_facts.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.

  (** The defining equation of the model update. *)
  Lemma sfmupd_unfold `{!TemporalInterp Λ Σ} E1 E2 (P : iProp Σ) :
    (|={E1,E2}=>m P) = (∀ h n σ Θ κs, history_tinterp h n σ Θ κs -∗
                         |={E1,E2:n,dom Θ}=>m history_tinterp h n σ Θ κs ∗ P)%I.
  Proof. by unfold_sfmupd. Qed.

  Lemma oblP_discharged_unfold k : oblP_discharged k ⊣⊢ oblG_elem k ∗ oblG_discharged k.
  Proof. rewrite oblP_discharged_lantana. apply omodel.oblP_discharged_unfold. Qed.

  (** The children predicates of the initial threads (for adequacy). *)
  Lemma thP_kids_alloc_threads Ω π TP :
    π ## TP →
    othread TP ∗ oforest Ω TP
    ⊢ |==> othread (TP ∪ π) ∗ oforest Ω (TP ∪ π) ∗ [∗ set] i ∈ π, thP_kids i ∅.
  Proof. rewrite parP_kids_lantana. apply omodel.thP_kids_alloc_threads. Qed.

  (** Running an m-update against the model, as the adequacy proofs do. *)
  Lemma all_interp_sfmupd_steps `{!TemporalInterp Λ Σ} γ E1 E2 h n σ Θ κs g v Ω W (P : iProp Σ) :
    owit_inv_lb_mon γ →
    owit_inv_lb γ Ω W →
    (|={E1,E2}=>m P) -∗ history_tinterp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={E1,E2}=∗
    (P ∗ history_tinterp h n σ Θ κs ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb γ Ω' W' ⌝ ∗
                    model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (MON LB) "HP HI MI". unfold_sfmupd. iPoseProof ("HP" with "HI") as ">HP".
    iMod (model_interp_mupd_steps γ with "HP MI") as "(>($& $)& $)"; done.
  Qed.
End model_facts.

(** Running the m-updates of several threads, with the fair scheduler. *)
Section run_sfmupd.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!TemporalInterp Λ Σ}.

  Lemma all_interp_sfmupd_steps_gmap (γ : thread_id → nat) E h n σ Θ κs g v Ω W
    (A : Type) (TQ : gmap thread_id ((expr Λ) * A)) (P : thread_id → (expr Λ) → A → iProp Σ) :
    (owit_inv_lb (fair_measure γ) Ω W) →
    ([∗ map] i ↦ '(e, a) ∈ TQ, |={E}=>m (P i e a)) -∗
    history_tinterp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={E}=∗
    (([∗ map] i ↦ '(e, a) ∈ TQ, (P i e a)) ∗ history_tinterp h n σ Θ κs ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb (fair_measure γ) Ω' W' ⌝ ∗
                    model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (LB) "PS HI MI".
    iAssert (|={E}=>m [∗ map] i ↦ '(e, a) ∈ TQ, P i e a)%I with "[PS]" as "PS".
    { iApply big_sepM_sfmupd. iApply (big_sepM_impl with "PS"). iIntros "!>" (k [e a] _) "H". done. }
    iMod (all_interp_sfmupd_steps (fair_measure γ) with "PS HI MI") as "$".
    { split; [apply fair_measure_mon | apply fair_measure_le_ub]. }
    { done. }
    done.
  Qed.
End run_sfmupd.
