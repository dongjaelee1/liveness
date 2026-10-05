(** * The forest model is an instance of the obligation-forest interface

    [obl_forest_lantana] instantiates [oblf.obl_forest_interface] with the predicates of
    [opreds.v]; the updates are the model-update rules of [sfmupd.v] and the steps those of
    [model_physical_updates.v]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.program_logic Require Export obl_forest.

Section instance.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!TemporalInterp Λ Σ}.

  (** ** Structural properties *)
  Lemma thP_done_timeless_lantana i : Timeless (thP_done i).
  Proof. unfold_opreds. apply _. Qed.

  (** ** Fuel and credits *)
  Lemma oblP_fuel_proper_lantana k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 == ℓ2)%ordi →
    (measure_rep ℓ1 μ1 == measure_rep ℓ2 μ2)%ord →
    oblP_fuel k ℓ1 μ1 ⊣⊢ oblP_fuel k ℓ2 μ2.
  Proof.
    intros Hℓ Hμ. rewrite (oblP_fuel_layer_eq k ℓ1 ℓ2 μ1 Hℓ) (oblP_fuel_eq k ℓ2 μ1 μ2); first done.
    etrans; last exact Hμ. symmetry. by apply measure_rep_layer_eq.
  Qed.

  Lemma oblP_fuel_extend_lantana k ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    oblP_fuel k ℓ2 1 ==∗ oblP_fuel k ℓ1 μ.
  Proof. iIntros (?) "F". by iApply oblP_fuel_extend. Qed.

  Lemma witP_cred_proper_lantana k a0 a1 :
    (a0 == a1)%ord → witP_cred k a0 ⊣⊢ witP_cred k a1.
  Proof. intros Ha. by rewrite (witP_cred_eq k a0 a1 Ha). Qed.

  (** ** Obligation invariants *)
  Lemma oblP_inv_acc_lantana E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))) ∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". iMod (oblP_inv_acc with "I") as "[$ ACC]"; first done.
    iIntros "!> V". iApply "ACC". iNext. by iApply oblP_variant_unfold.
  Qed.

  (** ** Forking threads *)
  Lemma step_fork_lantana n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (([∗ set] j ∈ π, parP_kids (PThread j) ∅) ={∅}=∗ P) -∗
    @={n1,n2,Θ1,Θ2}=> P.
  Proof. iIntros (???) "H". iApply mphys_step; [done..|]. by iModIntro. Qed.

  Global Instance obl_forest_lantana : oblf.obl_forest_interface := {|
    oblf.parP_kids := parP_kids;
    oblf.thP_done := thP_done;
    oblf.oblP_assigned := oblP_assigned;
    oblf.oblP_discharged := oblP_discharged;
    oblf.oblP_fuel := oblP_fuel;
    oblf.oblP_inv := oblP_inv;
    oblf.witP_layer := witP_layer;
    oblf.witP_cred := witP_cred;
    oblf.wit_fuels := wit_fuels;

    oblf.parP_kids_timeless := parP_kids_timeless;
    oblf.thP_done_timeless := thP_done_timeless_lantana;
    oblf.thP_done_persistent := thP_done_persistent;
    oblf.oblP_assigned_timeless := oblP_assigned_timeless;
    oblf.oblP_assigned_fractional := oblP_assigned_fractional;
    oblf.oblP_discharged_timeless := oblP_discharged_timeless;
    oblf.oblP_discharged_persistent := oblP_discharged_persistent;
    oblf.oblP_fuel_timeless := oblP_fuel_timeless;
    oblf.oblP_inv_persistent := oblP_inv_persistent;
    oblf.oblP_inv_contractive_1 := oblP_inv_contractive_1;
    oblf.oblP_inv_contractive_2 := oblP_inv_contractive_2;
    oblf.witP_layer_timeless := witP_layer_timeless;
    oblf.witP_layer_persistent := witP_layer_persistent;
    oblf.witP_cred_timeless := witP_cred_timeless;
    oblf.wit_fuels_timeless := wit_fuels_timeless;
    oblf.wit_fuels_empty_persistent := wit_fuels_empty_persistent;

    oblf.oblP_assigned_discharged_false := oblP_assigned_discharged_false;
    oblf.oblP_kids_discharged_false := oblP_kids_discharged_false;
    oblf.parP_kids_discharged := parP_kids_discharged;
    oblf.oblP_fuel_proper := oblP_fuel_proper_lantana;
    oblf.oblP_fuel_mon_gen := oblP_fuel_mon_gen;
    oblf.oblP_fuel_add := oblP_fuel_add;
    oblf.oblP_fuel_extend := oblP_fuel_extend_lantana;
    oblf.witP_cred_proper := witP_cred_proper_lantana;
    oblf.witP_cred_mon := witP_cred_mon;
    oblf.witP_cred_split := witP_cred_split;

    oblf.oblP_inv_alloc_assigned := oblP_inv_alloc_assigned;
    oblf.oblP_inv_alloc_discharged := oblP_inv_alloc_discharged;
    oblf.oblP_inv_acc := oblP_inv_acc_lantana;

    oblf.wit_fuels_init := wit_fuels_init;
    oblf.wit_fuels_witP_layer := wit_fuels_witP_layer;
    oblf.wit_fuels_add := wit_fuels_add;
    oblf.wit_fuels_decr := wit_fuels_decr;

    oblf.thread_terminate := thread_terminate;
    oblf.obl_new := obl_new;
    oblf.obl_new_discharged := obl_new_discharged;
    oblf.obl_move := obl_move;
    oblf.obl_move_up := obl_move_up;
    oblf.obl_check_witness := obl_check_witness;

    oblf.obl_discharge := obl_discharge_leaf;

    oblf.step_progress := mprog_step_kids;
    oblf.step_fork := step_fork_lantana;
  |}.
End instance.
