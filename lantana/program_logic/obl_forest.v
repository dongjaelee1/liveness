(** * The obligation-forest interface: the core of the logic

    [oblf.obl_forest_interface]: the obligation predicates, the model update [|={E1,E2}=>m P]
    and the rules of both. Every live obligation is a child of one parent, a thread or an
    obligation ([parP_kids p K]). The derived rules are in obl_forest_rules.v, the instance
    in obl_forest_instance.v. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.algebra Require Export layer.
From lantana.program_logic Require Export temporal_class.
From lantana.base_logic Require Export model_physical_updates.
Import uPred.

(** * Parents *)
(** One unit of fuel at layer [ℓ] is enough to hang below [p]: always below a thread; below an
    obligation [q], [ℓ] must be above a witness layer of [q] (given by [wl], instantiated with
    [witP_layer]). *)
Definition parent_below `{SI : sidx} {Σ : gFunctors} (wl : oid → layer → iProp Σ)
    (p : parent) (ℓ : layer) : iProp Σ :=
  match p with
  | PThread _ => True
  | PObl q => ∃ ℓq, ⌜ (ℓq < ℓ)%ordi ⌝ ∗ wl q ℓq
  end%I.

(** A new obligation at layer [ℓ] may be created below [p]: always below a thread; below an
    obligation [q], [ℓ] must be at least a witness layer of [q]. A move needs a strictly larger
    layer ([parent_below]): moving an obligation below one of the same layer is unsound. *)
Definition parent_le `{SI : sidx} {Σ : gFunctors} (wl : oid → layer → iProp Σ)
    (p : parent) (ℓ : layer) : iProp Σ :=
  match p with
  | PThread _ => True
  | PObl q => ∃ ℓq, ⌜ (ℓq <= ℓ)%ordi ⌝ ∗ wl q ℓq
  end%I.

Module oblf.

(** * The class

    In the model ([oforest.v]), an obligation owned by thread [i] is in the tree of [i], and
    below an obligation [c] a child stores a piece of fuel above the fuel of [c]. A step of [i]
    burns a unit of each child of [i]; deeper obligations of [i] burn a unit split off their
    piece. A move pays a unit at a layer that dominates the new parent; if the owner changes,
    the subtree changes owner in the same round.

    The model update is a field for every interpretation of the temporal layer
    ([TemporalInterp]), so that the predicates do not depend on one. *)
Class obl_forest_interface `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} := {
  (** ** Predicates
      [parP_kids p K]: the children of [p] are [K]; for a thread, it is also running, for an
      obligation, it exists exactly while the obligation is live and in the forest.
      [oblP_assigned k q]: [k] is live ([q] a fraction). [oblP_fuel k ℓ μ]: fuel [μ] of [k] at
      layer [ℓ]. [oblP_inv N k P R]: invariant over the status of [k], [P] while live, [R] once
      discharged. [witP_layer k ℓ]: a witness of [k] at layer [ℓ]; [witP_cred]: its credits;
      [wit_fuels k ℓ α F]: the witness induction with budget [α], carrying the fuels [F]. *)
  parP_kids : parent → oids → iProp Σ;
  thP_done : positive → iProp Σ;
  oblP_assigned : oid → Qp → iProp Σ;
  oblP_discharged : oid → iProp Σ;
  oblP_fuel : oid → layer → measure → iProp Σ;
  oblP_inv : namespace → oid → iProp Σ → iProp Σ → iProp Σ;
  witP_layer : oid → layer → iProp Σ;
  witP_cred : oid → obl_fuel → iProp Σ;
  wit_fuels : oid → layer → obl_fuel → gmap oid (layer * measure) → iProp Σ;

  (** ** The model update [|={E1,E2}=>m P]
      A fancy update that may also change the model; the usual rules are derived from these
      three. *)
  sfmupd `{!TemporalInterp Λ Σ} : coPset → coPset → iProp Σ → iProp Σ;
  #[global] sfmupd_ne :: ∀ `{!TemporalInterp Λ Σ} E1 E2, NonExpansive (sfmupd E1 E2);
  fupd_sfmupd `{!TemporalInterp Λ Σ} E1 E2 (P : iProp Σ) :
    (|={E1,E2}=> P) ⊢ sfmupd E1 E2 P;
  sfmupd_bind `{!TemporalInterp Λ Σ} E1 E2 E3 (P Q : iProp Σ) :
    (P -∗ sfmupd E2 E3 Q) ⊢ sfmupd E1 E2 P -∗ sfmupd E1 E3 Q;

  (** ** Structural properties *)
  #[global] parP_kids_timeless :: ∀ p K, Timeless (parP_kids p K);
  #[global] thP_done_timeless :: ∀ i, Timeless (thP_done i);
  #[global] thP_done_persistent :: ∀ i, Persistent (thP_done i);
  #[global] oblP_assigned_timeless :: ∀ k q, Timeless (oblP_assigned k q);
  #[global] oblP_assigned_fractional :: ∀ k, Fractional (oblP_assigned k);
  #[global] oblP_discharged_timeless :: ∀ k, Timeless (oblP_discharged k);
  #[global] oblP_discharged_persistent :: ∀ k, Persistent (oblP_discharged k);
  #[global] oblP_fuel_timeless :: ∀ k ℓ μ, Timeless (oblP_fuel k ℓ μ);
  #[global] oblP_inv_persistent :: ∀ N k P R, Persistent (oblP_inv N k P R);
  #[global] oblP_inv_contractive_1 :: ∀ N k R, Contractive (λ P, oblP_inv N k P R);
  #[global] oblP_inv_contractive_2 :: ∀ N k P, Contractive (λ R, oblP_inv N k P R);
  #[global] witP_layer_timeless :: ∀ k ℓ, Timeless (witP_layer k ℓ);
  #[global] witP_layer_persistent :: ∀ k ℓ, Persistent (witP_layer k ℓ);
  #[global] witP_cred_timeless :: ∀ k a, Timeless (witP_cred k a);
  #[global] wit_fuels_timeless :: ∀ k ℓ α F, Timeless (wit_fuels k ℓ α F);
  #[global] wit_fuels_empty_persistent :: ∀ k ℓ α, Persistent (wit_fuels k ℓ α ∅);

  (** ** Logical rules
      A live obligation is not discharged; a discharged one has no children predicate and is
      nobody's child. Fuel and credits are monotone and additive. *)
  oblP_assigned_discharged_false k q :
    oblP_assigned k q -∗ oblP_discharged k -∗ False;
  oblP_kids_discharged_false k K :
    parP_kids (PObl k) K -∗ oblP_discharged k -∗ False;
  parP_kids_discharged k p K :
    parP_kids p K -∗ oblP_discharged k -∗ ⌜ k ∉ K ⌝;

  oblP_fuel_proper k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 == ℓ2)%ordi →
    (measure_rep ℓ1 μ1 == measure_rep ℓ2 μ2)%ord →
    oblP_fuel k ℓ1 μ1 ⊣⊢ oblP_fuel k ℓ2 μ2;
  oblP_fuel_mon_gen k ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep ℓ1 μ1 <= measure_rep ℓ2 μ2)%ord →
    oblP_fuel k ℓ2 μ2 ==∗ oblP_fuel k ℓ1 μ1;
  oblP_fuel_add k ℓ μ1 μ2 :
    oblP_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2;
  oblP_fuel_extend k ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    oblP_fuel k ℓ2 1 ==∗ oblP_fuel k ℓ1 μ;

  witP_cred_proper k a0 a1 :
    (a0 == a1)%ord → witP_cred k a0 ⊣⊢ witP_cred k a1;
  witP_cred_mon k a0 a1 :
    (a0 <= a1)%ord → witP_cred k a1 ==∗ witP_cred k a0;
  witP_cred_split k a0 a1 :
    witP_cred k (a0 ⊕ a1)%ord ⊣⊢ witP_cred k a0 ∗ witP_cred k a1;

  (** ** Invariants over obligations *)
  oblP_inv_alloc_assigned E N k P R :
    oblP_assigned k (1/2) -∗ ▷ P ={E}=∗ oblP_inv N k P R;
  oblP_inv_alloc_discharged E N k P R :
    oblP_discharged k -∗ ▷ R ={E}=∗ oblP_inv N k P R;
  oblP_inv_acc E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))) ∗
    (▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R)) ={E ∖ ↑N,E}=∗ True);

  (** ** Witness induction
      Fuel above the layer of the witness can be stored in the induction, and comes back for
      each witness credit. *)
  wit_fuels_init k ℓ :
    witP_layer k ℓ -∗ ∃ α, wit_fuels k ℓ α ∅;
  wit_fuels_witP_layer k ℓ α F :
    wit_fuels k ℓ α F ==∗ witP_layer k ℓ;
  wit_fuels_add k ℓ1 α F f ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    wit_fuels k ℓ1 α F -∗ oblP_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k ℓ1 α (<[f:=(ℓ2, μ)]>F);
  wit_fuels_decr k ℓ α F :
    wit_fuels k ℓ α F -∗ witP_cred k Ord.one ==∗
    ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k ℓ α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m);

  (** ** Model updates that keep every obligation live
      A thread without children terminates. A new obligation below [p] at layer [ℓ]: below an
      obligation [q], [ℓ] is at least a witness layer of [q]. A move of [k] with its subtree
      burns a unit at a layer above the new parent; a move up to the grandparent is free.
      Checking a witness gives no credit, or tells that it is discharged. *)
  thread_terminate `{!TemporalInterp Λ Σ} E i :
    parP_kids (PThread i) ∅ -∗ sfmupd E E (thP_done i);
  obl_new `{!TemporalInterp Λ Σ} E p K ℓ μ :
    parent_le witP_layer p ℓ -∗
    parP_kids p K -∗
    sfmupd E E (∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ parP_kids (PObl k) ∅ ∗
                     oblP_assigned k 1 ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ);
  obl_new_discharged `{!TemporalInterp Λ Σ} E ℓ :
    ⊢ sfmupd E E (∃ k, oblP_discharged k ∗ witP_layer k ℓ);
  obl_move `{!TemporalInterp Λ Σ} E p1 p2 K1 K2 k ℓ :
    k ∈ K1 →
    parent_below witP_layer p2 ℓ -∗
    parP_kids p1 K1 -∗ parP_kids p2 K2 -∗ oblP_fuel k ℓ 1 -∗
    sfmupd E E (⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ parP_kids p2 ({[k]} ∪ K2));
  obl_move_up `{!TemporalInterp Λ Σ} E p K k Kk x :
    k ∈ K → x ∈ Kk →
    parP_kids p K -∗ parP_kids (PObl k) Kk -∗
    sfmupd E E (⌜ x ∉ K ⌝ ∗ parP_kids p ({[x]} ∪ K) ∗ parP_kids (PObl k) (Kk ∖ {[x]}));
  obl_check_witness `{!TemporalInterp Λ Σ} E r ℓ :
    witP_layer r ℓ -∗ sfmupd E E (witP_cred r Ord.O ∨ oblP_discharged r);

  (** ** Discharge
      A childless obligation [k] below [p] is discharged and leaves the forest. *)
  obl_discharge_leaf `{!TemporalInterp Λ Σ} E p K k :
    k ∈ K →
    parP_kids p K -∗ parP_kids (PObl k) ∅ -∗ oblP_assigned k 1 -∗
    sfmupd E E (parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k);

  (** ** Physical steps
      A step of thread [i] burns one unit of fuel of each child of [i] and gives one credit
      for each live witness in [R]. A step that forks the threads [π] gives each of them an
      empty set of children. *)
  step_progress n Θ i K R P :
    parP_kids (PThread i) K -∗
    ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ 1) -∗
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    (parP_kids (PThread i) K -∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)
     ={∅}=∗ P) -∗
    @={n,Θ,i}=↓ P;
  step_fork n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (([∗ set] j ∈ π, parP_kids (PThread j) ∅) ={∅}=∗ P) -∗
    @={n1,n2,Θ1,Θ2}=> P;
}.

(** The projections stay folded under [simpl] and [cbn]. *)
Global Arguments sfmupd {_ _ _ _ _ _ _ _} _ _ _%_I : simpl never.
Global Arguments parP_kids : simpl never.
Global Arguments thP_done : simpl never.
Global Arguments oblP_assigned : simpl never.
Global Arguments oblP_discharged : simpl never.
Global Arguments oblP_fuel : simpl never.
Global Arguments oblP_inv : simpl never.
Global Arguments witP_layer : simpl never.
Global Arguments witP_cred : simpl never.
Global Arguments wit_fuels : simpl never.

(** * Notations *)
Notation "'|={' E1 , E2 '}=>m' P" := (sfmupd E1 E2 P)
  (at level 20, P at level 200, format "|={ E1 , E2 }=>m  P").
Notation "'|={' E '}=>m' P" := (sfmupd E E P)
  (at level 20, P at level 200, format "|={ E }=>m  P").
(** The wand forms, as Iris' [P ={E1,E2}=∗ Q] and [P ={E}=∗ Q] for fancy updates. *)
Reserved Notation "P ={ E1 , E2 }=∗m Q"
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "'[' P  ={ E1 , E2 }=∗m  '/' '[' Q ']' ']'").
Reserved Notation "P ={ E }=∗m Q"
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  ={ E }=∗m  '/' '[' Q ']' ']'").
Notation "P ={ E1 , E2 }=∗m Q" := (P -∗ |={E1,E2}=>m Q)%I : bi_scope.
Notation "P ={ E1 , E2 }=∗m Q" := (P -∗ |={E1,E2}=>m Q) : stdpp_scope.
Notation "P ={ E }=∗m Q" := (P -∗ |={E}=>m Q)%I : bi_scope.
Notation "P ={ E }=∗m Q" := (P -∗ |={E}=>m Q) : stdpp_scope.

Notation thP_kids i K := (parP_kids (PThread i) K).
Notation oblP_kids k K := (parP_kids (PObl k) K).
Notation parP_below p ℓ := (parent_below witP_layer p ℓ).
Notation parP_le p ℓ := (parent_le witP_layer p ℓ).
(** [n] units of fuel of each obligation of a set, at any layers. *)
Notation oblP_fuels K n := ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ n)%I.
(** One witness credit: a step gives one to each live witness ([step_progress]), and each
    round of the witness induction consumes one ([wit_fuels_decr]). *)
Notation witP_cred1 r := (witP_cred r Ord.one).
(** No witness credit, as given by checking a witness ([obl_check_witness]). *)
Notation witP_cred0 r := (witP_cred r Ord.O).

End oblf.
Export oblf.
