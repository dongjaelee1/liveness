(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Import mono_nat.
From transfinite.base_logic.lib Require Export gen_heap proph_map.
(* From transfinite.base_logic.lib Require Export gen_heap proph_map gen_inv_heap. *)
From lantana.base_logic Require Export thread_map gen_inv_heap.
(** adequacy fixes step index to ordinals *)
From lantana.program_logic Require Export atomic adequacy.
From lantana.program_logic Require Import ectx_lifting.
From lantana.heap_lang Require Export class_instances.
From lantana.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.
From lantana.algebra Require Export ordinal_wfocm.

Class heap_stateGS Σ :=
  HeapStateGS {
      #[global] heap_stateGS_gen_heap_stateGS :: gen_heapGS loc (option val) Σ;
      #[global] heap_stateGS_inv_heap_stateGS :: inv_heapGS loc (option val) Σ;
      #[global] heap_stateGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
      #[global] heap_stateGS_thread_mapGS :: thread_mapGS thread_id (expr) Σ;
    }.

Definition heap_stateΣ : gFunctors :=
  #[gen_heapΣ loc (option val);
    inv_heapΣ loc (option val);
    proph_mapΣ proph_id (val * val);
    thread_mapΣ thread_id (expr)].

Global Instance subG_heap_stateΣ {Σ} : subG heap_stateΣ Σ → heap_stateGS Σ.
Proof.
  intros. econstructor.
  - econstructor.
    { eapply subG_gen_heapGpreS. solve_inG. }
    1,2: exact inhabitant.
  - econstructor.
    { eapply subG_inv_heapGpreS. solve_inG. }
    1: exact inhabitant.
  - econstructor.
    { eapply subG_proph_mapGpreS. solve_inG. }
    1: exact inhabitant.
  - econstructor.
    { eapply subG_thread_mapGpreS. solve_inG. }
    1: exact inhabitant.
Qed.

(** Since we use an [option val] instance of [gen_heap], we need to add a
[Some]. We also seal the definition to avoid confusion between the version from
[gen_heap], and our version with [Some]. That also helps for scopes and
coercions. *)
Local Definition pointsto_def `{heap_stateGS Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
                         (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.
Notation "l ↦ dq v" := (➢ (pred_pointsto l dq v))%F
                         (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : tf_scope.
Notation "l ↦ dq v" := (➢ (pred_pointsto l dq v))%P
                         (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : tp_scope.

(** Exact ownership of a thread's expression in its caller context. *)
Definition thread_expr `{heap_stateGS Σ}
    (i : thread_id) (C : list ectx_item) (e : expr) : iProp Σ :=
  thread i true (fill C e) 1.

(** Thread [i] has reached final value [v] at the empty context, not merely
    returned from a function within a larger thread expression. *)
Notation "'exits' v @ i" := (thread_expr i [] (of_val v))%I
  (at level 20, v, i at level 1, format "exits  v @ i") : bi_scope.
Notation "'exits' v @ i" := (➢ (pred_expr i [] (of_val v)))%F
  (at level 20, v, i at level 1, format "exits  v @ i") : tf_scope.
Notation "'exits' v @ i" := (➢ (pred_expr i [] (of_val v)))%P
  (at level 20, v, i at level 1, format "exits  v @ i") : tp_scope.

(** The terminal atom means actual value reachability, with no hidden context.
    This equivalence is purely semantic; clients establish its left-hand side
    under the behavior and fair-scheduling premises of adequacy. *)
Lemma exits_finally_iff (τ : trace heap_lang) i v :
  tp_trace (tp_finally (exits v@i))%P τ ↔
  ∃ n, τ.1 ≤ n ∧ (τ.2 n).1.1.1 !! i = Some (of_val v).
Proof.
  destruct τ as [m τf].
  change ((∃ n, m ≤ n ∧
    (let '((Θ, σ), _, _) := τf n in state_sat σ Θ (pred_expr i [] (of_val v))) ∧
    (∀ l, m ≤ l < n → True)) ↔
    ∃ n, m ≤ n ∧ (τf n).1.1.1 !! i = Some (of_val v)).
  split.
  - intros (n & Hn & H & _). exists n. split; first done.
    destruct (τf n) as [[[Θ σ] j] κ]. exact H.
  - intros (n & Hn & H). exists n. split; first done.
    split; last done. destruct (τf n) as [[[Θ σ] j] κ]. exact H.
Qed.

Definition state_interp `{!heap_stateGS Σ} (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  (gen_heap_interp σ.(heap) ∗
   thread_map_interp (dom Θ) Θ ∗
   proph_map_interp κs σ.(used_proph_id))%I.

Definition state_interp_aux `{!heap_stateGS Σ} (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  True%I.

(** State predicate. *)
Definition state_pred_interp `{!heap_stateGS Σ} (π : state_pred) : iProp Σ :=
  match π with
  | pred_pointsto l dq v =>
      pointsto l dq v
  | pred_expr i C e =>
      thread_expr i C e
  end.

Lemma thread_expr_read `{!heap_stateGS Σ} :
  ∀ (Θ : thread_pool heap_lang) i C e,
  thread_map_interp (dom Θ) Θ -∗ thread_expr i C e -∗ ⌜Θ !! i = Some (fill C e)⌝.
Proof.
  iIntros (????) "TI Ti".
  iPoseProof (thread_map_thread_read with "TI Ti") as "%". eauto.
Qed.

Lemma state_interp_wf `{!heap_stateGS Σ} :
  ∀ (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) (π : state_pred),
  state_interp σ Θ κs ∗ state_pred_interp π ⊢ ⌜state_sat σ Θ π⌝.
Proof.
  iIntros (????) "[(HI& TI& PI) SP]". destruct π; simpl.
  - rewrite pointsto_unseal /pointsto_def. iPoseProof (gen_heap_valid with "HI SP") as "%". eauto.
  - iPoseProof (thread_expr_read with "TI SP") as "%". eauto.
Qed.

(** We don't want this to be an instance, which can break iMod. *)
Definition heap_state_interp_class `{!heap_stateGS Σ} : state_interp_class heap_lang Σ :=
  Build_state_interp_class _ _ _ state_interp state_interp_aux state_pred_interp state_interp_wf.

(* Global Instance heap_state_interp_class `{!heap_stateGS Σ} : state_interp_class heap_lang Σ := { *)
(*     state_interp := state_interp; *)
(*     state_interp_aux := state_interp_aux; *)
(*     state_pred_interp := state_pred_interp; *)
(*     state_interp_wf := state_interp_wf; *)
(*   }. *)

Class heapGS Σ :=
  HeapGS {
      heapGS_temporalGS : temporalGS heap_lang Σ;
      (* heapGS_mupdGS : mupdGS Σ; *)
      (* heapGS_histGS : histGS.histGS Σ (state * thread_pool heap_lang * list (observation)); *)
      #[global] heapGS_heap_stateGS :: heap_stateGS Σ;
    }.

(* Definition heapΣ : gFunctors := *)
(*   #[mupdΣ; *)
(*     histGS.histΣ (state * thread_pool heap_lang * list (observation)); *)
(*     heap_stateΣ]. *)

(* Global Instance subG_heapΣ {Σ} : subG heapΣ Σ → heapGS Σ. *)
(* Proof. *)
(*   intros. econstructor. *)
(*   - apply subG_inv in H. destruct H. apply subG_inv in s. destruct s. apply subG_inv in s. destruct s. *)
(*     econstructor. *)
(*     + econstructor. *)
(*       * econstructor. *)
(*         { eapply subG_wsatΣ. auto. } *)
(*         all: exact inhabitant. *)
(*       * econstructor. *)
(*         { eapply subG_auth_rupdΣ. auto. } *)
(*         all: exact inhabitant. *)
(*     + econstructor. *)
(*       { eapply osatGS.subG_osatΣ. solve_inG. } *)
(*       all: exact inhabitant. *)
(*     + econstructor. *)
(*       { eapply othreadGS.subG_othreadΣ. solve_inG. } *)
(*       all: exact inhabitant. *)
(*     + econstructor. *)
(*       { eapply owitGS.subG_owitΣ. solve_inG. } *)
(*       all: exact inhabitant. *)
(*     + econstructor. *)
(*       { eapply mhistGS.subG_mhistΣ. solve_inG. } *)
(*       all: exact inhabitant. *)
(*   - econstructor. *)
(*     { eapply histGS.subG_histΣ. solve_inG. } *)
(*     all: exact inhabitant. *)
(*   - apply subG_heap_stateΣ. solve_inG. *)
(* Qed. *)

(* (** We don't want this to be an instance, which can break iMod. *) *)
(* Definition heapGS_temporalGS `{!heapGS Σ} : temporalGS heap_lang Σ := *)
(*   TemporalG heapGS_mupdGS heapGS_histGS. *)

Global Instance heapGS_lantanaGS `{!heapGS Σ} : lantanaGS heap_lang Σ := {
    lantana_temporalGS := heapGS_temporalGS;
    lantana_state_interp_class := heap_state_interp_class;
    fork_post i v := (True)%I;
  }.

(** [gen_inv_heap]: Similar to pointsto,
except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions here. *)
Section definitions.
  Context `{!heapGS Σ}.
  Definition inv_pointsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_pointsto_own l (Some v) (from_option I False).
  Definition inv_pointsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_pointsto l (from_option I False).
End definitions.

Global Instance: Params (@inv_pointsto_own) 5 := {}.
Global Instance: Params (@inv_pointsto) 4 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_pointsto_own l v I%stdpp%type)
                         (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

(* TODO: define tf representations for inv_heap *)

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : gmap thread_id expr.
Implicit Types σ : state.
Implicit Types Θ : thread_pool heap_lang.
Implicit Types l : loc.
Implicit Types e : expr.
Implicit Types v : val.

(** Thread-expression ownership and context agreement. *)
Global Instance thread_expr_timeless i C e : Timeless (thread_expr i C e).
Proof. apply _. Qed.

Lemma thread_expr_fill i C D e :
  thread_expr i C (fill D e) ⊣⊢ thread_expr i (D ++ C) e.
Proof. by rewrite /thread_expr fill_app. Qed.

Lemma thread_expr_ctx Θ i C D e σ κ e' σ' efs :
  Θ !! i = Some (fill D e) →
  prim_step i e σ (dom Θ) κ e' σ' efs →
  thread_map_interp (dom Θ) Θ -∗ thread_expr i C e -∗ ⌜C = D⌝.
Proof.
  iIntros (HT HS) "TI TE".
  iPoseProof (thread_expr_read with "TI TE") as "%HC".
  iPureIntro. eapply fill_ctx_step_inj; first exact HS. congruence.
Qed.

Lemma thread_expr_update Θ i C e e' :
  thread_map_interp (dom Θ) Θ -∗ thread_expr i C e ==∗
  thread_map_interp (dom (<[i:=fill C e']> Θ)) (<[i:=fill C e']> Θ) ∗
  thread_expr i C e'.
Proof.
  iIntros "TI TE".
  iPoseProof (thread_expr_read with "TI TE") as "%HT".
  iMod (thread_map_thread_update _ _ (fill C e') with "[$TI $TE]") as "[TI TE]".
  rewrite dom_insert_lookup_L; last eauto. by iFrame.
Qed.

(** Pure steps transport the client's single expression fragment. *)
Global Instance thread_expr_pure_exec_si C i :
  PureExecSI (λ i e, thread_expr i C e) i.
Proof.
  intros D e1 e2 σ Θ κ HD HT HS. iIntros "(TE& (HI& TI& PI)& _)".
  iPoseProof (thread_expr_ctx with "TI TE") as "%Heq"; [exact HT|exact HS|].
  subst D. iMod (thread_expr_update with "TI TE") as "[TI TE]".
  by iFrame.
Qed.

Lemma iter_modal_mono_modal M1 M2 P n :
  (∀ A B, (A -∗ B) -∗ (M1 A -∗ M1 B)) →
  (∀ A, M1 A -∗ M2 A) →
  (Nat.iter n M1 P -∗ Nat.iter n M2 P).
Proof.
  intros. revert P. induction n; intros; simpl; eauto.
  iIntros "H". iApply H0. iApply (H with "[] H"). iApply IHn.
Qed.

(** pure steps *)
Lemma lwp_pure_step n o s i E E' e1 e2 φ Φ {C} :
  PureExec φ n e1 e2 →
  φ →
  (thread_expr i C e1 ∗ Nat.iter n
    (λ P,
       |={E,E'}=> ∃ G, thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗
                 ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (thP_carriers i G -∗
                  ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                  ALC (£ o ={E',E}=∗ |={E}=>m P)))
    (thread_expr i C e2 -∗ lwpupd i E e2 (lWP e2 @ s; i; E {{ v, Φ v }})))
  ⊢ (lWP e1 @ s; i; E {{ Φ }}).
Proof.
  intros Hexec Hp. apply (lifting.lwp_pure_step n o s i E E' e1 e2 φ Φ
    (λ i e, thread_expr i C e)); auto; apply _.
Qed.

Lemma lwp_fork_step s i E E' e Φ {C} :
  (|={E,E'}=> thread_expr i C (Fork e) ∗
             ∃ G, thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗
             ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
             (∀ j, thread_expr i C #() -∗ thread_expr j [] e -∗
                   thP_carriers i G -∗
                   ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                   thP_carriers j ∅ -∗
                   ALC (|={E',E}=>
                        |={E}=>m (|={E}=>m Φ (LitV LitUnit)) ∗
                                (lwpupd j ⊤ e (lWP e @ s; j; ⊤ {{ lift_term j (λ _ _, True) }}))))) -∗
  lWP Fork e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "I".
  iMod "H" as "(TE& %&$&$& %&$& H)".
  iModIntro. iModIntro. iSplit; first eauto with base_step.
  iIntros (v2 σ2 efs Hstep).
  iDestruct "I" as "[(%HI& Ha& (Ih& It& Ip)) Ia]".
  iPoseProof (thread_expr_ctx with "It TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (thread_map_new_thread j e with "It") as "[It Tj]"; first eapply H0.
  iMod (thread_map_thread_update _ _ (fill K #()) with "[$It $TE]") as "[It TE]".
  replace (<[i:=fill K #()]> (<[j:=e]> Θ)) with (<[i:=fill K #()]> Θ ∪ {[j := e]}); cycle 1.
  { rewrite -insert_union_l. f_equal. rewrite insert_union_singleton_r; auto. apply not_elem_of_dom. auto. }
  iIntros "!> Tb Wcs Efs".
  iMod ("H" $! j with "TE Tj Tb Wcs [Efs]") as "H".
  { rewrite dom_singleton_L big_sepS_singleton. eauto. }
  iMod "H" as "HE".
  iMod (hG_history_auth_app with "Ha") as "Ha".
  rewrite big_sepM_singleton. iFrame.
  replace (dom (<[i:=fill K #()]> Θ ∪ {[j := e]})) with (dom Θ ∪ {[j]}); cycle 1.
  { rewrite dom_union_L dom_insert_lookup_L; eauto. rewrite dom_singleton_L. auto. }
  iFrame. iModIntro. iSplitR "HE"; cycle 1.
  { iMod "HE". iDestruct "HE" as "[>H HE]".
    iModIntro. iSplitL "H"; first by iFrame.
    iApply (lwpupd_mono with "HE").
    apply lwp_mono. intros v. by rewrite /lift_term /= right_id. }
  iPureIntro. destruct HI. split.
  - rewrite length_app H. simpl. lia.
  - rewrite last_app. simpl. auto.
Qed.

Lemma lwp_fork ℓ μ K P G R o s i E e g1 K1 {C} :
  K ⊆ K1 →
  (∀ j g2, l{{{ thread_expr j [] e ∗ thP_carriers j {[g2]} ∗ ([∗ set] g ∈ {[g2]}, crP_fuel g ℓ μ) ∗ crP_obls g2 ℓ K ∗ P }}}
             e @ s; j; ⊤ l{{{ v, RET v; lift_term j (λ _ _, True) v }}})%I
  ⊢
  l{{{ thread_expr i C (Fork e) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ crP_obls g1 ℓ K1 ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1) ∗ P }}}
    Fork e @ s; i; E
                     l{{{ RET #(); thread_expr i C #() ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ crP_obls g1 ℓ (K1 ∖ K)}}}.
Proof.
  iIntros (HK) "#Hfork !> %Φ (TE& (TG& GF& Rs)& Cg& OF& HP) HΦ".
  iApply lwp_fork_step. iModIntro. iFrame "TE TG GF Rs".
  iIntros (j) "TE TEj TG Ws TGj". iApply (ALC_credits _ _ o). iIntros "!> LC !>".
  iMod (carrier_alloc _ _ _ ℓ μ with "TGj") as "(%g2& _& TGj& Cg2& GF2)".
  iMod (obl_offload_set with "Cg Cg2 OF") as "(Cg& Cg2& _)". 1: set_solver. 1: done.
  rewrite union_empty_l_L union_empty_r_L. iModIntro. iSplitR "TEj HP TGj GF2 Cg2".
  - iApply ("HΦ" with "[$TE $LC $TG $Ws $Cg]").
  - iModIntro. iApply ("Hfork" with "[$TEj $TGj GF2 $Cg2 $HP]").
    { iApply big_sepS_singleton. iFrame. }
    auto.
Qed.

(** The fork rule with the child's carrier at an explicit depth, so that the
    child can be handed one unit one depth up for its specification. *)
Lemma lwp_fork_d ℓ d μ K P G R o s i E e g1 K1 {C} :
  K ⊆ K1 →
  (∀ j g2, l{{{ thread_expr j [] e ∗ thP_carriers j {[g2]} ∗ ([∗ set] g ∈ {[g2]}, crP_dfuel g ℓ d μ) ∗ crP_obls g2 ℓ K ∗ P }}}
             e @ s; j; ⊤ l{{{ v, RET v; lift_term j (λ _ _, True) v }}})%I
  ⊢
  l{{{ thread_expr i C (Fork e) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ crP_obls g1 ℓ K1 ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1) ∗ P }}}
    Fork e @ s; i; E
                     l{{{ RET #(); thread_expr i C #() ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ crP_obls g1 ℓ (K1 ∖ K)}}}.
Proof.
  iIntros (HK) "#Hfork !> %Φ (TE& (TG& GF& Rs)& Cg& OF& HP) HΦ".
  iApply lwp_fork_step. iModIntro. iFrame "TE TG GF Rs".
  iIntros (j) "TE TEj TG Ws TGj". iApply (ALC_credits _ _ o). iIntros "!> LC !>".
  iMod (carrier_alloc_d _ _ _ ℓ d μ with "TGj") as "(%g2& _& TGj& Cg2& GF2)".
  iMod (obl_offload_set with "Cg Cg2 OF") as "(Cg& Cg2& _)". 1: set_solver. 1: done.
  rewrite union_empty_l_L union_empty_r_L. iModIntro. iSplitR "TEj HP TGj GF2 Cg2".
  - iApply ("HΦ" with "[$TE $LC $TG $Ws $Cg]").
  - iModIntro. iApply ("Hfork" with "[$TEj $TGj GF2 $Cg2 $HP]").
    { iApply big_sepS_singleton. iFrame. }
    auto.
Qed.

(** Discharge at the actual final value, using credits from earlier steps. *)
Lemma thread_expr_terminate i E v g ℓ k N :
  ↑N ⊆ E →
  thread_expr i [] (of_val v) -∗ £ (2 : Ord.t) -∗
  thP_carriers i {[g]} -∗ crP_obls g ℓ {[k]} -∗
  ⟦finallyP N k 1 (exits v@i)⟧ₗ -∗ |={E}=>m
  thread_expr i [] (of_val v) ∗ thP_done i.
Proof.
  iIntros (Hmask) "TE LC TG Cg HF".
  iMod (tf_until_discharge with "HF") as "HF"; first set_solver.
  iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
  iApply (lc_sfmupd_add_later with "LC1"). iNext.
  iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
  iMod ("HF" with "[TE]") as "HF".
  { iNext. iEval (rewrite tf_atomic_logic). iFrame. }
  iPoseProof ("HF" with "[] Cg") as "HF".
  { iPureIntro. set_solver. }
  iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
  iApply (lc_sfmupd_add_later with "LC1"). iNext.
  iMod ("HF" $! _) as "HF". iMod "HF" as "(TE& Gg& #Odkl)".
  replace ({[k]} ∖ {[k]} : gset _) with (∅ : oids) by set_solver.
  iMod (carrier_delete with "TG Gg") as "TG"; first set_solver.
  replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
  iMod (thread_terminate with "TG") as "$". by iFrame.
Qed.

(** ChooseNat *)
Lemma lwp_choosenat_step o s i E E' Φ {C} :
  (|={E,E'}=> thread_expr i C ChooseNat ∗
                  ∃ G, thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗
                  ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                       (∀ (n : nat), thread_expr i C #n -∗ thP_carriers i G -∗
                                   ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                                   ALC (£ o ={E',E}=∗ (|={E}=>m Φ (#n))))) -∗
  lWP ChooseNat @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "I".
  iMod "H" as "(TE& %&$&$& %&$& H)".
  iModIntro. iModIntro. iSplit; first eauto with base_step.
  Unshelve. 2: exact 0.
  iIntros (v2 σ2 efs Hstep).
  iDestruct "I" as "[(%HI& Ha& (Ih& It& Ip)) Ia]".
  iPoseProof (thread_expr_ctx with "It TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (thread_expr_update _ _ _ _ #n0 with "It TE") as "[It TE]".
  iIntros "!> Tb Wcs". iPoseProof ("H" $! n0 with "TE Tb Wcs") as "H".
  iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
  iPoseProof (tlc_split with "LC") as "[LC LC2]".
  iMod ("H" with "LC2") as "H". iModIntro. iPoseProof ("H" with "LC") as "H".
  iMod "H" as "HE".
  iMod (hG_history_auth_app with "Ha") as "Ha".
  rewrite !map_union_empty. iFrame. iModIntro. iSplit; first done.
  iSplitR "HE"; cycle 1.
  { iMod "HE". iModIntro. iFrame. }
  iPureIntro. destruct HI. split.
  - rewrite length_app H. simpl. lia.
  - rewrite last_app. simpl. auto.
Qed.

Lemma lwp_choosenat G R o s i E {C} :
  l{{{ thread_expr i C ChooseNat ∗
       (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    ChooseNat @ s; i; E
  l{{{ (n : nat), RET LitV (LitInt n);
       thread_expr i C #n ∗
       (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) }}}.
Proof.
  iIntros (Φ) "(TE& TG& GF& Rs) HΦ".
  iApply (lwp_choosenat_step o with "[$TE $TG $GF $Rs HΦ]").
  iIntros "!> % TE TG RC !> LC !> !>".
  iApply ("HΦ" with "[$TE $TG $RC $LC]").
Qed.

Local Remark lwp_choosez_exists G R o s i E {C} :
  l{{{ thread_expr i C ChooseNat ∗
       (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    ChooseNat @ s; i; E
  l{{{ v, RET v; ∃ (n : nat), ⌜v = #n⌝ ∧
       (thread_expr i C (of_val v) ∗
        (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r))) }}}.
Proof.
  iIntros (Φ) "P HΦ".
  iPoseProof (lwp_choosenat with "P") as "H".
  iApply "H". iIntros (?) "H".
  iApply "HΦ". iExists n. iFrame. auto.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val] (and sealing). *)

Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_as_fractional l q v :
  AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
Proof. rewrite pointsto_unseal. apply _. Qed.
Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
Proof. rewrite pointsto_unseal. apply _. Qed.

Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 : 
  CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  rewrite pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? [=->]]. eauto.
Qed.

Lemma pointsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  rewrite pointsto_unseal.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$" gives %[_ [= ->]].
Qed.

Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
  CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
  (* higher cost than the Fractional instance, which kicks in for #qs *)
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
Qed.

Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. rewrite pointsto_unseal. apply pointsto_valid. Qed.
Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[? [= ?]]. done. Qed.
Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[_ [= ?]]. done. Qed.

Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_frac_ne. Qed.
Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rewrite pointsto_unseal. apply pointsto_ne. Qed.

Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. rewrite pointsto_unseal. apply pointsto_persist. Qed.
Lemma pointsto_unpersist l v : l ↦□ v ==∗ ∃ q, l ↦{#q} v.
Proof. rewrite pointsto_unseal. apply pointsto_unpersist. Qed.

Global Instance frame_pointsto p l v q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
Proof. apply: frame_fractional. Qed.

Global Instance inv_pointsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto_own. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.
Global Instance inv_pointsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.

Lemma make_inv_pointsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof.
  iIntros (??) "#HI Hl". rewrite pointsto_unseal.
  iApply make_inv_pointsto; done.
Qed.
Lemma inv_pointsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_pointsto_own_inv. Qed.

Lemma inv_pointsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
      inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv". rewrite pointsto_unseal.
  iMod (inv_pointsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl". rewrite pointsto_unseal.
  iMod (inv_pointsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ True).
Proof.
  iIntros (?) "#Hinv Hl". rewrite pointsto_unseal.
  iMod (inv_pointsto_acc with "Hinv Hl") as ([v|]) "(% & Hl & Hclose)"; [done| |done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs IH] forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_pointsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.pointsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n IH] forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton pointsto_unseal.
  iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Global Instance state_pred_interp_timesless π : Timeless (state_pred_interp π).
Proof. destruct π; simpl; apply _. Qed.

Lemma lwp_allocN_seq G R o s i E v n {C} :
  (0 < n)%Z →
  l{{{ thread_expr i C (AllocN #n (Val v)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l); thread_expr i C (Val (LitV (LitLoc l))) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
          [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "[TE (Tb& Gfs& Rs)] HP".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h ? σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs & Ht & Hk) Ia] !> !>". iSplit.
  { iPureIntro. split; first done. destruct n; auto with lia base_step. }
  iFrame "Tb Gfs Rs". iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hs")
    as "(Hs & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite length_replicate Z2Nat.id; auto with lia. }
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iFrame "Ha Hs Ht Hk". iModIntro. iSplitR; first done. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H. split; auto. lia. }
  iModIntro. iApply "HP". iFrame.
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.

Lemma lwp_alloc G R o s i E v {C} :
  l{{{ thread_expr i C (Alloc (Val v)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    Alloc (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l); thread_expr i C (Val (LitV (LitLoc l))) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
          l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "P HΦ".
  iApply (lwp_allocN_seq with "P"); [auto with lia..|].
  iIntros (l) "/= (TE& (?&?&?)&?&?)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.

Lemma lwp_free G R o s i E l v {C} :
  l{{{ thread_expr i C (Free #l) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v }}}
    Free (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET LitV LitUnit; thread_expr i C (#()) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) }}}.
Proof.
  iIntros (Φ) "[TE ((Tb& Gfs& Rs)& Hl)] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_load G R o s i E l dq v {C} :
  l{{{ thread_expr i C (Load #l) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦{dq} v }}}
    Load (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET v; thread_expr i C (Val v) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_store G R o s i E l v' v {C} :
  l{{{ thread_expr i C (Store #l (Val v)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET LitV LitUnit; thread_expr i C (#()) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_xchg G R o s i E l v' v {C} :
  l{{{ thread_expr i C (Xchg #l (Val v)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET v'; thread_expr i C (Val v') ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_fail G R o s i E l dq v' v1 v2 {C} :
  v' ≠ v1 → vals_compare_safe v' v1 →
  l{{{ thread_expr i C (CmpXchg #l (Val v1) (Val v2)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦{dq} v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool false); thread_expr i C (Val (PairV v' (LitV (LitBool false)))) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rewrite bool_decide_false //.
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H2. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_suc G R o s i E l v1 v2 v' {C} :
  v' = v1 → vals_compare_safe v' v1 →
  l{{{ thread_expr i C (CmpXchg #l (Val v1) (Val v2)) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool true); thread_expr i C (Val (PairV v' (LitV (LitBool true)))) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_faa G R o s i E l (i1 i2 : Z) {C} :
  l{{{ thread_expr i C (FAA #l #i2) ∗ (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ LitV (LitInt i1) }}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  l{{{ RET LitV (LitInt i1); thread_expr i C (#i1) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_new_proph G R o s i E {C} :
  l{{{ thread_expr i C (NewProph) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)}}}
    NewProph @ s; i; E
  l{{{ pvs p, RET (LitV (LitProphecy p)); thread_expr i C (Val (LitV (LitProphecy p))) ∗ (£ o ∗ thP_carriers i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ proph p pvs }}}.
Proof.
  iIntros (Φ) "[TE (Tb& Gfs& Rs)] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K h n σ1 Θ κ κs HK HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia] !> !>".
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rename select proph_id into p.
  iMod (proph_map_new_proph p with "Hk") as "[Hk Hp]"; first done.
  rewrite !map_union_empty.
  iMod (hG_history_auth_app with "Ha") as "Ha".
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame. iSplitR.
  { iPureIntro. destruct Hw. rewrite length_app last_app. simpl. rewrite H0. split; auto. lia. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a base step for [Resolve e _ _] not to be (base) stuck. *)

Lemma resolve_reducible i e σ D (p : proph_id) v :
  Atomic StronglyAtomic e → reducible i e σ D →
  reducible i (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ D.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃ w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A i σ D e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor; eauto. by apply prim_step_to_val_is_base_step.
Qed.

Lemma step_resolve i D e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step i (Resolve e (Val vp) (Val vt)) σ1 D κ e2 σ2 efs →
  base_step i (Resolve e (Val vp) (Val vt)) σ1 D κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_base_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A i σ1 D _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_base_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_base_step.
Qed.

(** FIXME: ectxi does not allow empty context, which seems necessary to compose with ResolveLCtx.
           Can we prove this without changing this constraint? *)
(* Lemma lwp_resolve s i E e Φ (p : proph_id) v (pvs : list (val * val)) : *)
(*   Atomic StronglyAtomic e → *)
(*   to_val e = None → *)
(*   proph p pvs -∗ *)
(*   (* (lwp_fix s i E e (λ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r)) -∗ *) *)
(*   lWP e @ s; i; E {{ Φ }} -∗ *)
(*   lWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   (* TODO we should try to use a generic lifting lemma (and avoid [lwp_unfold]) *) *)
(* (*      here, since this breaks the lWP abstraction. *) *)
(*   iIntros (A He0) "Hp lWPe". assert (He : to_val (fill_item K e) = None). *)
(*   { destruct (to_val (fill_item K e)) eqn:CASE; auto. assert (is_Some (to_val (fill_item K e))) by eauto. *)
(*     apply fill_item_val in H. rewrite He0 in H. done. } *)
(*   rewrite !lwp_unfold /lwp_pre /= He0. *)
(*   replace (Resolve (fill_item K e) #p v) with (fill_item (ResolveLCtx K #p v) e); cycle 1. *)
(*   { done. } *)
(*   iPoseProof (lwpupd_ctx with "lWPe") as "lWPe". iMod "lWPe". *)
(*   iModIntro. *)
(*   iIntros (K' h n σ1 Θ κ κs HK' HT) "[(%Hw& Ha& Hs& Ht& Hk) Ia]". *)
(*   destruct κ as [|[p' [w' v']] κ' _] using rev_ind. *)
(*   - iMod ("lWPe" $! (λ e', K' (fill_item (ResolveLCtx K #p v) e')) with "[] [] [$Ha $Hs $Ht $Hk $Ia]") as "lWPe". *)
(*     { iPureIntro. simpl. eapply language_ctx_compose; eauto. *)
(*       replace (λ e', Resolve (fill_item K e') #p v) with (fill_item (ResolveLCtx K #p v)); cycle 1. *)
(*       { done. } *)
(*       apply _. } *)
(*     { iPureIntro. simpl in *. apply HT. } *)
(*     { eauto. } *)
(*     iModIntro. iDestruct "lWPe" as "(%Hs& lWPe)". iSplit. *)
(*     { iPureIntro. destruct s; last auto. apply reducible_fill. auto. } *)
(*     iIntros (e2 σ2 efs step). exfalso. simpl in step. apply step_resolve in step; cycle 1. *)
(*     { unfold Atomic. simpl. intros. inv H. simpl in *. eapply base_ctx_step_val. eapply H2. *)
(*     last done. *)
(*     inv_base_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end. *)
(*   - iSpecialize ("lWPe" with "T"). *)
(*     rewrite -assoc. *)
(*     iMod ("lWPe" $! Θ σ1 _ _ with "[$Ht $Hσ $Hκ]") as "H". *)
(*     iModIntro. iMod "H" as "(%Hs& lWPe)". *)
(*     iModIntro. iSplit. *)
(*     { iPureIntro. destruct s; [ by apply resolve_reducible | done]. } *)
(*     iIntros (e2 σ2 efs step). apply step_resolve in step; last done. *)
(*     inv_base_step; simplify_list_eq. *)
(*     iMod ("lWPe" $! (Val w') σ2 efs with "[%]") as ">lWPe". *)
(*     { by eexists [] _ _. } *)
(*     iMod "lWPe" as ">(($& $& Hκ)& lWPe& Efs)". *)
(*     iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]". *)
(*     iModIntro. iFrame. *)
(*     rewrite !lwp_unfold /lwp_pre /=. *)
(*     iApply ("lWPe" with "[] HPost"). eauto. *)
(* Qed. *)

End lifting.
