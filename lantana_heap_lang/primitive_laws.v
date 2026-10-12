From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Export gen_heap proph_map.
From lantana.base_logic Require Export thread_map gen_inv_heap.
From lantana.program_logic Require Export atomic.
From lantana.trace Require Export triprop adequacy_step guarantee_infer adequacy_temporal.
From lantana.program_logic Require Import ectx_lifting.
From lantana.heap_lang Require Export class_instances.
From lantana.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.
From lantana.algebra Require Export ordinal_wfocm.

(** The heap_lang instance of the Lantana program logic: the ghost state ([heapGS]), the
    points-to and thread-expression assertions, and the primitive lWP laws, proved from the
    lifting lemmas. Adapted from Iris's [iris.heap_lang.primitive_laws]. *)

(** * Ghost state and assertions *)
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

(** The [gen_heap] points-to of [Some v], sealed to keep it apart from [gen_heap]'s. *)
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

(** Exact ownership of a thread's expression in its caller context. *)
Definition thread_expr `{heap_stateGS Σ}
    (i : thread_id) (C : list ectx_item) (e : expr) : iProp Σ :=
  thread i true (fill C e) 1.

(** Thread [i]'s whole expression is the value [v] (empty context). *)
Notation "'exits' v @ i" := (thread_expr i [] (of_val v))%I
  (at level 20, v, i at level 1, format "exits  v @ i") : bi_scope.
Notation "l ↦ dq v" := (tr_state (pointsto_sat l dq v))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : tr_scope.
Notation "'exits' v @ i" := (tr_state (thread_expr_sat i [] (of_val v)))
  (at level 20, v, i at level 1, format "exits  v @ i") : tr_scope.

Lemma exits_finally_iff (τ : trace heap_lang) i v :
  tr_eventually (exits v@i)%R τ ↔
  ∃ n, τ.1 ≤ n ∧ (τ.2 n).1.1.1 !! i = Some (of_val v).
Proof.
  destruct τ as [m τf].
  change ((∃ n, m ≤ n ∧
    (let '((Θ, σ), _, _) := τf n in thread_expr_sat i [] (of_val v) σ Θ) ∧
    (∀ l, m ≤ l < n → True)) ↔
    ∃ n, m ≤ n ∧ (τf n).1.1.1 !! i = Some (of_val v)).
  split.
  - intros (n & Hn & H & _). exists n. split; first done.
    destruct (τf n) as [[[Θ σ] j] κ]. exact H.
  - intros (n & Hn & H). exists n. split; first done.
    split; last done. destruct (τf n) as [[[Θ σ] j] κ]. exact H.
Qed.

(** * State interpretation *)
Definition state_interp `{!heap_stateGS Σ}
    (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  (gen_heap_interp σ.(heap) ∗
   thread_map_interp (dom Θ) Θ ∗
   proph_map_interp κs σ.(used_proph_id))%I.

Definition state_interp_aux `{!heap_stateGS Σ}
    (σ : state) (Θ : thread_pool heap_lang) (κs : list observation) : iProp Σ :=
  True%I.

Lemma thread_expr_read `{!heap_stateGS Σ} :
  ∀ (Θ : thread_pool heap_lang) i C e,
  thread_map_interp (dom Θ) Θ -∗ thread_expr i C e -∗ ⌜Θ !! i = Some (fill C e)⌝.
Proof.
  iIntros (????) "TI Ti".
  iPoseProof (thread_map_thread_read with "TI Ti") as "%". eauto.
Qed.

(** The facts about the state that a points-to and a thread expression determine
    (temporal_laws.v makes them [StateFact]s). *)
Lemma pointsto_state_interp `{!heap_stateGS Σ} σ Θ κs l dq v :
  state_interp σ Θ κs ∗ pointsto l dq v ⊢ ⌜pointsto_sat l dq v σ Θ⌝.
Proof.
  iIntros "[(HI& _& _) Hl]". rewrite pointsto_unseal /pointsto_def.
  iPoseProof (gen_heap_valid with "HI Hl") as "%". eauto.
Qed.
Lemma thread_expr_state_interp `{!heap_stateGS Σ} σ Θ κs i C e :
  state_interp σ Θ κs ∗ thread_expr i C e ⊢ ⌜thread_expr_sat i C e σ Θ⌝.
Proof. iIntros "[(_& TI& _) Ti]". iPoseProof (thread_expr_read with "TI Ti") as "%". eauto. Qed.

(** Not an instance: that can break [iMod]. *)
Definition heap_state_interp_class `{!heap_stateGS Σ} : state_interp_class heap_lang Σ :=
  Build_state_interp_class _ _ _ state_interp state_interp_aux.

(** * The program-logic instance *)
Class heapGS Σ :=
  HeapGS {
      heapGS_temporalGS : temporalGS heap_lang Σ;
      #[global] heapGS_heap_stateGS :: heap_stateGS Σ;
    }.

Global Instance heapGS_lantanaGS `{!heapGS Σ} : lantanaGS heap_lang Σ := {
    lantana_temporalGS := heapGS_temporalGS;
    lantana_state_interp_class := heap_state_interp_class;
    fork_post i v := (True)%I;
  }.

(** * The invariant heap *)
(** Definitions rather than notations, so that setoid rewriting in [I] works. *)
Section inv_heap.
  Context `{!heapGS Σ}.
  Definition inv_pointsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_pointsto_own l (Some v) (from_option I False).
  Definition inv_pointsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_pointsto l (from_option I False).
End inv_heap.

Global Instance: Params (@inv_pointsto_own) 5 := {}.
Global Instance: Params (@inv_pointsto) 4 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_pointsto_own l v I%stdpp%type)
                         (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

(** * Lifting lemmas *)
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

(** ** Thread expressions: ownership and context agreement *)
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

(** Pure steps of [e] in the context [C] update [thread_expr i C e]. *)
Global Instance thread_expr_pure_exec_si C i :
  PureExecSI (λ i e, thread_expr i C e) i.
Proof.
  intros D e1 e2 σ Θ κ HD HT HS. iIntros "(TE& (HI& TI& PI)& _)".
  iPoseProof (thread_expr_ctx with "TI TE") as "%Heq"; [exact HT|exact HS|].
  subst D. iMod (thread_expr_update with "TI TE") as "[TI TE]".
  by iFrame.
Qed.

(** ** Pure steps *)
Lemma lwp_pure_step n o s i E E' e1 e2 φ Φ {C} :
  PureExec φ n e1 e2 →
  φ →
  (thread_expr i C e1 ∗ Nat.iter n
    (λ P,
       |={E,E'}=> ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
                 ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (thP_kids i G -∗
                  ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                  ALC (£ o ={E',E}=∗ |={E}=>m P)))
    (thread_expr i C e2 -∗ (|={E}=>m (lWP e2 @ s; i; E {{ v, Φ v }}))))
  ⊢ (lWP e1 @ s; i; E {{ Φ }}).
Proof.
  intros Hexec Hp. apply (lifting.lwp_pure_step n o s i E E' e1 e2 φ Φ
    (λ i e, thread_expr i C e)); auto; apply _.
Qed.

(** ** Fork *)
Lemma lwp_fork_step s i E E' e Φ {C} :
  (|={E,E'}=> thread_expr i C (Fork e) ∗
             ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
             ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
             (∀ j, thread_expr i C #() -∗ thread_expr j [] e -∗
                   thP_kids i G -∗
                   ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                   thP_kids j ∅ -∗
                   ALC (|={E',E}=>
                        |={E}=>m (|={E}=>m Φ (LitV LitUnit)) ∗
                                (lWP e @ s; j; ⊤ {{ lift_term j (λ _ _, True) }})))) -∗
  lWP Fork e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "I".
  iMod "H" as "(TE& %&$&$& %&$& H)".
  iModIntro. iSplit; first eauto with base_step.
  iIntros (v2 σ2 efs Hstep).
  iDestruct "I" as "[(Ih& It& Ip) Ia]".
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
  rewrite big_sepM_singleton. iFrame.
  rewrite dom_union_L dom_insert_lookup_L; last eauto. rewrite dom_singleton_L. by iFrame.
Qed.

(** The forked thread [j] takes the children [K] of the forking thread, each paying one
    unit of fuel (at any layer) to change owner. *)
Lemma lwp_fork K P G R o s i E e {C} :
  K ⊆ G →
  (∀ j, l{{{ thread_expr j [] e ∗ thP_kids j K ∗ P }}}
          e @ s; j; ⊤ l{{{ v, RET v; lift_term j (λ _ _, True) v }}})%I
  ⊢
  l{{{ thread_expr i C (Fork e) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ ([∗ set] k ∈ K, ∃ ℓ, oblP_fuel k ℓ 1) ∗ P }}}
    Fork e @ s; i; E
  l{{{ RET #(); thread_expr i C #() ∗ (£ o ∗ thP_kids i (G ∖ K) ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) }}}.
Proof.
  iIntros (HK) "#Hfork !> %Φ (TE& (TG& GF& Rs)& OF& HP) HΦ".
  iApply lwp_fork_step. iModIntro. iFrame "TE TG GF Rs".
  iIntros (j) "TE TEj TG Ws TGj". iApply (ALC_credits _ _ o). iIntros "!> LC !>".
  iMod (obl_move_thread_set _ (PThread i) j G ∅ K with "TG TGj OF") as "(_& TG& TGj)"; first done.
  rewrite union_empty_r_L. iModIntro. iSplitR "TEj HP TGj".
  - iApply ("HΦ" with "[$TE $LC $TG $Ws]").
  - iApply ("Hfork" with "[$TEj $TGj $HP]"). auto.
Qed.

(** ** ChooseNat *)
Lemma lwp_choosenat_step o s i E E' Φ {C} :
  (|={E,E'}=> thread_expr i C ChooseNat ∗
                  ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
                  ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                       (∀ (n : nat), thread_expr i C #n -∗ thP_kids i G -∗
                                   ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                                   ALC (£ o ={E',E}=∗ (|={E}=>m Φ (#n))))) -∗
  lWP ChooseNat @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "I".
  iMod "H" as "(TE& %&$&$& %&$& H)".
  iModIntro. iSplit; first eauto with base_step.
  Unshelve. 2: exact 0.
  iIntros (v2 σ2 efs Hstep).
  iDestruct "I" as "[(Ih& It& Ip) Ia]".
  iPoseProof (thread_expr_ctx with "It TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (thread_expr_update _ _ _ _ #n with "It TE") as "[It TE]".
  iIntros "!> Tb Wcs". iPoseProof ("H" $! n with "TE Tb Wcs") as "H".
  iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
  iPoseProof (tlc_split with "LC") as "[LC LC2]".
  iMod ("H" with "LC2") as "H". iModIntro. iPoseProof ("H" with "LC") as "H".
  iMod "H" as "HE".
  rewrite !map_union_empty. iFrame. by iModIntro.
Qed.

Lemma lwp_choosenat G R o s i E {C} :
  l{{{ thread_expr i C ChooseNat ∗
       (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗ ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    ChooseNat @ s; i; E
  l{{{ (n : nat), RET LitV (LitInt n);
       thread_expr i C #n ∗
       (£ o ∗ thP_kids i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) }}}.
Proof.
  iIntros (Φ) "(TE& TG& GF& Rs) HΦ".
  iApply (lwp_choosenat_step o with "[$TE $TG $GF $Rs HΦ]").
  iIntros "!> % TE TG RC !> LC !> !>".
  iApply ("HΦ" with "[$TE $TG $RC $LC]").
Qed.

(** ** Heap *)

(** The [gen_heap] and [gen_inv_heap] lemmas, for [option val] and the sealing. *)

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

(** The points-to of a freed location, which [lwp_free_freed] keeps. *)
Definition freed (l : loc) (q : Qp) : iProp Σ := gen_heap.pointsto l (DfracOwn q) (None : option val).

Lemma freed_split (l : loc) q1 q2 : freed l (q1 + q2) ⊣⊢ freed l q1 ∗ freed l q2.
Proof. rewrite /freed -gen_heap.pointsto_fractional. done. Qed.

Lemma freed_pointsto_false (l : loc) q dq v : freed l q -∗ l ↦{dq} v -∗ False.
Proof.
  rewrite pointsto_unseal /pointsto_def /freed.
  iIntros "H1 H2". by iDestruct (gen_heap.pointsto_agree with "H1 H2") as %?.
Qed.

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

(** The [allocN] rules with [array] are in derived_laws.v. *)
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

Lemma lwp_allocN_seq G R o s i E v n {C} :
  (0 < n)%Z →
  l{{{ thread_expr i C (AllocN #n (Val v)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l); thread_expr i C (Val (LitV (LitLoc l))) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
          [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "[TE (Tb& Gfs& Rs)] HP".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs & Ht & Hk) Ia] !>". iSplit.
  { iPureIntro. split; first done. destruct n; auto with lia base_step. }
  iFrame "Tb Gfs Rs". iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hs")
    as "(Hs & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite length_replicate Z2Nat.id; auto with lia. }
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iFrame "Hs Ht Hk". iModIntro. iSplitR; first done.
  iModIntro. iApply "HP". iFrame.
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.

Lemma lwp_alloc G R o s i E v {C} :
  l{{{ thread_expr i C (Alloc (Val v)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) }}}
    Alloc (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l); thread_expr i C (Val (LitV (LitLoc l))) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
          l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "P HΦ".
  iApply (lwp_allocN_seq with "P"); [auto with lia..|].
  iIntros (l) "/= (TE& (?&?&?)&?&?)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.

Lemma lwp_free G R o s i E l v {C} :
  l{{{ thread_expr i C (Free #l) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v }}}
    Free (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET LitV LitUnit; thread_expr i C (#()) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) }}}.
Proof.
  iIntros (Φ) "[TE ((Tb& Gfs& Rs)& Hl)] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

(** [lwp_free], keeping the points-to of the freed location. *)
Lemma lwp_free_freed G R o s i E (l : loc) v {C} :
  l{{{ thread_expr i C (Free #l) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v }}}
    Free (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET LitV LitUnit; thread_expr i C (#()) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ freed l 1 }}}.
Proof.
  iIntros (Φ) "[TE ((Tb& Gfs& Rs)& Hl)] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_load G R o s i E l dq v {C} :
  l{{{ thread_expr i C (Load #l) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦{dq} v }}}
    Load (Val $ LitV $ LitLoc l) @ s; i; E
  l{{{ RET v; thread_expr i C (Val v) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_store G R o s i E l v' v {C} :
  l{{{ thread_expr i C (Store #l (Val v)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET LitV LitUnit; thread_expr i C (#()) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_xchg G R o s i E l v' v {C} :
  l{{{ thread_expr i C (Xchg #l (Val v)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; i; E
  l{{{ RET v'; thread_expr i C (Val v') ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_fail G R o s i E l dq v' v1 v2 {C} :
  v' ≠ v1 → vals_compare_safe v' v1 →
  l{{{ thread_expr i C (CmpXchg #l (Val v1) (Val v2)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦{dq} v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool false); thread_expr i C (Val (PairV v' (LitV (LitBool false)))) ∗ (£ o ∗
       thP_kids i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rewrite bool_decide_false //.
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_cmpxchg_suc G R o s i E l v1 v2 v' {C} :
  v' = v1 → vals_compare_safe v' v1 →
  l{{{ thread_expr i C (CmpXchg #l (Val v1) (Val v2)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ v' }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; i; E
  l{{{ RET PairV v' (LitV $ LitBool true); thread_expr i C (Val (PairV v' (LitV (LitBool true)))) ∗ (£ o ∗
       thP_kids i G ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
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
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma lwp_faa G R o s i E l (i1 i2 : Z) {C} :
  l{{{ thread_expr i C (FAA #l #i2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦ LitV (LitInt i1) }}}
    FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; i; E
  l{{{ RET LitV (LitInt i1); thread_expr i C (#i1) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) "[TE [(Tb& Gfs& Rs) Hl]] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  rewrite pointsto_unseal. iDestruct (gen_heap_valid with "Hs Hl") as %?.
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2' σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  iMod (gen_heap_update with "Hs Hl") as "[$ Hl]".
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

(** ** Prophecies *)
Lemma lwp_new_proph G R o s i E {C} :
  l{{{ thread_expr i C (NewProph) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)}}}
    NewProph @ s; i; E
  l{{{ pvs p, RET (LitV (LitrProphecy p)); thread_expr i C (Val (LitV (LitrProphecy p))) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ proph p pvs }}}.
Proof.
  iIntros (Φ) "[TE (Tb& Gfs& Rs)] HΦ".
  iApply lwp_lift_atomic_base_step_no_fork. 1: eauto.
  iIntros (K σ1 Θ κ κs HK HT) "[(Hs& Ht& Hk) Ia] !>".
  iSplit; first by eauto with base_step.
  iFrame "Tb Gfs Rs".
  iIntros (v2 σ2 efs Hstep).
  iPoseProof (thread_expr_ctx with "Ht TE") as "%HC".
  { exact HT. } { by apply base_prim_step. }
  subst C. inv_base_step.
  rename select proph_id into p.
  iMod (proph_map_new_proph p with "Hk") as "[Hk Hp]"; first done.
  rewrite !map_union_empty.
  iMod (thread_expr_update with "Ht TE") as "[Ht TE]".
  iIntros "!> Tb Wcs". iExists o. iIntros "LC !>".
  iModIntro. iSplit; first done. iFrame.
  iModIntro. iApply "HΦ". iFrame.
Qed.

(* Strong atomicity: [e] must take a base step for [Resolve e _ _] not to be stuck. *)

Lemma resolve_reducible i e σ D (p : proph_id) v :
  Atomic StronglyAtomic e → reducible i e σ D →
  reducible i (Resolve e (Val (LitV (LitrProphecy p))) (Val v)) σ D.
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

(** FIXME: no [lwp_resolve] yet: it seems to need an empty context item ([ectxi_language]). *)

End lifting.
