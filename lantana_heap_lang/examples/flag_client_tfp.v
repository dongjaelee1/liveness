From iris.proofmode Require Import proofmode.
From lantana.program_logic Require Import temporal_prop.
From lantana.heap_lang Require Import notation proofmode.
From lantana.heap_lang.examples Require Import flag flag_client.
From iris.prelude Require Import options.

(** [flag_client_adequacy] again, through the adequacy theorem for semantic temporal
    formulas: the formula of [flag_client] is translated into the semantic connectives with
    [tf_native], and the proof of [flag_client_pre] is reused unchanged. *)
Section adequacy.

  Let i : thread_id := 1%positive.
  Let j : thread_id := 2%positive.
  Let l : loc := X_loc.
  Let Θ0 : thread_pool heap_lang := {[i := writer #(); j := reader #()]}.
  Let σ0 : gmap loc (option val) := {[l := Some #0]}.

  Let Φ : tp :=
        (is_flag_tp l ∧
         tp_until (l ↦ #0) (l ↦ #1) ∧
         tp_finally (exits #()@i) ∧
         tp_finally (exits #1@j))%P.

  Let Φ' : tp :=
        (∃ (g1 g2 : ocid) (k kl1 kl2 : oid),
            ⌜ k ≠ kl1 ⌝ ∧ is_flag_tp' l ∧
            tp_until (l ↦ #0) (l ↦ #1) ∧
            tp_finally (exits #()@i) ∧
            tp_finally (exits #1@j) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    Local Opaque is_flag_tp' is_flag_tp.
    simpl. unfold_trProp. intros. destruct τ. destruct H as (?&?&?&?&?&?&?&?).
    split. 1: apply is_flag_tp_impl; auto.
    firstorder.
    Local Transparent is_flag_tp' is_flag_tp.
  Qed.

  Let N := nroot.@ "flag".
  Let Np := N.@ "pointsto".
  Let Nl := nroot.@ "writer_return".

  Let Φ_tf `{!heapGS Σ} : _ → _ → tf Σ :=
        λ μ1 μ2,
          (∃ g1 g2 k kl1 kl2,
              ⌜ k ≠ kl1 ⌝ ∗ is_flag_tf l k 0 ∗
              untilP Np k (1/2) (l ↦ #0) (l ↦ #1) ∗
              finallyP Nl kl1 1 (exits #()@i) ∗
              finallyP Nl kl2 1 (exits #1@j) ∗
              ⟨thP_carriers i {[g1]} ∗ crP_obls g1 0 {[k; kl1]} ∗
               thP_carriers j {[g2]} ∗ crP_obls g2 1 ({[kl2]}) ∗
               crP_fuel g1 0 μ1 ∗ crP_fuel g2 1 μ2⟩)%F.

  (** The skeleton of the semantic formula is computed by [tfp_skel]. *)
  Lemma tfp_skel_Φ `{!heapGS Σ} m1 m2 :
    tfp_skel (tf_native (Φ_tf m1 m2)) = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post; j := fork_post]}.

  Theorem flag_client_adequacy_tfp :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    apply Φ_impl.
    eapply (lwp_adequacy_tfp Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] Φ').
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { iDestruct "PI" as "[PI _]". by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (flag_client_pre (heapGS0:=HHeapGS) Θ0 i j with "[Tis] [Ptrs] [TGs]") as "H".
    { subst i j. lia. }
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { subst σ0. rewrite big_sepM_singleton.
      by rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def. }
    { iFrame. }
    iDestruct "H" as (m1 m2) "(HP& H)".
    iModIntro. iExists (tf_native (Φ_tf m1 m2)). rewrite !tf_native_logic. iFrame "HP". iSplit.
    { iPureIntro. by rewrite tf_native_skel. }
    iFrame.
  Qed.

End adequacy.
