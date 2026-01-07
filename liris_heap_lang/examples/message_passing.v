From iris.algebra Require Import lib.frac_auth numbers auth.
From iris.proofmode Require Import proofmode.
(** Fix step index to ordinals *)
From transfinite.stepindex Require Import ordinals.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export weakestpre.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import primitive_laws.
From liris.heap_lang Require Import tactics.
(* From liris.heap_lang Require Import proofmode. *)
From iris.prelude Require Import options.

(* From liris.heap_lang.lib Require Import par. *)

(* Local Instance ordI : indexT := ordI. *)

Definition writer : val :=
  λ: "l", "l" <- #1;;
          Exit #().

Definition reader : val := 
  rec: "reader" "l" :=
    let: "n" := !"l" in
    if: "n" = #1
    then Exit #()
    else "reader" "l".

Section mp_proof.
  Context `{SI : indexT} `{!heapGS Σ} (N : namespace).

  Definition mp_ξ : gl_witness := λ _, ω%ord.
  Definition mp_ηξ : gl_witness := λ v, gupd_η (Σ[mp_ξ] v).

  Definition mp_proto (k : gl_id) (v : ghost_lock_version) (l : loc) : iProp Σ :=
    gl_witfun k mp_ξ ∗ gl k v ∗ wit k v (mp_ηξ v) ∗
    gl_variant N k v (l ↦ #0) (l ↦ #1) (False).

  Definition mp (k : gl_id) (l : loc) : iProp Σ :=
    mp_proto k 0 l.

  (** The main proofs. *)
  Global Instance mp_proto_persistent k v l : Persistent (mp_proto k v l).
  Proof. apply _. Qed.
  Global Instance mp_persistent k l : Persistent (mp k l).
  Proof. apply _. Qed.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step; constructor; [solve_exec_safe | solve_exec_puredet].

  Lemma mp_writer_spec i l :
    l{{{ ∃ k, mp k l ∗
              thread_exec i 1 ∗ th_obls i (<[k:=0]>∅) 1 ∗
              gl_fuel k (Σ[mp_ξ] 0) }}}
      writer #l @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iApply lwp_sfgupd.
    iDestruct "HP" as "(%& (#Gwfk& #Gk& #Wkv& #GVkv)& Tx& G& Gfk)".
    rewrite /writer /=.
    iMod (gl_fuel_lt k 100 with "Gfk") as "[Gfk Gfk1]".
    { apply Ord.omega_upperbound. }
    (* Pure steps *)
    iApply (lwp_pure_step 1). 1: done.
    simpl. iModIntro. iFrame "Tx G". iSplitL "Gfk1".
    { iApply big_sepM_singleton. auto. }
    iExists ∅. iSplitR; first done.
    iIntros "Tx Tb _ !> !> _".
    iMod (gl_fuel_mon_split k 99 1 with "Gfk") as "[Gfk Gfk1]".
    { rewrite -Hessenberg.add_from_nat. reflexivity. }
    (* How to proceed? *)

    TODO

    lazymatch goal with
    | |- environments.envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
        first [ reshape_expr e ltac:(fun K e' => idtac)
              | fail 1 "wp_bind: cannot find" ]
    | _ => fail "wp_bind: not a 'wp'"
    end.
    lazymatch goal with
    | |- environments.envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
        first [ reshape_expr e ltac:(fun K e' => iApply lwp_bind)
              | fail 1 "wp_bind: cannot find" ]
    | _ => fail "wp_bind: not a 'wp'"
    end.
    iApply lwp_bind.
    { econstructor; simpl; eauto.
      - intros. inv H; simpl in *. econstructor; simpl; eauto.
        + rewrite /fill.

        eapply fill_prim_step.
        Unset Printing Notations.
        

        econstructor.

        econstructor; simpl; eauto.
        + Set Printing All.


    lazymatch goal with
    | |- environments.envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
        first [ reshape_expr e ltac:(fun K e' => unify e' (Store _ _))
              | fail 1 "wp_bind: cannot find" ]
    | _ => fail "wp_bind: not a 'wp'"
    end.


Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

    iApply lwp_bind.
    { econstructor; simpl; eauto.
      - intros. inv H; simpl in *. econstructor; simpl; eauto.
        + Set Printing All.

        apply Ectx_step'. fill_prim_step. econstructor; simpl; eauto.
        + rewrite fill_app.

    iApply (lwp_pure_step 1).
    { instantiate (2:=True).
      subst; intros ?; apply nsteps_once, pure_base_step_pure_step; constructor; simpl; eauto.
      - intros; subst; do 3 eexists. simpl. econstructor; eauto.

      [solve_exec_safe | solve_exec_puredet].

      Set Printing All. apply pure_beta.
      eapply pure_recc. solve_pure_exec.

      econstructor; eauto. econstructor. }
    {
      solve_pure_exec. eapply pure_recc. econstructor; simpl; eauto.
      - intros. eapply base_prim_reducible_no_obs. econstructor; simpl; eauto.
        

      Unset Printing Notations. eapply pure_exec_fill.

    1: done.

    iApply lwp_lift_base_step.
    iApply lwp_bind.

    iApply (lwp_store _ _ _ _ _ _ _ _ ∅ 0 with "[$Tx $Tb Gfk1]").

    iMod (gl_unlock with "Tb GVkv") as "[>(Tb& Glk& VP) ACC]".
    { set_solver. }
    { rewrite lookup_insert_eq. auto. }

    iApply lwp_sfgupd.
    iApply (lwp_store _ _ _ _ _ _ _ _ ∅ 0 with "[$VP $Tx $Tb Gfk1]").
    { rewrite !big_sepM_singleton. iFrame. by iApply big_sepM_empty. }
    iIntros "(_& Tx& Tb& _& ptl)".
    iPoseProof ("ACC" with "Tb Glk ptl") as "ACC". iSpecialize ("ACC" $! (⊤ ∖ ↑N)).
    iMod "ACC". iModIntro. iMod "ACC" as "(Tb& Gc& #Gd)". iModIntro.
    
    

    TODO
    
    iApply lwp_store.
gl_variant_acc_own:
  ∀ {SI : indexT} {Σ : gFunctors} {gupdGS0 : gupdGS Σ} (E : coPset) (i : positive) 
    (G : gmap gl_id ghost_lock_version) (q : Qp) (N : namespace) (k : gl_id) 
    (v : ghost_lock_version) (P Q R : iProp Σ),
    ↑N ⊆ E
    → G !! k = Some v
      → th_obls i G q -∗
        gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
        ▷ (th_obls i G q ∗ gl_locked k v ∗ P) ∗ (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True)

    TODO

  Lemma newcounter_mp_spec i Δ q :
    l{{{ thread_obls i Δ q }}} newcounter #() @ i l{{{ l, RET #l; thread_obls i Δ q ∗ mp l 0 }}}.
  Proof.
    iIntros (Φ) "T HΦ". rewrite /newcounter /=.
    iApply (lwp_pure_step with "[$T HΦ]"). 1: done.
    iIntros "T". iApply lwp_fupd.
    iApply (lwp_alloc with "T"). iIntros (l) "[T [Hl Hm]]".
    iMod (own_alloc (● (MaxNat O) ⋅ ◯ (MaxNat O))) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (inv_alloc N _ (mp_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0. by iFrame. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  TODO

  Lemma incr_mp_spec i Δ q l n :
    l{{{ thread_obls i Δ q ∗ mp l n }}} incr #l @ i l{{{ RET #(); thread_obls i Δ q ∗ mp l (S n) }}}.
  Proof.
    iIntros (Φ) "[T Hl] HΦ". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (γ) "[#? Hγf]".
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hγ Hl]".
    destruct (decide (c' = c)) as [->|].
    - iCombine "Hγ Hγf"
        gives %[?%max_nat_included _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
      { apply auth_update, (max_nat_local_update _ _ (MaxNat (S c))). simpl. auto. }
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. iApply "HΦ". iModIntro. iExists γ; repeat iSplit; eauto.
      iApply (own_mono with "Hγf").
      (* FIXME: FIXME(Coq #6294): needs new unification *)
      apply: auth_frag_mono. by apply max_nat_included, le_n_S.
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]). iModIntro.
      iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. iApply ("IH" with "[Hγf] [HΦ]"); last by auto.
      rewrite {3}/mp; eauto 10.
  Qed.

  Lemma read_mp_spec l j :
    {{{ mp l j }}} read #l {{{ i, RET #i; ⌜j ≤ i⌝ ∧ mp l i }}}.
  Proof.
    iIntros (ϕ) "Hc HΦ". iDestruct "Hc" as (γ) "[#Hinv Hγf]".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]".
    wp_load.
    iCombine "Hγ Hγf"
      gives %[?%max_nat_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
    { apply auth_update, (max_nat_local_update _ _ (MaxNat c)); auto. }
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"). rewrite /mp; eauto 10.
  Qed.
End mp_proof.
