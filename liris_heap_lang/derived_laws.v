(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array]. *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From liris.heap_lang Require Export primitive_laws.
From liris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [array] connective is a version of [pointsto] that works
with lists of values. *)

Definition array `{!heapGS Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

Notation "l ↦∗ dq vs" := (array l dq vs)
  (at level 20, dq custom dfrac  at level 1, format "l  ↦∗ dq  vs") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{#q} vs) (λ q, l ↦∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l dq : l ↦∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦∗{dq} [v] ⊣⊢ l ↦{dq} v.
Proof. by rewrite /array /= right_id Loc.add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦∗{dq} (vs ++ ws) ⊣⊢ l ↦∗{dq} vs ∗ (l +ₗ length vs) ↦∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite Loc.add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦∗{dq} (v :: vs) ⊣⊢ l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons Loc.add_0.
  setoid_rewrite Loc.add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
  Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) ↦{dq} v ∗ ∀ v', (l +ₗ off) ↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite - [X in (l ↦∗{_} X)%I] (take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite length_take min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert_eq. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I] (take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert_ge; last by lia. iFrame.
  iApply array_cons. rewrite length_take min_l; last by lia. iFrame.
  rewrite drop_insert_lt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma pointsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{dq} v) -∗
  l ↦∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n' IH] forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc. iApply "IH". done.
Qed.

Lemma lwp_allocN G R o s q i E v n :
  (0 < n)%Z →
  l{{{ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
       ([∗ map] r↦v ∈ R, gl r v) }}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l);
         (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗
         ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗
         l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "T HΦ". iApply (lwp_allocN_seq with "T"); [auto.. | ].
  iIntros (l) "[T Hlm]". iApply "HΦ". iFrame "T".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply pointsto_seq_array.
Qed.

Lemma lwp_allocN_vec G R o s q i E v n :
  (0 < n)%Z →
  l{{{ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
       ([∗ map] r↦v ∈ R, gl r v) }}}
    AllocN #n v @ s; i; E
  l{{{ l, RET #l;
         (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗
         ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗
         l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "T HΦ". iApply (lwp_allocN with "T") ; [ lia | ].
  iIntros (l) "[T [Hl Hm]]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

(** * Rules for accessing array elements *)
Lemma lwp_load_offset G R o s q i E l dq off vs v :
  vs !! off = Some v →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗{dq} vs }}}
    ! #(l +ₗ off) @ s; i; E
  l{{{ RET v; (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_load with "[$T $Hl1]"). iIntros "[T Hl1]". iApply "HΦ". iFrame.
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_load_offset_vec G R o s q i E l dq sz (off : fin sz) (vs : vec val sz) :
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗{dq} vs }}}
    ! #(l +ₗ off) @ s; i; E
  l{{{ RET vs !!! off; (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗{dq} vs }}}.
Proof. apply lwp_load_offset. by apply vlookup_lookup. Qed.

Lemma lwp_store_offset G R o s q i E l off (vs : list val) (v : val) :
  is_Some (vs !! off) →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    #(l +ₗ off) <- v @ s; i; E
  l{{{ RET #(); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ (l ↦∗ (<[off:=v]> vs)) }}}.
Proof.
  iIntros ([w Hlookup] Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_store with "[$T $Hl1]"). iIntros "[T Hl1]".
  iApply "HΦ". iFrame "T". iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_store_offset_vec G R o s q i E l sz (off : fin sz) (vs : vec val sz) v :
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    #(l +ₗ off) <- v @ s; i; E
  l{{{ RET #(); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply lwp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

Lemma lwp_xchg_offset G R o s q i E l off (vs : list val) (v v' : val) :
  vs !! off = Some v →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    Xchg #(l +ₗ off) v' @ s; i; E
  l{{{ RET v; (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ <[off:=v']> vs }}}.
Proof.
  iIntros (Hlookup Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_xchg with "[$T $Hl1]"). iIntros "[T Hl1]".
  iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_xchg_offset_vec G R o s q i E l sz (off : fin sz) (vs : vec val sz) v :
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    Xchg #(l +ₗ off) v @ s; i; E
  l{{{ RET (vs !!! off); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply lwp_xchg_offset.
  by apply vlookup_lookup.
Qed.

Lemma lwp_cmpxchg_suc_offset G R o s q i E l off vs (v' v1 v2 : val) :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (v', #true); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (Hlookup ?? Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_cmpxchg_suc with "[$T $Hl1]"); [done..|].
  iIntros "[T Hl1]". iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_cmpxchg_suc_offset_vec G R o s q i E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (vs !!! off, #true); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ vinsert off v2 vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert.
  apply lwp_cmpxchg_suc_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma lwp_cmpxchg_fail_offset G R o s q i E l dq off vs (v0 v1 v2 : val) :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (v0, #false); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_cmpxchg_fail with "[$T $Hl1]"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "[T Hl1]". iApply "HΦ". iFrame "T". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_cmpxchg_fail_offset_vec G R o s q i E l dq sz (off : fin sz) (vs : vec val sz) (v1 v2 : val) :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (vs !!! off, #false); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗{dq} vs }}}.
Proof.
  intros. apply lwp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma lwp_faa_offset G R o s q i E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
       ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    FAA #(l +ₗ off) #i2 @ s; i; E
  l{{{ RET LitV (LitInt i1); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (Hlookup Φ) "[T Hl] HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_faa with "[$T $Hl1]").
  iIntros "[T Hl1]". iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_faa_offset_vec G R o s q i E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ l ↦∗ vs }}}
    FAA #(l +ₗ off) #i2 @ s; i; E
  l{{{ RET LitV (LitInt i1); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply lwp_faa_offset.
  by apply vlookup_lookup.
Qed.

(** Derived prophecy laws *)

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma lwp_resolve_proph G R o s q i E (p : proph_id) (pvs : list (val * val)) v :
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; i; E
  l{{{ pvs', RET (LitV LitUnit); (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "[[Tx T] Hp] HΦ". iApply (lwp_resolve with "Hp Tx"); first done.
  iIntros "Tx". iApply lifting.lwp_pure_step; first done. simpl.
  iFrame "Tx". iIntros "!>". iDestruct "T" as "($& $& $)".
  iIntros "Tx TG Rs". iExists o. iIntros "_ !> LC !>".
  iApply lwp_value. iIntros (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma lwp_resolve_cmpxchg_suc G R o s q i E l (p : proph_id) (pvs : list (val * val)) (v1 v2 v : val) :
  vals_compare_safe v1 v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; i; E
  l{{{ RET (v1, #true) ; (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[[Tx T] [Hp >Hl]] HΦ".
  iApply (lwp_resolve with "Hp Tx"); first done. iIntros "Tx".
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (lwp_cmpxchg_suc with "[$Tx $T $Hl]"); [done..|]. iIntros "[T Hl]".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma lwp_resolve_cmpxchg_fail G R o s q i E l (p : proph_id) (pvs : list (val * val)) dq (v' v1 v2 v : val) :
  v' ≠ v1 → vals_compare_safe v' v1 →
  l{{{ (thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] g↦v ∈ G, gl_fuel g Ord.one) ∗
        ([∗ map] r↦v ∈ R, gl r v)) ∗ proph p pvs ∗ ▷ l ↦{dq} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; i; E
  l{{{ RET (v', #false) ; (£ o ∗ thread_exec i q ∗ th_obls i G 1 ∗ ([∗ map] r↦v ∈ R, wit_credit r v Ord.one ∨ gl_done r v)) ∗ ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[[Tx T] [Hp >Hl]] HΦ".
  iApply (lwp_resolve with "Hp Tx"); first done. iIntros "Tx".
  iApply (lwp_cmpxchg_fail with "[$Tx $T $Hl]"); [done..|]. iIntros "[T Hl]".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

End lifting.

Global Typeclasses Opaque array.
