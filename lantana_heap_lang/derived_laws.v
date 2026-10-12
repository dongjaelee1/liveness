From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From lantana.heap_lang Require Export primitive_laws.
From lantana.heap_lang Require Import notation.
From iris.prelude Require Import options.

(** The [array] connective ([pointsto] for a list of values) and the lWP rules for arrays,
    derived without the lifting lemmas. Adapted from Iris's [iris.heap_lang.derived_laws]. *)

Definition array `{!heapGS Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

Notation "l ↦∗ dq vs" := (array l dq vs)
  (at level 20, dq custom dfrac  at level 1, format "l  ↦∗ dq  vs") : bi_scope.

(** The fraction splits (via [AsFractional]); the list does not, as that would give
    overlapping instances. *)

Section array_laws.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types vs : list val.
Implicit Types v : val.
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
  iApply big_sepL_proper.
  2:{ iApply "IH". iApply (big_sepL_impl with "Hl").
      iIntros "!> %% %". rewrite Nat2Z.inj_succ -Z.add_1_l -Loc.add_assoc. iIntros "$". }
  intros. rewrite Nat2Z.inj_succ -Z.add_1_l -Loc.add_assoc. done.
Qed.

Lemma lwp_allocN G R o s i E v n {C} :
  (0 < n)%Z →
  l{{{ thread_expr i C (AllocN (Val $ LitV $ LitInt $ n) (Val v)) ∗ thP_kids i G ∗
       ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) }}}
    AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; i; E
  l{{{ l, RET LitV (LitLoc l); thread_expr i C (of_val (LitV (LitLoc l))%V) ∗ (£ o ∗ thP_kids i G ∗
         ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
         l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "T HΦ". iApply (lwp_allocN_seq with "T"); [auto.. | ].
  iIntros (l) "(TE& T& Hlm)". iApply "HΦ". iFrame "TE T".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply pointsto_seq_array.
Qed.

Lemma lwp_allocN_vec G R o s i E v n {C} :
  (0 < n)%Z →
  l{{{ thread_expr i C (AllocN #n v) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) }}}
    AllocN #n v @ s; i; E
  l{{{ l, RET #l; thread_expr i C (of_val (#l)%V) ∗ (£ o ∗ thP_kids i G ∗
         ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗
         l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "T HΦ". iApply (lwp_allocN with "T") ; [ lia | ].
  iIntros (l) "(TE& T& Hl& Hm)". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

(** * Rules for accessing array elements *)
Lemma lwp_load_offset G R o s i E l dq off vs v {C} :
  vs !! off = Some v →
  l{{{ thread_expr i C (! #(l +ₗ off)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗{dq} vs }}}
    ! #(l +ₗ off) @ s; i; E
  l{{{ RET v; thread_expr i C (of_val (v)%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_load with "[$TE $T $Hl1]"). iIntros "(TE& T& Hl1)". iApply "HΦ". iFrame.
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_load_offset_vec G R o s i E l dq sz (off : fin sz) (vs : vec val sz) {C} :
  l{{{ thread_expr i C (! #(l +ₗ off)) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗{dq} vs }}}
    ! #(l +ₗ off) @ s; i; E
  l{{{ RET vs !!! off; thread_expr i C (of_val (vs !!! off)%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗{dq} vs }}}.
Proof. apply lwp_load_offset. by apply vlookup_lookup. Qed.

Lemma lwp_store_offset G R o s i E l off (vs : list val) (v : val) {C} :
  is_Some (vs !! off) →
  l{{{ thread_expr i C (#(l +ₗ off) <- v) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    #(l +ₗ off) <- v @ s; i; E
  l{{{ RET #(); thread_expr i C (of_val (#())%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ (l ↦∗ (<[off:=v]> vs)) }}}.
Proof.
  iIntros ([w Hlookup] Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_store with "[$TE $T $Hl1]"). iIntros "(TE& T& Hl1)".
  iApply "HΦ". iFrame "TE T". iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_store_offset_vec G R o s i E l sz (off : fin sz) (vs : vec val sz) v {C} :
  l{{{ thread_expr i C (#(l +ₗ off) <- v) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    #(l +ₗ off) <- v @ s; i; E
  l{{{ RET #(); thread_expr i C (of_val (#())%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=v]> vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply lwp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

Lemma lwp_xchg_offset G R o s i E l off (vs : list val) (v v' : val) {C} :
  vs !! off = Some v →
  l{{{ thread_expr i C (Xchg #(l +ₗ off) v') ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    Xchg #(l +ₗ off) v' @ s; i; E
  l{{{ RET v; thread_expr i C (of_val (v)%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=v']> vs }}}.
Proof.
  iIntros (Hlookup Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_xchg with "[$TE $T $Hl1]"). iIntros "(TE& T& Hl1)".
  iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_xchg_offset_vec G R o s i E l sz (off : fin sz) (vs : vec val sz) v {C} :
  l{{{ thread_expr i C (Xchg #(l +ₗ off) v) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    Xchg #(l +ₗ off) v @ s; i; E
  l{{{ RET (vs !!! off); thread_expr i C (of_val ((vs !!! off))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=v]> vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply lwp_xchg_offset.
  by apply vlookup_lookup.
Qed.

Lemma lwp_cmpxchg_suc_offset G R o s i E l off vs (v' v1 v2 : val) {C} :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  l{{{ thread_expr i C (CmpXchg #(l +ₗ off) v1 v2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (v', #true); thread_expr i C (of_val ((v', #true))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (Hlookup ?? Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_cmpxchg_suc with "[$TE $T $Hl1]"); [done..|].
  iIntros "(TE& T& Hl1)". iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_cmpxchg_suc_offset_vec G R o s i E l sz (off : fin sz) (vs : vec val sz) v1 v2 {C} :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  l{{{ thread_expr i C (CmpXchg #(l +ₗ off) v1 v2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (vs !!! off, #true); thread_expr i C (of_val ((vs !!! off, #true))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=v2]> vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert.
  apply lwp_cmpxchg_suc_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma lwp_cmpxchg_fail_offset G R o s i E l dq off vs (v0 v1 v2 : val) {C} :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  l{{{ thread_expr i C (CmpXchg #(l +ₗ off) v1 v2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (v0, #false); thread_expr i C (of_val ((v0, #false))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_cmpxchg_fail with "[$TE $T $Hl1]"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "(TE& T& Hl1)". iApply "HΦ". iFrame "TE T". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_cmpxchg_fail_offset_vec G R o s i E l dq sz (off : fin sz) (vs : vec val sz) (v1 v2 : val) {C} :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  l{{{ thread_expr i C (CmpXchg #(l +ₗ off) v1 v2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; i; E
  l{{{ RET (vs !!! off, #false); thread_expr i C (of_val ((vs !!! off, #false))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗{dq} vs }}}.
Proof.
  intros. apply lwp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma lwp_faa_offset G R o s i E l off vs (i1 i2 : Z) {C} :
  vs !! off = Some #i1 →
  l{{{ thread_expr i C (FAA #(l +ₗ off) #i2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    FAA #(l +ₗ off) #i2 @ s; i; E
  l{{{ RET LitV (LitInt i1); thread_expr i C (of_val (LitV (LitInt i1))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (Hlookup Φ) "(TE& T& Hl) HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (lwp_faa with "[$TE $T $Hl1]").
  iIntros "(TE& T& Hl1)". iApply "HΦ". iFrame. iApply "Hl2". iApply "Hl1".
Qed.

Lemma lwp_faa_offset_vec G R o s i E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) {C} :
  vs !!! off = #i1 →
  l{{{ thread_expr i C (FAA #(l +ₗ off) #i2) ∗ (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ)) ∗ l ↦∗ vs }}}
    FAA #(l +ₗ off) #i2 @ s; i; E
  l{{{ RET LitV (LitInt i1); thread_expr i C (of_val (LitV (LitInt i1))%V) ∗ (£ o ∗ thP_kids i G ∗
       ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r)) ∗ l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply lwp_faa_offset.
  by apply vlookup_lookup.
Qed.

End array_laws.

Global Typeclasses Opaque array.
