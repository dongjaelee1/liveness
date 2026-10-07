From iris.proofmode Require Import proofmode environments.
From lantana.base_logic Require Export opreds.
From iris.prelude Require Import options.

(** * Lexicographic witness induction with a packaged budget

  A blocking loop often waits on a *sequence* of obligations rather than on a
  single one: the ticket-lock [acquire] loop waits on the current holder's
  unlock obligation, and when that is discharged it waits on the next holder's,
  and so on, finitely often because the waiter's ticket distance strictly
  decreases on every change of holder.

  In the style of transition invariants (Podelski & Rybalchenko; Cook,
  Podelski & Rybalchenko's TERMINATOR), such a loop is justified by a finite
  family of well-founded relations, every iteration being covered by one of
  them:

  - the *variant* [a : A] decreased (and the obligation we wait on may change), or
  - the variant is unchanged and the witness of the obligation we wait on decreased.

  Lantana's carriers hold a single ordinal that burns on every step, so a
  disjunctive argument has to be paid for with a single budget. Doing this by
  hand means charging the loop with a product such as
  [((m ⊕ (m × ▽)) × ℵ) ⊕ (m × ▽)] and running two nested inductions, one on
  [a] and an inner one on the witness. This file packages that into one
  predicate [lex_fuels] with one induction principle [lex_fuels_ind]: the
  proof of the loop body only ever chooses which component made progress
  (the two conjuncts of the hypothesis of [lex_fuels_ind]), reclaims the
  per-iteration budget [m], and never sees the combined ordinal, which lives
  in [lex_budget]. *)

Section lex_fuels.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.
  Context {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA).

  (** The combined budget, hidden from the user of [lex_fuels_ind]: for each
      value of the variant, [m] for the iteration in which the variant drops
      and [m × ▽] for the witness induction on the obligation waited on there,
      plus [m × ▽] for the initial obligation. *)
  Definition lex_budget (m : measure) : measure :=
    (((m ⊕ (m × ▽)) × ℵ) ⊕ (m × ▽))%M.

  (** [lex_fuels a k ℓ G l m]: the carriers [G] at layer [l] hold enough fuel
      to wait at variant [a] on obligation [k] at layer [ℓ < l], reclaiming
      [m] fuel per iteration. *)
  Definition lex_fuels (a : A) (k : oid) (ℓ : ord.t) (G : gset ocid) (l : ord.t) (m : measure) : iProp Σ :=
    witP_layer k ℓ ∗
    embed_fuels wf_ltA a (gset_to_gmap (l, (m ⊕ (m × ▽))%M) G) ∗
    ∃ α, wit_fuels k ℓ α (gset_to_gmap (l, m) G).

  Lemma lex_fuels_init a k ℓ G l m :
    (ℓ < l)%ordi →
    witP_layer k ℓ -∗
    ([∗ set] g ∈ G, crP_fuel g l (lex_budget m)) ==∗
    lex_fuels a k ℓ G l m.
  Proof.
    iIntros (LT) "#Wl Fs". rewrite /lex_budget.
    iPoseProof (crP_fuel_add_set with "Fs") as "[Fe Fw]".
    iPoseProof (embed_fuels_init wf_ltA a) as "E0".
    iMod (embed_fuels_add_map with "E0 Fe") as "E". rewrite map_union_empty.
    iPoseProof (wit_fuels_init with "Wl") as "(%α& W0)".
    iMod (wit_fuels_add_map with "W0 Fw") as "W". 1: done. rewrite map_union_empty.
    iModIntro. iFrame "Wl E". eauto.
  Qed.

  (** Inner step: the obligation [k] made progress; the variant is unchanged. *)
  Lemma lex_fuels_wit_step a k ℓ G l m :
    lex_fuels a k ℓ G l m -∗ witP_cred k Ord.one ==∗
    lex_fuels a k ℓ G l m ∗ ([∗ set] g ∈ G, crP_fuel g l m).
  Proof.
    iIntros "(#Wl& E& %α& W) Wc".
    iMod (wit_fuels_decr with "W Wc") as "(%α'& _& W& Fs)".
    rewrite big_sepM_gset_to_gmap. iFrame "Wl E Fs". eauto.
  Qed.

  (** Outer step: the variant decreased; we may now wait on a new obligation
      [k'] at any layer [ℓ' < l]. The remaining witness budget of [k] is dropped. *)
  Lemma lex_fuels_var_step a a' k k' ℓ ℓ' G l m :
    (ℓ' < l)%ordi → ltA a' a →
    lex_fuels a k ℓ G l m -∗ witP_layer k' ℓ' ==∗
    lex_fuels a' k' ℓ' G l m ∗ ([∗ set] g ∈ G, crP_fuel g l m).
  Proof.
    iIntros (LTl LTa) "(_& E& _) #Wl'".
    iMod (embed_fuels_decr _ _ a' with "E") as "[E Fs]". 1: done.
    rewrite big_sepM_gset_to_gmap. iPoseProof (crP_fuel_add_set with "Fs") as "[Fm Fw]".
    iPoseProof (wit_fuels_init with "Wl'") as "(%α& W0)".
    iMod (wit_fuels_add_map with "W0 Fw") as "W". 1: done. rewrite map_union_empty.
    iModIntro. iFrame "Wl' E Fm". eauto.
  Qed.

  (** The induction principle. To prove [P a k ℓ] (the loop at variant [a],
      waiting on [k] at layer [ℓ]) one proves the body under an inductive
      hypothesis that offers, as a non-separating conjunction so that the body
      picks exactly one, the two ways of making progress; each reclaims [m]
      fuel on [G]. *)
  Lemma lex_fuels_ind G l m (P : A → oid → ord.t → iProp Σ) a k ℓ :
    (ℓ < l)%ordi →
    □ (∀ a k ℓ, ⌜(ℓ < l)%ordi⌝ -∗ witP_layer k ℓ -∗
         ((witP_cred k Ord.one ==∗ ([∗ set] g ∈ G, crP_fuel g l m) ∗ P a k ℓ)
          ∧ (∀ a' k' ℓ', ⌜ltA a' a⌝ -∗ ⌜(ℓ' < l)%ordi⌝ -∗ witP_layer k' ℓ' ==∗
                         ([∗ set] g ∈ G, crP_fuel g l m) ∗ P a' k' ℓ'))
         ==∗ P a k ℓ) ∗
    lex_fuels a k ℓ G l m
    ⊢ |==> P a k ℓ.
  Proof.
    iIntros (LTl) "[#H LF]". iRevert (k ℓ LTl) "LF".
    iInduction a as [a IHa] using (well_founded_ind wf_ltA).
    iIntros (k ℓ LTl) "(#Wl& E& %α& W)".
    iAssert (|==> (embed_fuels wf_ltA a (gset_to_gmap (l, (m ⊕ (m × ▽))%M) G) -∗ |==> P a k ℓ))%I
      with "[W]" as ">HP"; last by iApply ("HP" with "E").
    iApply (wit_fuels_ind with "[$W]").
    iIntros "!> IHw !> E". iApply ("H" with "[//] Wl"). iSplit.
    - iIntros "Wc". iMod ("IHw" with "Wc") as "[Fs HP]".
      iEval (rewrite big_sepM_gset_to_gmap) in "Fs". iFrame "Fs". by iApply ("HP" with "E").
    - iIntros (a' k' ℓ' LTa LTl') "#Wl'".
      iMod (embed_fuels_decr _ _ a' with "E") as "[E Fs]". 1: done.
      iEval (rewrite big_sepM_gset_to_gmap) in "Fs". iPoseProof (crP_fuel_add_set with "Fs") as "[Fm Fw]".
      iPoseProof (wit_fuels_init with "Wl'") as "(%α'& W0)".
      iMod (wit_fuels_add_map with "W0 Fw") as "W'". 1: done. rewrite map_union_empty.
      iMod ("IHa" with "[//] [//] [$Wl' $E W']") as "$"; last done.
      eauto.
  Qed.

End lex_fuels.

(** [iLexInduction wf a k ℓ LT LF]: run [lex_fuels_ind] on the current goal,
    which must be the loop's goal with the variant [a], the obligation [k] and
    its layer [ℓ] free (everything else reverted). [LT : ℓ < l] and [LF] is a
    specialization pattern for [lex_fuels a k ℓ G l m], e.g. ["[$LF]"]. The
    predicate [P] of [lex_fuels_ind] is obtained by abstracting the goal over
    [a], [k] and [ℓ]; what remains is the body obligation (the [□ ∀ ...]
    premise of [lex_fuels_ind]). *)
Tactic Notation "iLexInduction" constr(wf) ident(a) ident(k) ident(l) constr(LT) constr(LF) :=
  lazymatch goal with
  | |- envs_entails _ ?G =>
      let G' := eval pattern a, k, l in G in
      lazymatch G' with
      | ?P _ _ _ =>
          iPoseProof (lex_fuels_ind wf _ _ _ P a k l LT with LF) as "__lex_H";
          [ | iMod "__lex_H" as "__lex_H"; iExact "__lex_H" ]
      end
  end.
