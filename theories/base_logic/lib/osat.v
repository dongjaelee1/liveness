From iris.algebra Require Import gmap_view gset mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import orderedCM bcred.

Inductive obl_type `{OrderedCM.t A leR addO} : Type :=
| obl_init (a : A) | obl_live (a : A) | obl_done.

Definition obl_type_lt `{OrderedCM.t A leR addO} (l1 l2 : obl_type) : Prop :=
  match l1, l2 with
  | obl_init a1, obl_init a2 => a1 = a2
  | obl_live a1, obl_live a2 => OrderedCM.le a1 a2
  | obl_done, obl_done => True
  | _, _ => False
  end.

(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [osatGS] module. The module [osatGS] is thus exported in
[fancy_updates], where [osat] is only imported. *)
Module osatGS.
  Class osatGpreS `{SI : indexT} `{OrderedCM.t A leR addO} (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_goal :
        inG Σ (gmap_viewR positive (prodR (prodR (prodR (agreeR $ laterO (iPropO Σ)) bcredUR) mono_natUR) mono_natUR));
        osatGpreS_dom : inG Σ (gset_disjR positive);
      }.

  Class osatGS `{SI : indexT} `{OrderedCM.t A leR addO} (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS Σ;
        obligation_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{OrderedCM.t A leR addO} : gFunctors :=
    #[GFunctor (gmap_viewTRF positive (prodTRF (prodTRF (prodTRF (agreeTRF $ laterTF idTF) bcredUR) mono_natUR) mono_natUR));
      GFunctor (gset_disjR positive)].

  Global Instance subG_osatΣ `{SI : indexT} `{OrderedCM.t A leR addO} {Σ} : subG osatΣ Σ → osatGpreS Σ.
  Proof. solve_inG. Qed.
End osatGS.
Import osatGS.

TODO

(* Make the instances local to this file. We cannot use #[local] in the code
above, as that would make the instances local to the module. *)
Local Existing Instances wsat_inG wsatGpreS_inv wsatGpreS_enabled wsatGpreS_disabled.

Definition invariant_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) :=
  Next P.
Definition ownI `{SI : indexT} `{!wsatGS Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own invariant_name
    (gmap_view_frag i DfracDiscarded (to_agree $ invariant_unfold P)).
Global Typeclasses Opaque ownI.
Global Instance: Params (@invariant_unfold) 2 := {}.
Global Instance: Params (@ownI) 4 := {}.

Definition ownE `{SI : indexT} `{!wsatGS Σ} (E : coPset) : iProp Σ :=
  own enabled_name (CoPset E).
Global Typeclasses Opaque ownE.
Global Instance: Params (@ownE) 4 := {}.

Definition ownD `{SI : indexT} `{!wsatGS Σ} (E : gset positive) : iProp Σ :=
  own disabled_name (GSet E).
Global Typeclasses Opaque ownD.
Global Instance: Params (@ownD) 4 := {}.

Definition wsat `{SI : indexT} `{!wsatGS Σ} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name
      (gmap_view_auth (DfracOwn 1) (to_agree <$> (invariant_unfold <$> I))) ∗
    [∗ map] i ↦ Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})%I.

Section wsat.
Context `{SI : indexT} `{!wsatGS Σ}.
Implicit Types P : iProp Σ.

(* Invariants *)
Local Instance invariant_unfold_contractive : Contractive (@invariant_unfold SI Σ).
Proof. solve_contractive. Qed.
Global Instance ownI_contractive i : Contractive (@ownI SI Σ _ i).
Proof. solve_contractive. Qed.
Global Instance ownI_persistent i P : Persistent (ownI i P).
Proof. rewrite /ownI. apply _. Qed.

Lemma ownE_empty : ⊢ |==> ownE ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (coPset_disjUR) enabled_name).
Qed.
Lemma ownE_op E1 E2 : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof. intros. by rewrite /ownE -own_op coPset_disj_union. Qed.
Lemma ownE_disjoint E1 E2 : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownE -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownE_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownE_op|].
  iIntros "HE". iDestruct (ownE_disjoint with "HE") as %?.
  iSplit; first done. iApply ownE_op; by try iFrame.
Qed.
Lemma ownE_singleton_twice i : ownE {[i]} ∗ ownE {[i]} ⊢ False.
Proof. rewrite ownE_disjoint. iIntros (?); set_solver. Qed.

Lemma ownD_empty : ⊢ |==> ownD ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (gset_disjUR positive) disabled_name).
Qed.
Lemma ownD_op E1 E2 : E1 ## E2 → ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof. intros. by rewrite /ownD -own_op gset_disj_union. Qed.
Lemma ownD_disjoint E1 E2 : ownD E1 ∗ ownD E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownD -own_op own_valid. by iIntros (?%gset_disj_valid_op). Qed.
Lemma ownD_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownD_op|].
  iIntros "HE". iDestruct (ownD_disjoint with "HE") as %?.
  iSplit; first done. iApply ownD_op; by try iFrame.
Qed.
Lemma ownD_singleton_twice i : ownD {[i]} ∗ ownD {[i]} ⊢ False.
Proof. rewrite ownD_disjoint. iIntros (?); set_solver. Qed.

Lemma invariant_lookup (I : gmap positive (iProp Σ)) i P :
  own invariant_name (gmap_view_auth (DfracOwn 1) (to_agree <$> (invariant_unfold <$> I))) ∗
  own invariant_name (gmap_view_frag i DfracDiscarded (to_agree $ invariant_unfold P)) ⊢
  ∃ Q, ⌜I !! i = Some Q⌝ ∗ ▷ (Q ≡ P).
Proof.
  rewrite -own_op own_valid gmap_view_both_validI_total.
  iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
  case: (I !! i)=> [Q|] /=; last first.
  { iDestruct "HQ'" as %?. done. }
  iDestruct "HQ'" as %[= <-]. iExists Q; iSplit; first done.
  rewrite to_agree_includedI internal_eq_sym -later_equivI. done.
Qed.

Lemma ownI_open i P : wsat ∗ ownI i P ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ $]|HiE'] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i P : wsat ∗ ownI i P ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ ?]|$] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof.
  iIntros (Hfresh) "[Hw HP]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree _)); [|done..].
    by rewrite /= !lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite !fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree _)); [|done..].
    by rewrite /= !lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  rewrite -/(ownD _). iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite !fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". by iRight.
Qed.
End wsat.

(* Allocation of an initial world *)
Lemma wsat_alloc `{SI : indexT} `{!wsatGpreS Σ} : ⊢ |==> ∃ _ : wsatGS Σ, wsat ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG SI _ _ γI γE γD).
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.
