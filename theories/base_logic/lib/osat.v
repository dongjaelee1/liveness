From iris.algebra Require Import gmap_view gset mono_nat excl_auth.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import wfOrderedCM bcred.

Inductive obl_type `{WFOrderedCM.t A leR addO ltR} : Type :=
| obl_init (a : A) | obl_live (a : A) | obl_done.

Definition obl_type_lt `{WFOrderedCM.t A leR addO ltR} (l1 l2 : obl_type) : Prop :=
  match l1, l2 with
  | obl_init a1, obl_init a2 => a1 = a2
  | obl_live a1, obl_live a2 => ltR a1 a2
  | obl_done, obl_done => True
  | _, _ => False
  end.

Definition obl_type_lt_gmap `{WFOrderedCM.t A leR addO ltR} (ls1 ls2 : gmap positive obl_type) : Prop :=
  map_Forall2 (λ _ l1 l2, obl_type_lt l1 l2) ls1 ls2.

(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [osatGS] module. The module [osatGS] is thus exported in
[fancy_updates], where [osat] is only imported. *)
Module osatGS.
  Class osatGpreS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_obl :
        inG Σ (gmap_viewR positive
                 (prodUR (prodUR (prodUR (optionUR (agreeR $ laterO (iPropO Σ))) bcredUR) mono_natUR) mono_natUR));
        osatGpreS_domain : inG Σ (excl_authUR (gset positive));
      }.

  Class osatGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS Σ;
        obligation_name : gname;
        domain_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (gmap_viewTRF positive (prodTRF (prodTRF (prodTRF (optionTRF $ agreeTRF $ laterTF idTF) bcredUR) mono_natUR) mono_natUR));
      GFunctor (excl_authTRF (gsetO positive))].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} {Σ} : subG osatΣ Σ → (osatGpreS Σ).
  Proof.
    (* FIXME : solve_inG fails with an error:
Error: Cannot infer this placeholder of type
"inG Σ
   (gmap_viewR positive
      (prodR (prodR (prodR (agreeR (laterO (iPropO Σ))) bcredUR) mono_natUR) mono_natUR))" (no type
class instance found) in
environment:
SI : indexT
A : Type
leR : A → A → Prop
addO : A → A → A
ltR : A → A → Prop
WF : WFOrderedCM.t leR addO ltR
Σ : gFunctors
H : subG osatΣ Σ
     *)
    intros. unfold osatΣ in H.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    apply subG_inG in s. apply subG_inG in s0. simpl in *. split; assumption.
  Qed.

End osatGS.
Import osatGS.

(* Make the instances local to this file. We cannot use #[local] in the code
above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG osatGpreS_obl osatGpreS_domain.

Definition obl_promise_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) :=
  Next P.
Definition oblG_promise `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (Some $ to_agree $ obl_promise_unfold P, ε, ε, ε)).
Global Typeclasses Opaque oblG_promise.
Global Instance: Params (@obl_promise_unfold) 2 := {}.
Global Instance: Params (@oblG_promise) 9 := {}.

Definition oblG_idle `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN{#(q/2)} 0, ε)).
Global Typeclasses Opaque oblG_idle.
Global Instance: Params (@oblG_idle) 9 := {}.

Definition oblG_active_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN 1, ε)).
Global Typeclasses Opaque oblG_active_auth.
Global Instance: Params (@oblG_active_auth) 9 := {}.

Definition oblG_active `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ◯MN 1, ε)).
Global Typeclasses Opaque oblG_active.
Global Instance: Params (@oblG_active) 9 := {}.

Definition oblG_live `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN{#(1/2)} 0)).
Global Typeclasses Opaque oblG_live.
Global Instance: Params (@oblG_live) 9 := {}.

Definition oblG_done_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN 1)).
Global Typeclasses Opaque oblG_done_auth.
Global Instance: Params (@oblG_done_auth) 9 := {}.

Definition oblG_done `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ◯MN 1)).
Global Typeclasses Opaque oblG_done.
Global Instance: Params (@oblG_done) 9 := {}.

Definition oblG_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (a : A) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, credit a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε)).
Global Typeclasses Opaque oblG_credit.
Global Instance: Params (@oblG_credit) 9 := {}.

Definition oblG_bound `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (a : A) : iProp Σ :=
  own obligation_name
    (gmap_view_frag i DfracDiscarded (ε, credit_bound a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε)).
Global Typeclasses Opaque oblG_bound.
Global Instance: Params (@oblG_bound) 9 := {}.

Definition oblD_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (D : gset positive) : iProp Σ :=
  own domain_name (●E D).
Global Typeclasses Opaque oblD_auth.
Global Instance: Params (@oblD_auth) 9 := {}.

Definition oblD `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (D : gset positive) : iProp Σ :=
  own domain_name (◯E D).
Global Typeclasses Opaque oblD.
Global Instance: Params (@oblD) 9 := {}.

Definition osat `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ}
  (O : gmap positive obl_type) : iProp Σ :=
  locked
    (∃ (Obls : gmap positive (obl_type * ((iProp Σ) * (A * A) * nat * nat))%type),
        (⌜O = fst <$> Obls⌝) ∗
        (own obligation_name
           (gmap_view_auth (DfracOwn 1)
              ((λ '(_, (Q, aa, n1, n2)),
                  ((Some $ to_agree $ (obl_promise_unfold Q),
                      (credit_bound aa.1 ⋅ credit aa.2),
                        ●MN n1,
                          ●MN n2) : (prodUR (prodUR (prodUR (optionUR (agreeR $ laterO (iPropO Σ))) bcredUR) mono_natUR) mono_natUR)))
                 <$> Obls))) ∗
        ([∗ map] i ↦ oQ ∈ Obls,
           match oQ with
           | (obl_init a, (_, (_, a'), _, _)) =>
               (⌜leR a a'⌝ ∗ oblG_credit i a' ∗ oblG_idle i 1%Qp ∗ oblG_live i)
           | (obl_live a, (_, (_, a'), _, _)) =>
               (⌜leR a a'⌝ ∗ oblG_credit i a' ∗ oblG_active_auth i ∗ oblG_live i)
           | (obl_done, (Q, _, _, _)) =>
               (▷ Q ∗ oblG_active_auth i ∗ oblG_done_auth i)
           end) ∗
        (oblD_auth (dom O))
    )%I.

TODO

(* Lemma test `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} i : Persistent (oblG_done i). *)
(* Proof. apply own_core_persistent. typeclasses eauto. Qed. *)
(* Lemma test0 `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} i : Persistent (oblG_active i). *)
(* Proof. apply own_core_persistent. typeclasses eauto. Qed. *)
(* Lemma test1 `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} i P : Persistent (oblG i P). *)
(* Proof. apply own_core_persistent. typeclasses eauto. Qed. *)
(* Lemma test2 `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} i a : Persistent (oblG_bound i a). *)
(* Proof. apply own_core_persistent. typeclasses eauto. Qed. *)

Definition osat `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name
      (gmap_view_auth (DfracOwn 1) (to_agree <$> (obl_goal_unfold <$> I))) ∗
    [∗ map] i ↦ Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})%I.

Section osat.
Context `{SI : indexT} `{!osatGS Σ}.
Implicit Types P : iProp Σ.

(* Invariants *)
Local Instance obl_goal_unfold_contractive : Contractive (@obl_goal_unfold SI Σ).
Proof. solve_contractive. Qed.
Global Instance oblG_contractive i : Contractive (@oblG SI Σ _ i).
Proof. solve_contractive. Qed.
Global Instance oblG_persistent i P : Persistent (oblG i P).
Proof. rewrite /oblG. apply _. Qed.

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
  own invariant_name (gmap_view_auth (DfracOwn 1) (to_agree <$> (obl_goal_unfold <$> I))) ∗
  own invariant_name (gmap_view_frag i DfracDiscarded (to_agree $ obl_goal_unfold P)) ⊢
  ∃ Q, ⌜I !! i = Some Q⌝ ∗ ▷ (Q ≡ P).
Proof.
  rewrite -own_op own_valid gmap_view_both_validI_total.
  iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
  case: (I !! i)=> [Q|] /=; last first.
  { iDestruct "HQ'" as %?. done. }
  iDestruct "HQ'" as %[= <-]. iExists Q; iSplit; first done.
  rewrite to_agree_includedI internal_eq_sym -later_equivI. done.
Qed.

Lemma oblG_open i P : osat ∗ oblG i P ∗ ownE {[i]} ⊢ osat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /oblG /osat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ $]|HiE'] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma oblG_close i P : osat ∗ oblG i P ∗ ▷ P ∗ ownD {[i]} ⊢ osat ∗ ownE {[i]}.
Proof.
  rewrite /oblG /osat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ ?]|$] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma oblG_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  osat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ osat ∗ oblG i P.
Proof.
  iIntros (Hfresh) "[Hw HP]". rewrite /osat -!lock.
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
  iModIntro; iExists i;  iSplit; [done|]. rewrite /oblG; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite !fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma oblG_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  osat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ osat) ∗ oblG i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite /osat -!lock. iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree _)); [|done..].
    by rewrite /= !lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /oblG; iFrame "HiP".
  rewrite -/(ownD _). iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite !fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". by iRight.
Qed.
End osat.

(* Allocation of an initial world *)
Lemma osat_alloc `{SI : indexT} `{!osatGpreS Σ} : ⊢ |==> ∃ _ : osatGS Σ, osat ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (OsatG SI _ _ γI γE γD).
  rewrite /osat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.
