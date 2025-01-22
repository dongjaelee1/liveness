From iris.algebra Require Import gmap_view gmap gset mono_nat excl_auth.
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
        osatGpreS_goal : inG Σ (gmap_viewR positive (agreeR $ laterO (iPropO Σ)));
        osatGpreS_state : inG Σ (gmapUR positive (prodUR (prodUR bcredUR mono_natUR) mono_natUR));
        osatGpreS_domain : inG Σ (authUR (gsetUR positive));
      }.

  Class osatGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS Σ;
        goal_name : gname;
        state_name : gname;
        domain_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (gmap_viewTRF positive (agreeTRF $ laterTF idTF));
      GFunctor (gmapTRF positive (prodTRF (prodTRF bcredUR mono_natUR) mono_natUR));
      GFunctor (authTRF (gsetUR positive))].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} {Σ} : subG osatΣ Σ → (osatGpreS Σ).
  Proof.
    (* FIXME : solve_inG fails with an error:
Error: Cannot infer this placeholder of type "inG Σ (gmap_viewR positive (agreeR (laterO (iPropO Σ))))" (no type class instance
found) in
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
    repeat match goal with
           | H:subG _ _ |- _ => apply subG_inG in H
           end.
    simpl in *. repeat split; auto.
  Qed.

End osatGS.
Import osatGS.

(* Make the instances local to this file. We cannot use #[local] in the code
above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG osatGpreS_goal osatGpreS_state osatGpreS_domain.

Definition goal_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) :=
  Next P.
Definition oblG_goal `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own goal_name
    (gmap_view_frag i DfracDiscarded (to_agree $ goal_unfold P)).
Global Typeclasses Opaque oblG_goal.
Global Instance: Params (@goal_unfold) 2 := {}.
Global Instance: Params (@oblG_goal) 9 := {}.

Definition oblS_idle `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN{#(q/2)} 0, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_idle.
Global Instance: Params (@oblS_idle) 9 := {}.

Definition oblS_active_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ●MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active_auth.
Global Instance: Params (@oblS_active_auth) 9 := {}.

Definition oblS_active `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ◯MN 1, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_active.
Global Instance: Params (@oblS_active) 9 := {}.

Definition oblS_live `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN{#(q/2)} 0) ]} : gmap _ _).
Global Typeclasses Opaque oblS_live.
Global Instance: Params (@oblS_live) 9 := {}.

Definition oblS_done_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ●MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done_auth.
Global Instance: Params (@oblS_done_auth) 9 := {}.

Definition oblS_done `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own state_name ({[ i := (ε : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ◯MN 1) ]} : gmap _ _).
Global Typeclasses Opaque oblS_done.
Global Instance: Params (@oblS_done) 9 := {}.

Definition oblS_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_credit.
Global Instance: Params (@oblS_credit) 9 := {}.

Definition oblS_bound `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) (a : A) : iProp Σ :=
  own state_name ({[ i := (credit_bound a : (@bcredUR _ _ _ _ WFOrderedCM.orderedCM), ε, ε) ]} : gmap _ _).
Global Typeclasses Opaque oblS_bound.
Global Instance: Params (@oblS_bound) 9 := {}.

Definition oblD_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (D : gset positive) : iProp Σ :=
  own domain_name (●D).
Global Typeclasses Opaque oblD_auth.
Global Instance: Params (@oblD_auth) 9 := {}.

Definition oblD_elem `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ} (i : positive) : iProp Σ :=
  own domain_name (◯{[i]}).
Global Typeclasses Opaque oblD_elem.
Global Instance: Params (@oblD_elem) 9 := {}.

Definition osat `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!osatGS Σ}
  (O : gmap positive obl_type) : iProp Σ :=
  locked
    (∃ (Obls : gmap positive (obl_type * (iProp Σ))%type),
        (⌜O = fst <$> Obls⌝) ∗
        (own goal_name (gmap_view_auth (DfracOwn 1) (to_agree <$> (goal_unfold <$> (snd <$> Obls))))) ∗
        ([∗ map] i ↦ oQ ∈ Obls,
           match oQ with
           | (obl_init a, _) =>
               (∃ a', ⌜leR a a'⌝ ∗ oblS_credit i a' ∗ oblS_idle i 1%Qp ∗ oblS_live i 1)
           | (obl_live a, _) =>
               (∃ a', ⌜leR a a'⌝ ∗ oblS_credit i a' ∗ oblS_active_auth i ∗ oblS_live i 1)
           | (obl_done, Q) =>
               (▷ Q ∗ oblS_active_auth i ∗ oblS_done_auth i)
           end) ∗
        (oblD_auth (dom O))
    )%I.

Section osat.
  Context `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!osatGS Σ}.
  Implicit Types P : iProp Σ.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive i : Contractive (@oblG_goal SI _ _ _ _ WF Σ _ i).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_persistent i P : Persistent (oblG_goal i P).
  Proof. rewrite /oblG_goal. apply _. Qed.

  Global Instance oblS_active_persistent i : Persistent (oblS_active i).
  Proof. rewrite /oblS_active. apply _. Qed.
  Global Instance oblS_done_persistent i : Persistent (oblS_done i).
  Proof. rewrite /oblS_done. apply _. Qed.
  Global Instance oblS_bound_persistent i (a : A) : Persistent (oblS_bound i a).
  Proof. rewrite /oblS_bound. apply _. Qed.

  Global Instance oblD_elem_persistent i : Persistent (oblD_elem i).
  Proof. rewrite /oblD_elem. apply _. Qed.

  Local Infix "/≤" := leR (at level 70).
  Local Infix "/+" := addO (at level 70).
  Local Infix "/<" := ltR (at level 70).
  Local Notation "/0" := OrderedCM.unit.

  Lemma oblS_idle_active i q :
    oblS_idle i q ∗ oblS_active i ⊢ False.
  Proof.
    rewrite /oblS_idle /oblS_active. iIntros "[Hi Ha]".
    iCombine "Hi Ha" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro.
    apply singleton_valid in V. rewrite pair_valid in V. destruct V as [V _].
    rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblS_active_auth_active i :
    oblS_active_auth i ⊢ oblS_active i.
  Proof.
    rewrite /oblS_active_auth /oblS_active. apply own_mono.
    apply singleton_included, option_included. right.
    do 2 eexists. split; [eauto|]. split; [eauto|]. right.
    apply prod_included. simpl. split; [|done].
    apply prod_included. split; [done | apply mono_nat_included].
  Qed.

  Lemma oblS_live_done i q :
    oblS_live i q ∗ oblS_done i ⊢ False.
  Proof.
    rewrite /oblS_live /oblS_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro.
    apply singleton_valid in V. rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblS_done_auth_done i :
    oblS_done_auth i ⊢ oblS_done i.
  Proof.
    rewrite /oblS_done_auth /oblS_done. apply own_mono.
    apply singleton_included, option_included. right.
    do 2 eexists. split; [eauto|]. split; [eauto|]. right.
    apply prod_included. simpl. split; [done | apply mono_nat_included].
  Qed.

  Lemma oblS_credit_mon i a0 a1 :
    a0 /≤ a1 →
    oblS_credit i a1 ⊢ |==> oblS_credit i a0.
  Proof.
    intros LE. rewrite /oblS_credit. apply own_update.
    apply singleton_update.
    apply prod_update; [simpl | reflexivity]. apply prod_update; [simpl | reflexivity].
    by apply credit_update.
  Qed.

  Lemma oblS_credit_split i a0 a1 :
    oblS_credit i (a0 /+ a1) ⊣⊢ oblS_credit i a0 ∗ oblS_credit i a1.
  Proof.
    rewrite /oblS_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite singleton_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite credit_split). iFrame.
  Qed.

  Lemma oblS_credit_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    oblS_credit i a2 ⊢ |==> oblS_credit i a0 ∗ oblS_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply oblS_credit_split. iApply oblS_credit_mon; done.
  Qed.

  Lemma oblS_bound_mon i a0 a1 :
    a0 /≤ a1 →
    oblS_bound i a0 ⊢ |==> oblS_bound i a1.
  Proof.
    intros LE. rewrite /oblS_bound. apply own_update.
    apply singleton_update.
    apply prod_update; [simpl | reflexivity]. apply prod_update; [simpl | reflexivity].
    by apply cmra_update_included, credit_bound_included.
  Qed.

  Lemma oblS_credit_spend i a0 a1 :
    oblS_bound i a0 ∗ oblS_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ oblS_bound i a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite singleton_op -!pair_op !left_id.
      eapply (singleton_updateP
                (λ k, ∃ a2, (k = (credit_bound a2, ε, ε)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (credit_bound a2, ε, ε)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply (prod_updateP (λ k, ∃ a2, (k = (credit_bound a2, ε)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
        { eapply (prod_updateP (λ k, ∃ a2, (k = credit_bound a2) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
          { eapply credit_spend. }
          { eapply cmra_update_updateP. reflexivity. }
          { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
        }
        { eapply cmra_update_updateP. reflexivity. }
        { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
      }
      { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma oblS_credit_induction i a P :
    oblS_bound i a ∗ □(∃ c, ⌜/0 /< c⌝ ∧ ((oblS_credit i c ==∗ P) ==∗ P)) ⊢ |==> P.
  Proof.
    iIntros "[#Hb (%c & %LTc & #HI)]".
    iStopProof. pattern a. revert a. apply (well_founded_induction WFOrderedCM.lt_wf).
    intros a IND. iIntros "[#Hb #HI]".
    iApply "HI". iIntros "Hc".
    iMod (oblS_credit_spend with "[Hb Hc]") as "(%a' & %LE & #Hb')"; [iFrame; done |].
    iClear "Hb". iApply (IND a'); [| iModIntro; iSplit; done].
    apply WFOrderedCM.lt_exists_l. exists c. split; [auto | by rewrite OrderedCM.add_comm_le ].
  Qed.

  Lemma oblD_auth_elem i D :
    oblD_auth D ∗ oblD_elem i ⊢ ⌜i ∈ D⌝.
  Proof.
    rewrite /oblD_auth /oblD_elem -own_op own_valid.
    iIntros "%V". iPureIntro.
    apply auth_both_valid_discrete in V. destruct V as [V _].
    apply gset_included in V. set_solver.
  Qed.

  Lemma oblD_auth_dom_update D i :
    oblD_auth D ⊢ |==> oblD_auth ({[i]} ∪ D) ∗ oblD_elem i.
  Proof.
    rewrite /oblD_auth /oblD_elem -!own_op. apply own_update.
    apply auth_update_alloc, local_update_unital_discrete.
     intros. split; [done|]. rewrite H0. set_solver.
  Qed.

  Lemma osat_oblD_elem i O :
    osat O ∗ oblD_elem i ⊢ ⌜i ∈ dom O⌝.
  Proof.
    rewrite /osat -!lock. iIntros "(Ho & #He)".
    iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom & HoD)".
    iApply (oblD_auth_elem with "[HoD]"). iFrame. done.
  Qed.

  Lemma osat_alloc O a P :
    osat O
    ⊢ |==> ∃ i, osat (<[i:=obl_init a]>O) ∗ ⌜O !! i = None⌝ ∗
                oblG_goal i P ∗ oblS_idle i 1%Qp ∗ oblS_live i 1 ∗ oblS_bound i a ∗ oblD_elem i.
  Proof.
    rewrite /osat -!lock.
    iIntros "Ho". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom & Hod)".
    iMod (@own_unit _ _ _ osatGpreS_state state_name) as "HU".
    iMod ((@own_updateP _ _ _ osatGpreS_state _ state_name) with "HU") as "H".
    { apply (alloc_updateP_cofinite' ∅ ((credit_bound a ⋅ credit a : bcred (H:=WFOrderedCM.orderedCM)), ●MN 0, ●MN 0) (dom O)).
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      apply credit_bound_credit_valid_eq.
    }
    iSimpl. iDestruct "H" as (a' (i & NIN & Ha' & _)) "H". rewrite insert_empty in Ha'. subst a'.
    iAssert (oblS_bound i a ∗ oblS_credit i a ∗ oblS_idle i 1 ∗ oblS_idle i 1 ∗ oblS_live i 1 ∗ oblS_live i 1)%I
      with "[H]" as "(Sb & Sc & Si1 & Si2 & Sl1 & Sl2)".
    { rewrite /oblS_bound /oblS_credit /oblS_idle /oblS_live -!own_op !singleton_op -!pair_op. iSimpl.
      iApply own_mono; [|done].
      apply singleton_included, option_included. right. do 2 eexists. do 2 split; [eauto|].
      left. rewrite !left_id !right_id. rewrite -!mono_nat_auth_dfrac_op dfrac_op_own Qp.half_half.
      done.
    }
    iMod (own_update with "Hoa") as "Hoa".
    { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree $ goal_unfold P)); [| done | done].
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done |].
      set_solver.
    }
    iDestruct "Hoa" as "[Hoa #Hg]".
    iMod ((oblD_auth_dom_update _ i) with "Hod") as "(Hod & He)".
    iModIntro. iExists i. iFrame. rewrite -!lock. iSplitL.
    { iClear "Hg". iExists (<[i:=(obl_init a, P)]>Obls). iSplit.
      { iPureIntro. subst O. by rewrite fmap_insert. }
      iSplitL "Hoa".
      { iEval (rewrite !fmap_insert). iFrame. }
      iSplitR "Hod".
      { iApply big_sepM_insert.
        { subst O. apply not_elem_of_dom_1. set_solver. }
        iFrame. done.
      }
      { by rewrite dom_insert_L. }
    }
    iSplit; [|done]. iPureIntro.
    subst O. apply not_elem_of_dom_1. set_solver.
  Qed.

  Lemma osat_progress_one O i q o1 o2 :
    (O !! i = Some o1) →
    (obl_type_lt o2 o1) →
    osat O ∗ oblS_active i ∗ oblS_live i q
    ⊢ |==> osat (<[i:=o2]> O) ∗ oblS_live i q ∗ ∃ a, oblS_credit i a ∗ ⌜/0 /< a⌝.
  Proof.
    intros LU LT. rewrite /osat -!lock.
    iIntros "(Ho & #Ha & Hl)". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom & HoD)".
    assert (LU2 : exists Q, Obls !! i = Some (o1, Q)).
    { subst O. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o1, o2; simpl in LT; try contradiction LT.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & IDLE & _)".
      iPoseProof (oblS_idle_active with "[IDLE Ha]") as "%F"; [iFrame; done | done].
    - iDestruct "LU" as "(%a' & %LE & CRED & ACTa & LIVE)".
      apply WFOrderedCM.lt_exists_l in LT. destruct LT as (b&LTb&LEb).
      iMod (oblS_credit_mon_split with "CRED") as "[CRED CRED']".
      { etrans; [|eauto]. eauto. }
      iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live a0, Q))  with "[Hom ACTa LIVE CRED]") as "Hom".
      { apply lookup_delete. }
      { iFrame. iExists a0. iFrame. done. }
      iModIntro. iFrame. iSplit; [|done]. iSplit.
      { iPureIntro. rewrite fmap_insert fmap_delete.
        rewrite -HO. simpl. symmetry. apply insert_delete_insert.
      }
      iSplitL "Hoa".
      { assert (snd <$> Obls = (snd <$> <[i:=(obl_live a0, Q)]> (delete i Obls))).
        { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete.
          rewrite lookup_fmap. rewrite LU2. done.
        }
        by iEval (rewrite -H).
      }
      rewrite dom_insert_lookup_L; [done |].
      by rewrite LU.
    - iExFalso. subst. iDestruct "LU" as "(_ & _ & DONE)".
      iPoseProof (oblS_live_done with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (oblS_done_auth_done with "DONE") as "#D". done.
  Qed.

  TODO

    osat_induction?

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
