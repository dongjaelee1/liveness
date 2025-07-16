From iris.algebra Require Import functions reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris Require Import bank language.

Section gmap.
  Context {K : Type} {EqDecision0 : EqDecision K} {Countable0 : Countable K}.

  Lemma map_Forall2_map_Forall {A B : Type} (R : K → A → B → Prop) (m1 : gmap K A) (m2 : gmap K B) :
    map_Forall2 R m1 m2 → dom m1 ≡ dom m2 ∧ map_Forall (λ k a, ∃ b, m2 !! k = Some b ∧ R k a b) m1.
  Proof.
    intros Hmf. pose proof (map_Forall2_dom _ _ _ Hmf) as Hd. split; [auto|].
    intros k. specialize (Hmf k). intros. assert (is_Some (m2 !! k)).
    { destruct (m2 !! k) eqn:Hm2; [eauto|]. exfalso. apply elem_of_dom_2 in H. apply not_elem_of_dom in Hm2. set_solver. }
    destruct H0. eexists; esplit; [eauto|]. rewrite H H0 in Hmf. by inv Hmf.
  Qed.

  Lemma map_Forall_map_Forall_2 {A B : Type} (R : K → A → B → Prop) (m1 : gmap K A) (m2 : gmap K B) :
    (dom m1 ≡ dom m2 ∧ map_Forall (λ k a, ∃ b, m2 !! k = Some b ∧ R k a b) m1) → map_Forall2 R m1 m2.
  Proof.
    intros [Hd Hmf]. intros k. destruct (m1 !! k) eqn:Hm1.
    - specialize (Hmf k a Hm1). simpl in Hmf. destruct Hmf as (?&?&?). rewrite H. by econstructor.
    - assert (m2 !! k = None).
      { destruct (m2 !! k) eqn:Hm2; [|auto]. exfalso. apply elem_of_dom_2 in Hm2. apply not_elem_of_dom in Hm1. set_solver. }
      rewrite H. econstructor.
  Qed.

  Lemma map_Forall2_lookup_l {A B : Type} (R : K → A → B → Prop) (m1 : gmap K A) (m2 : gmap K B) :
    map_Forall2 R m1 m2 → ∀ i a, m1 !! i = Some a → ∃ b, m2 !! i = Some b ∧ R i a b.
  Proof.
    intros. specialize (H i). rewrite H0 in H. inv H. eauto.
  Qed.

  Lemma map_Forall2_lookup_r {A B : Type} (R : K → A → B → Prop) (m1 : gmap K A) (m2 : gmap K B) :
    map_Forall2 R m1 m2 → ∀ i b, m2 !! i = Some b → ∃ a, m1 !! i = Some a ∧ R i a b.
  Proof.
    intros. specialize (H i). rewrite H0 in H. inv H. eauto.
  Qed.

  Lemma map_Forall2_ind {A B : Type} (R : K → A → B → Prop) (Q : gmap K A → gmap K B → Prop) :
    Q ∅ ∅ →
    (∀ m1 m2 (i : K) (x : A) (y : B),
       m1 !! i = None → m2 !! i = None → R i x y → map_Forall2 R m1 m2 → Q m1 m2 → Q (<[i:=x]>m1) (<[i:=y]>m2)) →
    ∀ m1 m2, map_Forall2 R m1 m2 → Q m1 m2.
  Proof.
    intros Hempty Hind. apply (map_ind (K:=K) (A:=A) (λ m1, ∀ (m2 : gmap K B), map_Forall2 R m1 m2 → Q m1 m2)).
    - intros. apply map_Forall2_empty_inv_l in H. by subst.
    - intros i a m1 Him1 IH m2 Hmf2. apply map_Forall2_insert_inv_l in Hmf2; [|auto].
      destruct Hmf2 as (b&m2'&Hm2'&Him2&HR&Hmf2). specialize (Hind _ _ _ _ _ Him1 Him2 HR Hmf2 (IH _ Hmf2)).
      rewrite Hm2'. auto.
  Qed.

End gmap.

Module schedfairGS.

  Class schedfairGpreS `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairGpreS {
        schedfairGpreS_state : inG Σ (discrete_funUR (λ (k : thread_id), bankUR));
      }.

  Class schedfairGS `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairG {
        schedfair_inG : schedfairGpreS Σ;
        state_name : gname;
      }.

  (* Do we need discrete_fun version of gmapTRF? Why do we even need Functor? *)
  Definition schedfairΣ `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (discrete_funUR (λ (k : thread_id), bankUR))
      ].

  Global Instance subG_schedfairΣ `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} {Σ} : subG schedfairΣ Σ → (schedfairGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End schedfairGS.
Import schedfairGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances schedfair_inG schedfairGpreS_state.

Definition sfS_fuel_bound `{SI : indexT} `{WFOCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) (q : Qp) : iProp Σ :=
  own state_name (discrete_fun_singleton i (debt a q)).
Global Typeclasses Opaque sfS_fuel_bound.
Global Instance: Params (@sfS_fuel_bound) 9 := {}.

Definition sfS_fuel_credit `{SI : indexT} `{WFOCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) : iProp Σ :=
  own state_name (discrete_fun_singleton i (cash a)).
Global Typeclasses Opaque sfS_fuel_credit.
Global Instance: Params (@sfS_fuel_credit) 9 := {}.

Definition sfS_fuel_credit_forall `{SI : indexT} `{WFOCM.t A leR addO ltR} `{!schedfairGS Σ} : iProp Σ :=
  (∀ i, ∃ c, ⌜ ltR OCM.unit c ⌝ ∗ sfS_fuel_credit i c)%I.
Global Typeclasses Opaque sfS_fuel_credit_forall.
Global Instance: Params (@sfS_fuel_credit_forall) 8 := {}.

Definition schedfairI `{SI : indexT} `{WFOCM.t A leR addO ltR} `{!schedfairGS Σ}
  (δ : gmap thread_id A) : iProp Σ :=
  locked
    (∃ a, own state_name ((λ k, if (decide (k ∈ dom δ)) then ε else (debt a 1)) : discrete_fun _) ∗
     [∗ map] i ↦ f ∈ δ, (∃ f', ⌜leR f f'⌝ ∗ sfS_fuel_credit i f'))%I.

Section sfi.
  Context `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} `{!schedfairGS Σ}.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := leR (at level 70).
  Local Infix "/+" := addO (at level 70).
  Local Infix "/<" := ltR (at level 70).
  Local Infix "/∧" := OCM.meet (at level 70).
  Local Notation "/0" := OCM.unit.

  Lemma sfS_fuel_credit_eq i a0 a1 :
    a0 /= a1 →
    sfS_fuel_credit i a0 = sfS_fuel_credit i a1.
  Proof.
    intros EQ. rewrite /sfS_fuel_credit. by erewrite cash_eq.
  Qed.

  Lemma sfS_fuel_credit_mon i a0 a1 :
    a0 /≤ a1 →
    sfS_fuel_credit i a1 ⊢ |==> sfS_fuel_credit i a0.
  Proof.
    intros LE. rewrite /sfS_fuel_credit. apply own_update.
    by apply discrete_fun_singleton_update, cash_update.
  Qed.

  Lemma sfS_fuel_credit_add i a0 a1 :
    sfS_fuel_credit i (a0 /+ a1) ⊣⊢ sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite /sfS_fuel_credit -own_op discrete_fun_singleton_op cash_add. f_equal.
  Qed.

  Lemma sfS_fuel_credit_mon_add i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    sfS_fuel_credit i a2 ⊢ |==> sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply sfS_fuel_credit_add. by iApply sfS_fuel_credit_mon.
  Qed.

  Lemma sfS_fuel_bound_eq i a0 a1 q :
    a0 /= a1 →
    sfS_fuel_bound i a0 q = sfS_fuel_bound i a1 q.
  Proof.
    intros EQ. rewrite /sfS_fuel_bound. by erewrite debt_eq.
  Qed.

  Lemma sfS_fuel_bound_mon i a0 a1 q:
    a0 /≤ a1 →
    sfS_fuel_bound i a0 q ⊢ |==> sfS_fuel_bound i a1 q.
  Proof.
    intros LE. rewrite /sfS_fuel_bound. apply own_update.
    by apply discrete_fun_singleton_update, debt_update.
  Qed.

  Lemma sfS_fuel_bound_add i a0 a1 q0 q1 :
    sfS_fuel_bound i (a0 /∧ a1) (q0 + q1) ⊣⊢ sfS_fuel_bound i a0 q0 ∗ sfS_fuel_bound i a1 q1.
  Proof.
    rewrite /sfS_fuel_bound -own_op discrete_fun_singleton_op debt_add. f_equal.
  Qed.

  Lemma sfS_fuel_pay i a0 a1 q :
    sfS_fuel_bound i a0 q ∗ sfS_fuel_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ sfS_fuel_bound i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite discrete_fun_singleton_op.
      eapply (discrete_fun_singleton_updateP' i (λ k, ∃ a2, (k = (debt a2 q)) ∧ (a1 /+ a2 /≤ a0))).
      eapply debt_pay.
    }
    iSimpl. iDestruct "H" as "((% & % & %a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma sfS_fuel_owe i a0 a1 :
    sfS_fuel_bound i a0 1 ⊢ |==> sfS_fuel_bound i (a0 /+ a1) 1 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_update with "H") as "H".
    { eapply (discrete_fun_singleton_update i _ (debt (a0 /+ a1) 1 ⋅ cash a1)), debt_owe. }
    iModIntro. by rewrite discrete_fun_singleton_op.
  Qed.

  Lemma schedfairI_thread_is_exec δ i a q :
    schedfairI δ ∗ sfS_fuel_bound i a q
    ⊢ ⌜is_Some(δ !! i)⌝.
  Proof.
    rewrite /schedfairI -!lock. iIntros "((% & Htk & Hs) & He)".
    iAssert (∃ f, ⌜δ !! i = Some f⌝)%I with "[Htk He]" as "[% %LU]".
    { destruct (decide (i ∈ dom δ)).
      { by apply elem_of_dom in e. }
      { iExFalso. rewrite /sfS_fuel_bound. iCombine "Htk He" as "H". iPoseProof (own_valid with "H") as "V".
        rewrite /discrete_fun_singleton /discrete_fun_insert.
        iPoseProof (discrete_fun_validI with "V") as "%V". iPureIntro.
        specialize (V i). rewrite discrete_fun_lookup_op in V. destruct (decide (i ∈ dom δ)); [done|].
        destruct (decide (i = i)); [|done]. rewrite rew_const debt_add bank_valid_debt in V.
        destruct V as [_ V]. by eapply Qp.not_add_le_l.
      }
    }
    done.
  Qed.

  Lemma schedfairI_reserved_alloc_thread (S : thread_ids) (i : thread_id) a :
    (i ∉ S) →
    own state_name ((λ k : thread_id, if decide (k ∈ S) then ε else (debt a 1)) : discrete_fun _)
    ⊢ (own state_name ((λ k : thread_id, if decide (k ∈ {[i]} ∪ S) then ε else (debt a 1)) : discrete_fun _) ∗
       own state_name (discrete_fun_singleton i (debt a 1))).
  Proof.
    iIntros (LU) "Htk".
    assert (FORK : ((λ k : thread_id, if decide (k ∈ S) then ε else (debt a 1)) : discrete_fun _)
                     ≡
                     (((λ k : thread_id, if decide (k ∈ {[i]} ∪ S) then ε else (debt a 1)) : discrete_fun _)
                      ⋅ discrete_fun_singleton i (debt a 1))).
    { intros x. rewrite discrete_fun_lookup_op. destruct (decide (x ∈ S)).
      - destruct (decide (x ∈ {[i]} ∪ S)).
        + rewrite discrete_fun_lookup_singleton_ne; [by rewrite left_id | set_solver].
        + exfalso. set_solver.
      - destruct (decide (x = i)).
        + subst. destruct (decide (i ∈ {[i]} ∪ S)); [|exfalso; set_solver].
          by rewrite discrete_fun_lookup_singleton left_id.
        + destruct (decide (x ∈ {[i]} ∪ S)); [exfalso; set_solver |].
          rewrite discrete_fun_lookup_singleton_ne; [by rewrite right_id | done].
    }
    rewrite FORK own_op. iDestruct "Htk" as "[Htk Hi]". iFrame.
  Qed.

  Lemma schedfairI_alloc_thread δ i f :
    (δ !! i = None) →
    schedfairI δ
    ⊢ |==> schedfairI (<[i:=f]>δ) ∗ ∃ fb, sfS_fuel_bound i fb 1.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "(% & Htk & Hs)".
    pose proof LU as LU'. apply not_elem_of_dom in LU.
    iDestruct (schedfairI_reserved_alloc_thread _ _ _ LU with "Htk") as "[Htk Hfb]".
    iMod (sfS_fuel_owe i _ f with "Hfb") as "[Hfb Hfc]".
    iModIntro. iFrame.
    (* iSplit; [|iPureIntro; apply OCM.add_base_right_le]. *)
    iExists a. iSplitL "Htk".
    - rewrite dom_insert_L. done.
    - iApply big_sepM_insert; [auto|]. iFrame. done.
  Qed.

  Lemma schedfairI_alloc_threads δ1 δ2 δ' :
    (δ2 = δ1 ∪ δ') → (dom δ1 ## dom δ') →
    schedfairI δ1
    ⊢ |==> schedfairI δ2 ∗ [∗ set] i ∈ dom δ', ∃ fb, sfS_fuel_bound i fb 1.
  Proof.
    revert δ1 δ2. pattern δ'. revert δ'. apply map_ind.
    { iIntros. rewrite right_id in H. subst. iFrame. rewrite dom_empty_L. iModIntro. done. }
    iIntros (i f δ LUd IH δ1 δ2 Hdu Hdd) "SF". iMod (IH δ1 (delete i δ2) with "SF") as "[SF Hbs]".
    { subst. replace (δ1 ∪ <[i:=f]> δ) with (<[i:=f]>(δ1 ∪ δ)).
      - rewrite delete_insert; auto. rewrite lookup_union_l; auto. apply not_elem_of_dom_1. set_solver.
      - rewrite insert_union_r; auto. apply not_elem_of_dom_1. set_solver.
    }
    { set_solver. }
    iMod (schedfairI_alloc_thread _ i f with "SF") as "[SF Hb]".
    { apply lookup_delete. }
    pose proof (not_elem_of_dom_2 _ _ LUd) as NINd.
    rewrite dom_insert_L big_sepS_union; [|set_solver].
    rewrite big_sepS_singleton. iFrame. rewrite insert_delete; first by iFrame.
    subst. rewrite -insert_union_r; first by rewrite lookup_insert. apply not_elem_of_dom_1. set_solver.
  Qed.

  Lemma schedfairI_decr_one δ i f f' :
    (δ !! i = Some f) →
    (f' /< f) →
    schedfairI δ
    ⊢ |==> schedfairI (<[i:=f']>δ) ∗ ∃ c, ⌜/0 /< c⌝ ∗ sfS_fuel_credit i c.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU Hf) "(%&Htk&Hs)".
    rewrite (dom_insert_lookup_L δ i f'); [iFrame | done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hfc)".
    assert (∃ f1, (/0 /< f1) ∧ (f' /+ f1) /≤ f'0).
    { apply WFOCM.lt_exists_left in Hf. destruct Hf as (?&?&?). exists x. split; [auto | etransitivity; eauto]. }
    destruct H0 as (f1&Hpos&Hf1). 
    iMod (sfS_fuel_credit_mon_add _ _ _ _ Hf1 with "Hfc") as "[Hfc1 Hfc2]".
    iPoseProof (big_sepM_insert _ (delete i δ) i f' with "[Hs Hfc1]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame. done.
  Qed.

  Lemma schedfairI_decr_set δ1 δ2 :
    map_Forall2 (λ _ f1 f2, (f2 /< f1)) δ1 δ2 →
    schedfairI δ1
    ⊢ |==> schedfairI δ2 ∗ [∗ set] i ∈ dom δ1, ∃ c, ⌜/0 /< c⌝ ∗ sfS_fuel_credit i c.
  Proof.
    rewrite /schedfairI -!lock. iIntros (Hmf2) "(%&Ho&HM)".
    pose proof (map_Forall2_dom_L _ _ _ Hmf2) as Hd. rewrite <- Hd. iFrame.
    rewrite Hd -big_opM_dom -big_sepM_sep. iApply big_sepM_bupd.
    iPoseProof (big_sepM_impl_strong _ _ δ1 δ2 with "HM []") as "[HM _]"; [|iApply "HM"].
    iModIntro. clear a. iIntros (k f2) "Hc %Hd2". pose proof (map_Forall2_lookup_r _ _ _ Hmf2 _ _ Hd2).
    destruct H as (f1&Hd1&Hf). rewrite Hd1. iDestruct "Hc" as "(%&%&Hc)".
    assert (∃ f0, (/0 /< f0) ∧ (f2 /+ f0) /≤ f').
    { apply WFOCM.lt_exists_left in Hf. destruct Hf as (?&?&?). exists x. split; [auto | etransitivity; done]. }
    destruct H0 as (f0&Hpos&Hf0). 
    iMod (sfS_fuel_credit_mon_add _ _ _ _ Hf0 with "Hc") as "[Hc1 Hc2]".
    iModIntro. iSplitL "Hc1".
    - iExists f2. by iFrame.
    - iExists f0. by iFrame.
  Qed.

  Lemma schedfairI_reset_one δ i f f0 f' c :
    (δ !! i = Some f) →
    schedfairI δ ∗ sfS_fuel_bound i f0 1
    ⊢ |==> schedfairI (<[i:=f']>δ) ∗ sfS_fuel_bound i (f0 /+ (f' /+ c)) 1 ∗ sfS_fuel_credit i c.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "[(%&Htk&Hs) Hfb]".
    rewrite dom_insert_lookup_L; [iFrame|done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&_)".
    iMod (sfS_fuel_owe i _ (f' /+ c) with "Hfb") as "[Hfb Hfc]".
    iPoseProof (sfS_fuel_credit_add with "Hfc") as "[Hf Hc]". iFrame.
    iPoseProof (big_sepM_insert _ (delete i δ) i f' with "[Hs Hf]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame.
  Qed.

  Lemma schedfairI_credit_of_reserved δ c :
    schedfairI δ
    ⊢ |==> schedfairI δ ∗
           (own state_name ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (cash c)) : discrete_fun _)).
  Proof.
    rewrite /schedfairI -!lock. iIntros "(%&Htk&Hs)".
    iMod (own_update with "Htk") as "Htk".
    { apply (discrete_fun_update _ (λ k, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1 ⋅ cash c))).
      intros. destruct (decide (a0 ∈ dom δ)); [done|]. apply debt_owe.
    }
    assert (ADD : ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1 ⋅ cash c)) : discrete_fun _)
                    ≡
                    (((λ k : thread_id, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1)) : discrete_fun _)
                     ⋅ ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (cash c)) : discrete_fun _))).
    { intros x. rewrite discrete_fun_lookup_op. destruct (decide (x ∈ dom δ)); [by rewrite left_id|done]. }
    rewrite ADD. clear ADD. iDestruct "Htk" as "[Htk Hc]". iModIntro. iFrame.
  Qed.

  Lemma schedfairI_credit_from_all δ1 δ2 (S : thread_ids) c :
    map_Forall2 (λ i f1 f2, if decide (i ∈ S) then True else (f2 /< f1)) δ1 δ2 →
    schedfairI δ1 ∗ ([∗ set] i ∈ dom δ1, if decide (i ∈ S) then ∃ f, sfS_fuel_bound i f 1 else True)
    ⊢ |==> schedfairI δ2 ∗ ([∗ set] i ∈ dom δ2, if decide (i ∈ S) then ∃ f, sfS_fuel_bound i f 1 else True) ∗
           (own state_name ((λ k : thread_id, if decide (k ∈ dom δ1) then ε else (cash c)) : discrete_fun _)) ∗
           ([∗ set] i ∈ dom δ1, if decide (i ∈ S) then sfS_fuel_credit i c else ∃ c, ⌜ /0 /< c ⌝ ∗ sfS_fuel_credit i c).
  Proof.
    iIntros (Hmf2) "[Hsi HS]". iMod (schedfairI_credit_of_reserved with "Hsi") as "[Hsi Hcr]". iFrame "Hcr".
    rewrite /schedfairI -!lock. iDestruct "Hsi" as "(%&Ho&HM)".
    pose proof (map_Forall2_dom_L _ _ _ Hmf2) as Hd. rewrite <- Hd. iFrame "Ho".
    iPoseProof (big_opM_dom with "HS") as "HS". iCombine "HM HS" as "H".
    rewrite -big_sepS_sep Hd -!big_opM_dom -!big_sepM_sep. iApply big_sepM_bupd.
    iPoseProof (big_sepM_impl_strong _ _ δ1 δ2 with "H []") as "[H _]"; [|iApply "H"].
    iModIntro. clear a. iIntros (k f2) "Hc %Hd2". pose proof (map_Forall2_lookup_r _ _ _ Hmf2 _ _ Hd2).
    destruct H as (f1&Hd1&Hf). rewrite Hd1. iDestruct "Hc" as "[(%&%&Hc) Hs]".
    destruct (decide (k ∈ S)).
    - iDestruct "Hs" as "[% Hfb]". iMod (sfS_fuel_owe k _ (f2 /+ c) with "Hfb") as "[Hfb Hfc]".
      iClear "Hc". iPoseProof (sfS_fuel_credit_add with "Hfc") as "[Hf Hc]".
      iModIntro. iSplitL "Hf"; [|iFrame]. iExists f2. by iFrame.
    - iClear "Hs". assert (∃ f0, (/0 /< f0) ∧ (f2 /+ f0) /≤ f').
      { apply WFOCM.lt_exists_left in Hf. destruct Hf as (?&?&?). exists x. split; [auto | etransitivity; done]. }
      destruct H0 as (f0&Hpos&Hf0). 
      iMod (sfS_fuel_credit_mon_add _ _ _ _ Hf0 with "Hc") as "[Hc1 Hc2]".
      iModIntro. iSplitL "Hc1".
      + iExists f2. by iFrame.
      + iSplit; first done. iExists f0. by iFrame.
  Qed.

  Lemma sfS_fuel_credit_forall_get (δ : gmap thread_id A) (S : thread_ids) c :
    (/0 /< c) →
    (own state_name ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (cash c)) : discrete_fun _)) ∗
    ([∗ set] i ∈ dom δ, if decide (i ∈ S) then sfS_fuel_credit i c else ∃ c, ⌜/0 /< c⌝ ∗ sfS_fuel_credit i c)
    ⊢ sfS_fuel_credit_forall.
  Proof.
    rewrite /sfS_fuel_credit_forall. iIntros (LT) "(H1 & H2) %i". destruct (decide (i ∈ dom δ)).
    - iPoseProof (big_sepS_elem_of_acc _ _ _ e with "H2") as "[Hc H2]". destruct (decide (i ∈ S)).
      + iExists c. by iFrame.
      + done.
    - iExists c. iSplit; first done. iClear "H2". rewrite /sfS_fuel_credit. iStopProof. apply own_mono.
      assert (((λ k : thread_id, if decide (k ∈ dom δ) then ε else cash c) : discrete_fun _)
                ≡
                discrete_fun_singleton i (cash c)
              ⋅ ((λ k : thread_id, if decide (k ∈ dom δ) then ε else if decide (k = i) then ε else cash c) : discrete_fun _)).
      { rewrite /discrete_fun_singleton /discrete_fun_insert.
        intros k. rewrite discrete_fun_lookup_op. destruct (decide (k ∈ dom δ)).
        - destruct (decide (i = k)); [subst; set_solver|]. rewrite right_id. done.
        - destruct (decide (i = k)).
          + subst. simpl. destruct (decide (k = k)); [|done]. by rewrite right_id.
          + destruct (decide (k = i)); [done|]. by rewrite left_id.
      }
      rewrite H. apply cmra_included_l.
  Qed.

  Lemma sfS_fuel_pay_forall i a0 q :
    sfS_fuel_bound i a0 q ∗ sfS_fuel_credit_forall ⊢ |==> ∃ a1, ⌜ a1 /< a0 ⌝ ∗ sfS_fuel_bound i a1 q.
  Proof.
    iIntros "[Hb Hcf]". rewrite /sfS_fuel_credit_forall. iSpecialize ("Hcf" $! i).
    iDestruct "Hcf" as "(%&%&Hc)". iMod (sfS_fuel_pay with "[Hb Hc]") as "(%&%&Hb)"; first iFrame.
    iFrame. iPureIntro. apply WFOCM.lt_exists_right. exists c. done.
  Qed.

End sfi.

(* Allocation of an initial obligation protocol. *)
Lemma schedfairI_alloc `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} `{!schedfairGpreS Σ} : ⊢ |==> ∃ _ : schedfairGS Σ, schedfairI ∅.
Proof.
  iIntros.
  iMod (own_alloc ((λ k, if (decide (k ∈ dom (∅ : gmap thread_id (option A)))) then ε else (debt OCM.unit 1)) : discrete_fun _)) as (γS) "HS".
  { intros x. destruct (decide (x ∈ dom ∅)).
    - apply ucmra_unit_valid.
    - by apply bank_valid_debt.
  }
  iModIntro; iExists (SchedfairG SI _ _ _ _ WF _ _ γS).
  rewrite /schedfairI -lock.
  iExists OCM.unit. rewrite big_opM_empty. by iFrame.
Qed.
