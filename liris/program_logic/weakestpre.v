From iris.proofmode Require Import base proofmode classes.
From liris Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From liris.base_logic Require Export fancy_updates.
From liris.program_logic Require Export gupd.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.
Import uPred.

Section curry5.
  Definition curry5 {A B C D E F : Type} (f : A * B * C * D * E → F) (a : A) (b : B) (c : C) (d : D) (e : E) : F :=
    f (a, b, c, d, e).
  Definition uncurry5 {A B C D E F : Type} (f : A → B → C → D → E → F) : (A * B * C * D * E) → F :=
    λ '(a, b, c, d, e), f a b c d e.

  Lemma curry5_uncurry5 : ∀ {A B C D E F : Type} (f : A → B → C → D → E → F), curry5 (uncurry5 f) = f.
  Proof. done. Qed.
  Lemma uncurry5_curry5 : ∀ {A B C D E F : Type} (f : A * B * C * D * E → F) (p : A * B * C * D * E), uncurry5 (curry5 f) p = f p.
  Proof. intros. destruct p as [[[[a b] c] d] e]. done. Qed.

  Global Instance uncurry5_proper' : ∀ {A : Type} {RA : relation A} {B : Type} {RB : relation B} {C : Type} {RC : relation C} {D : Type} {RD : relation D} {E : Type} {RE : relation E} {F : Type} {RF : relation F},
    Proper
      ((RA ==> RB ==> RC ==> RD ==> RE ==> RF) ==>
         prod_relation (prod_relation (prod_relation (prod_relation RA RB) RC) RD) RE ==> RF)
      (@uncurry5 A B C D E F).
  Proof.
    intros. repeat intro.
    destruct x0 as [[[[a0 b0] c0] d0] e0], y0 as [[[[a1 b1] c1] d1] e1].
    simpl. destruct H0 as [[[[? ?] ?] ?] ?]. simpl in *. by eapply H.
  Qed.
  Global Instance uncurry5_proper : ∀ {A : Type} {H : Equiv A} {B : Type} {H0 : Equiv B} {C : Type} {H1 : Equiv C} {D : Type} {H2 : Equiv D} {E : Type} {H3 : Equiv E} {F : Type} {H4 : Equiv F},
    Proper ((equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) ==> equiv ==> equiv) (@uncurry5 A B C D E F).
  Proof. intros. eapply uncurry5_proper'. Qed.

  Global Instance uncurry5_ne : ∀ {SI : indexT} {A B C D E F : ofe} (n : index),
    Proper ((dist n ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n) (@uncurry5 A B C D E F).
  Proof. intros. apply uncurry5_proper. Qed.
End curry5.

Class lirisGS `{SI : indexT} (Λ : language) (Σ : gFunctors) := LirisG {
  (** Ghost lock protocol including invariants. *)
  #[global] liris_gupdGS :: gupdGS Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction.
  Here [state] is the global state, [thread_ids] is the allocated thread ids,
  and [list (observation Λ)] are the remaining observations. *)
  state_interp : state Λ → thread_ids → list (observation Λ) → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : thread_id → val Λ → iProp Σ;
}.

Global Opaque liris_gupdGS.
Global Arguments LirisG {SI Λ Σ}.

(* Ensure progress of thread i's obligations and every live witnesses. *)
Definition gprog `{SI : indexT} `{!lirisGS Λ Σ} Θ1 Θ2 i : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ (Ω1 : ghost_locks) (W1 : witnesses),
     (gproto Ω1 W1 Θ1) ={∅}=∗
     ∃ Ω2, (⌜(Ω1 ↪ₚ Ω2 | gl_cond_owner i)⌝) ∗
     ∀ W2, (⌜(W1 ↓ₚ W2 | wit_cond_locked) ∧ glwit_inv Ω2 W2 ⌝) ={∅}=∗
     (gproto Ω2 W2 Θ2) ∗ P)%I.

Notation "'@={' Θ1 , Θ2 , i '}=↓' P" := (gprog Θ1 Θ2 i P) (at level 99, P at level 200, format "@={ Θ1 , Θ2 , i }=↓  P").

Section gprog.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  Global Instance gprog_ne Θ1 Θ2 i :
    NonExpansive (gprog Θ1 Θ2 i).
  Proof.
    intros n P1 P2 HP. rewrite /gprog. do 15 (f_equiv || done).
  Qed.
  Global Instance gprog_proper Θ1 Θ2 i :
    Proper ((≡) ==> (≡)) (gprog Θ1 Θ2 i).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply gprog_ne. apply equiv_dist. done.
  Qed.

  Lemma gprog_mono Θ1 Θ2 i P Q : (P ⊢ Q) → (@={Θ1,Θ2,i}=↓ P) ⊢ (@={Θ1,Θ2,i}=↓ Q).
  Proof.
    intros Hent. rewrite /gprog. iIntros "P % % I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply Hent.
  Qed.
  Lemma gprog_wand_l Θ1 Θ2 i P Q : (P -∗ Q) ∗ (@={Θ1,Θ2,i}=↓ P) ⊢ (@={Θ1,Θ2,i}=↓ Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /gprog. iIntros "% % I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply "PQ".
  Qed.

  Global Instance gprog_ent_proper Θ1 Θ2 i : Proper ((⊢) ==> (⊢)) (gprog Θ1 Θ2 i).
  Proof. intros P Q PQ. by apply gprog_mono. Qed.
  Global Instance gprog_flip_ent_proper Θ1 Θ2 i : Proper (flip (⊢) ==> flip (⊢)) (gprog Θ1 Θ2 i).
  Proof. intros P Q PQ; by apply gprog_mono. Qed.
  Global Instance gprog_equiv_proper Θ1 Θ2 i : Proper ((≡) ==> (≡)) (gprog Θ1 Θ2 i) := ne_proper _.

  Global Instance elim_gprog (p : bool) Θ1 Θ2 i P Q :
    ElimModal True p false (@={Θ1,Θ2,i}=↓ P) P (@={Θ1,Θ2,i}=↓ Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (gprog_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_gprog Θ1 Θ2 i P : (|={∅}=> @={Θ1,Θ2,i}=↓ P) ⊢ @={Θ1,Θ2,i}=↓ P.
  Proof.
    rewrite /gprog. iIntros "H % % IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_gprog (p : bool) Θ1 Θ2 i P Q :
    ElimModal True p false (|={∅}=> P) P (@={Θ1,Θ2,i}=↓ Q) (@={Θ1,Θ2,i}=↓ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_gprog. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

  Local Ltac unfold_defs :=
    try rewrite !gupd.wit_fuels_unseal /gupd.wit_fuels_def;
    try rewrite !gupd.wit_unseal /gupd.wit_def;
    try rewrite !gupd.wit_layer_unseal /gupd.wit_layer_def;
    try rewrite !gupd.wit_bound_unseal /gupd.wit_bound_def;
    try rewrite !gupd.th_term_unseal /gupd.th_term_def;
    try rewrite !gupd.th_obls_unseal /gupd.th_obls_def;
    try rewrite !gupd.gl_variant_cases_unseal /gupd.gl_variant_cases_def;
    try rewrite !gupd.gl_variant_unseal /gupd.gl_variant_def;
    try rewrite !gupd.gl_fuel_unseal /gupd.gl_fuel_def;
    try rewrite !gupd.gl_fuel_val_unseal /gupd.gl_fuel_val_def;
    try rewrite !gupd.gl_expired_unseal /gupd.gl_expired_def;
    try rewrite !gupd.gl_current_unseal /gupd.gl_current_def;
    try rewrite !gupd.gl_done_unseal /gupd.gl_done_def;
    try rewrite !gupd.gl_locked_unseal /gupd.gl_locked_def;
    try rewrite !gupd.gl_layer_unseal /gupd.gl_layer_def;
    try rewrite !gupd.gl_unseal /gupd.gl_def.

  (** Step rule *)
  Lemma gprog_step Θ π i P :
    Θ ## π →
    (|={∅}=> ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0ₗ%L 1) ∗
                 ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
                      ((th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) ∗ ([∗ set] j ∈ π, th_obls j ∅ 1))
                       ={∅}=∗ P))
    ⊢ @={Θ,(Θ ∪ π),i}=↓ P.
  Proof.
    unfold_defs. iIntros (DisjTP) "H". iMod "H" as "(%& (#Oe& Ox& Ob& OS)& GFs& %& #REs& H)".
    iAssert ([∗ map] g↦_ ∈ G, glG_elem g ∗ glG_fuel g Ord.one)%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!> %%% H". rewrite (glG_fuel_eq _ (measure 0ₗ%L 1) Ord.one); auto.
      rewrite measure_finite Ord.from_nat_1. done. }
    iIntros "% % (S& O& A& W& %GWI1)".
    iAssert (⌜ dom G ⊆ dom Ω1 ⌝)%I as "%GOSub".
    { rewrite elem_of_subseteq. iIntros (x INGx).
      apply elem_of_dom in INGx. destruct INGx as (?& INGx).
      iPoseProof (big_sepM_delete _ _ _ _ INGx with "GFs") as "[(#Bex& _) _]".
      iApply (glsat_elem with "[$S $Bex]").
    }
    iAssert ([∗ map] k ↦ _ ∈ Ω1, (⌜ k ∈ dom G ⌝ ∗ glG_fuel k Ord.one) ∨ (⌜ k ∉ dom G ⌝))%I with "[GFs]" as "GFs".
    { rewrite !big_sepM_dom. replace (dom Ω1) with ((dom G) ∪ (dom Ω1 ∖ (dom G))).
      2:{ rewrite -union_difference_L; auto. }
      iApply (big_sepS_union). 1: set_solver.
      iSplitL.
      - iApply (big_sepS_impl with "GFs"). iIntros "!>" (??) "(_& Bfx)". iLeft. iFrame. done.
      - iApply big_sepS_intro. iIntros "!>" (??). iRight. iPureIntro. set_solver + H.
    }
    iAssert (∀ g, ⌜ g ∈ dom G ⌝ → ∃ o, ⌜ Ω1 !! g = Some o ∧ gl_cond_owner i g o ⌝)%I as "%LUG".
    { iIntros (g INGg). pose proof INGg. apply elem_of_dom in H. destruct H as (?& LUGg).
      iPoseProof (big_sepM_delete _ _ _ _ LUGg with "OS") as "[(#Ge& Gl& Gv& Go& Oo) _]".
      iPoseProof (globl_obls_lookup _ _ g _ _ _ INGg with "[$S $O $Oe $Ob $Ge]") as "(%& %& %)".
      iExists _. iPureIntro. done.
    }
    iAssert (∀ k, ⌜ k ∈ dom Ω1 ⌝ → ⌜ k ∉ dom G ⌝ → ∃ o, ⌜ Ω1 !! k = Some o ∧ ¬ gl_cond_owner i k o ⌝)%I as "%NotG".
    { iIntros (k INOk NINGk). apply elem_of_dom in INOk. destruct INOk.
      destruct (decide (gl_cond_owner i k x)); eauto.
      iExFalso. destruct x. destruct g1; last done. simpl in *. subst.
      iPoseProof (globl_assigned_obls_lookup _ _ k with "[$S $O $A $Ob]") as "%".
      { apply H. }
      done.
    }
    iAssert ([∗ map] k ↦ o ∈ Ω1, (⌜ gl_cond_owner i k o ⌝ ∗ (∃ c, ⌜ WFOCM.ltR OCM.unit c ⌝ ∗ glG_fuel k c)) ∨ (⌜ ¬ gl_cond_owner i k o ⌝))%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!>" (???) "[(%& Bfk) | %]".
      - iLeft. iFrame "Bfk". iPureIntro; split.
        + apply LUG in H0. destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply Ord.S_pos.
      - iRight. iPureIntro. apply NotG in H0.
        + destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply elem_of_dom; eauto.
    }
    assert (DomOW : dom Ω1 = dom W1) by (eapply glwit_inv_dom; eauto).
    iAssert (⌜ dom R ⊆ dom W1 ⌝)%I as "%RWSub".
    { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
      pose proof INRx. apply elem_of_dom in H. destruct H.
      iPoseProof (big_sepM_delete _ _ _ _ H with "REs") as "[[#Beg _] _]".
      iPoseProof (glsat_elem with "[$S $Beg]") as "%". done.
    }
    iMod (glsat_progress with "[$S $GFs]") as "(%Ω2& S& %ProgO)".
    { intros. destruct g. destruct g0; eauto. done. }
    iModIntro. iExists Ω2. iSplitR; first done. iIntros (W2 (ProgW& GWI2)).
    iMod (glwit_progress with "W") as "[W Ws]". 1: eauto.
    assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ dom R = dom WR).
    { clear GWI1 DomOW ProgW.
      revert R RWSub. induction W1 using map_ind; intros.
      { assert (dom R = ∅) by (set_solver). apply dom_empty_inv_L in H. subst. exists ∅, ∅. done. }
      rename i0 into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ dom R)).
      - set (R2 := delete r R). assert (dom R2 ⊆ dom m).
        { subst R2. rewrite dom_delete_L. set_solver + RWSub. }
        apply elem_of_dom in e. destruct e. rename H1 into LUR.
        destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
        exists (<[r:=x]>WR), WR'. subst R2.
        assert (WR !! r = None ∧ WR' !! r = None).
        { apply lookup_union_None. rewrite -H2; auto. }
        destruct H4. split_and !.
        + apply map_disjoint_insert_l. split; auto.
        + subst. rewrite insert_union_l. done.
        + replace R with (<[r:=x0]> (delete r R)).
          * rewrite !dom_insert_L H3. auto.
          * rewrite insert_delete_id; auto.
      - assert (dom R ⊆ dom m).
        { set_solver + RWSub n. }
        pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
        assert (WR !! r = None ∧ WR' !! r = None).
        { apply lookup_union_None. rewrite -H2; auto. }
        destruct H4. exists WR, (<[r:=x]>WR'). split_and !; auto.
        + apply map_disjoint_insert_r. split; auto.
        + subst. rewrite insert_union_r; done.
    }
    destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
    assert (DomO : fst <$> Ω1 = fst <$> Ω2).
    { destruct ProgO. apply map_eq. intros j. rewrite !lookup_fmap. specialize (H0 j).
      destruct (Ω1 !! j) eqn:LUO1.
      - inv H0. destruct g, y. inv H3. rewrite LUO1 -H2. done.
      - inv H0. rewrite LUO1 -H1. done.
    }
    assert (EQfst : fst <$> Ω2 = fst <$> W1).
    { rewrite -DomO. apply map_eq. intros j. destruct ProgO.
      specialize (GWI1 j). rewrite !lookup_fmap. destruct (W1 !! j) eqn:LUW1.
      - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. destruct x. destruct w. destruct H3. by subst.
      - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. done.
    }
    iAssert (⌜ ∀ k v, R !! k = Some v → ∃ w, WR !! k = Some w ∧ v ≤ w.1 ⌝)%I as "%Rver".
    { iIntros (k v LUR). iPoseProof (big_sepM_delete _ _ _ _ LUR with "REs") as "[(#Ge& #Gvl& #His) _]".
      iPoseProof (glsat_lookup_version_lb with "[$S $Ge $Gvl]")as "(%&%&%&%)".
      rewrite map_eq_iff in EQfst. specialize (EQfst k). rewrite !lookup_fmap H in EQfst.
      assert (is_Some (WR !! k)).
      { apply elem_of_dom. rewrite -DomWR. apply elem_of_dom; eauto. }
      destruct H1 as (?& LUWRk).
      assert (WR' !! k = None).
      { eapply map_disjoint_Some_l; eauto.  }
      destruct (W1 !! k) eqn:LUW1.
      - rewrite LUW1 in EQfst. inv EQfst. apply lookup_union_Some_inv_l in LUW1; eauto.
      - rewrite LUW1 in EQfst. inv EQfst.
    }
    iAssert (|==> [∗ map] r↦v ∈ R, (witG_witness r v Ord.one) ∨ (glG_unlocked r v))%I with "[Ws]" as ">Rs".
    { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto.
      iApply big_sepM_bupd. iClear "Oe REs". clear dependent WR'.
      iStopProof. revert R DomWR Rver. induction WR using map_ind; iIntros (R DomWR Rver) "M".
      { apply dom_empty_inv_L in DomWR. subst. done. }
      rename i0 into r. rewrite dom_insert_L in DomWR. destruct (R !! r) eqn:LUR; cycle 1.
      { exfalso. apply not_elem_of_dom in LUR. set_solver + DomWR LUR. }
      remember (delete r R) as R0.
      assert (dom R0 = dom m).
      { subst. rewrite dom_delete_L. apply not_elem_of_dom in H. rewrite DomWR. set_solver + H. }
      assert (R0 !! r = None).
      { subst. apply lookup_delete_eq. }
      assert (R = <[r:=g]>R0).
      { subst. rewrite insert_delete_id; auto. }
      rewrite H2.
      assert (∀ k v, R0 !! k = Some v → ∃ w, m !! k = Some w ∧ v ≤ w.1).
      { intros. specialize (Rver k v). subst. destruct (decide (k = r)).
        { subst. rewrite lookup_delete_eq in H3. inv H3. }
        rewrite lookup_delete_ne in H3; auto. apply Rver in H3. destruct H3 as (?&?&?).
        rewrite lookup_insert_ne in H3; eauto.
      }
      destruct (Rver _ _ LUR) as (w& LUmk& LEv). rewrite lookup_insert_eq in LUmk.
      clear dependent R. inv LUmk. rewrite !big_sepM_insert; auto.
      destruct w. iDestruct "M" as "[H M]". iPoseProof (IHWR _ H0 H3 with "M") as "$".
      iDestruct "H" as "(#H1& #H2& H)". simpl in LEv. destruct w.
      - assert (g = n ∨ g < n) by lia. destruct H2.
        + subst. iDestruct "H" as "(%& %& Wc)". apply ord_lt_one in H2.
          iLeft. iMod (witG_witness_mon_split with "Wc") as "[_ $]"; done.
        + assert (g ∈ (set_seq 0 n : gset _)).
          { apply elem_of_set_seq. lia. }
          iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
          iRight. auto.
      - assert (g = n ∨ g < n) by lia. destruct H2.
        + subst. iRight. auto.
        + assert (g ∈ (set_seq 0 n : gset _)).
          { apply elem_of_set_seq. lia. }
          iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
          iRight. auto.
    }
    iAssert ([∗ map] r↦v ∈ R,
               ((glG_elem r ∗ glG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ witG_witness r v Ord.one) ∨
                 ((glG_elem r ∗ glG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ glG_unlocked r v))%I
      with "[Rs]" as "Rs".
    { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
      iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl& #His)".
      - iLeft. iFrame. auto.
      - iRight. auto.
    }
    iMod (globl_alloc_threads π with "O") as "[O Efs]".
    { eauto. }
    iMod ("H" with "[$Ob $Ox $Oe $OS $Rs Efs]") as "H".
    { iApply (big_sepS_impl with "Efs"). iIntros "!> %% ($& $& $)". done. }
    iModIntro. rewrite DomO /gproto. iFrame. done.
  Qed.

End gprog.

(** Predicates we take the fixpoint of in order to define the lWP. *)
(* Ω must make strict progress for every step (to bound step-index) *)
(* W witnesses progress of obligations; it exploits fair scheduler in the adequacy proof *)
Definition lwp_step `{SI : indexT} `{!lirisGS Λ Σ}
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ Θ σ1 κ κs,
      (state_interp σ1 Θ (κ ++ κs)) ={E,∅}=∗
      |=[Θ]=>g
      (⌜if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
      ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
      @={Θ,(Θ ∪ dom efs),i}=↓
      ALC (|=[(Θ ∪ dom efs)]=>g
           |={∅,E}=> (state_interp σ2 (Θ ∪ dom efs) κs) ∗ ν e2 efs))%I.

Section lwp_step.

  Global Instance lwp_step_ne `{SI : indexT} `{!lirisGS Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step.
    do 30 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper `{SI : indexT} `{!lirisGS Λ Σ} s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono `{SI : indexT} `{!lirisGS Λ Σ} s
    (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp". iModIntro. iMod "Hwp" as "($& Hwp)".
    iModIntro.
    iIntros (???) "H0".
    iDestruct ("Hwp" with "[$]") as ">>>Hwp".
    iModIntro. iMod "Hwp" as "Hwp".
    iModIntro. iDestruct "Hwp" as "[$ H]".
    by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step `{SI : indexT} `{!lirisGS Λ Σ} s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step.
    iMod "Hf" as "Hf". done.
  Qed.

End lwp_step.

(* Wrapper. *)
Definition sfgupd `{SI : indexT} `{!lirisGS Λ Σ} E : iPropO Σ -d> iPropO Σ :=
  (λ P, ∀ σ Θ κs, (state_interp σ Θ κs) -∗ |={E:Θ}=>g (state_interp σ Θ κs) ∗ P)%I.

Notation "'|={' E '}=>g' P" := (sfgupd E P) (at level 99, P at level 200, format "|={ E }=>g  P").

Section sfgupd.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  Global Instance sfgupd_ne E :
    NonExpansive (sfgupd E).
  Proof.
    intros n P1 P2 HP. rewrite /sfgupd. do 12 (f_equiv || done).
  Qed.
  Global Instance sfgupd_proper E :
    Proper ((≡) ==> (≡)) (sfgupd E).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply sfgupd_ne. apply equiv_dist. done.
  Qed.

  Lemma fupd_sfgupd E P : (|={E}=> P) ⊢ (|={E}=>g P).
  Proof.
    rewrite /sfgupd. iIntros ">Hupd %%% SI".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose !>". iMod "Hclose" as "_".
    iModIntro. iFrame.
  Qed.

  Lemma sfgupd_intro E P : P ⊢ |={E}=>g P.
  Proof.
    iIntros "$ %%% $". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_sfgupd_elim E P :
    (|={E}=> |={E}=>g P) ⊢ |={E}=>g P.
  Proof.
    iIntros "H". iIntros (???) "SI". iMod "H". iApply "H". done.
  Qed.

  (** Change to a larger mask. *)
  Lemma sfgupd_mask_mono E1 E2 P :
    E1 ⊆ E2 →
    (|={E1}=>g P) ⊢ |={E2}=>g P.
  Proof.
    iIntros (Sub) "H %%% SI".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod ("H" with "SI") as "H". iModIntro. iMod "H" as ">H".
    iMod "close" as "_".
    iMod (fupd_mask_subseteq ∅) as "close". 1: set_solver.
    iIntros "!> !>". iMod "close" as "_". by iApply "H".
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma sfgupd_bind E P Q :
    (P -∗ |={E}=>g Q) ⊢ (|={E}=>g P) -∗ (|={E}=>g Q).
  Proof.
    iIntros "H HP". iIntros "%%% SI".
    iMod ("HP" with "SI") as "[SI HP]".
    iPoseProof ("H" with "HP SI") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma sfgupd_mono E P Q : (P ⊢ Q) → (|={E}=>g P) ⊢ (|={E}=>g Q).
  Proof.
    intros Hent. iApply sfgupd_bind.
    iIntros "P"; iApply sfgupd_intro; by iApply Hent.
  Qed.
  Lemma sfgupd_trans E P :  (|={E}=>g |={E}=>g P) ⊢ |={E}=>g P.
  Proof.
    iIntros "HP". iApply sfgupd_bind; eauto.
  Qed.
  Lemma sfgupd_frame_r E P R : (|={E}=>g P) ∗ R ⊢ |={E}=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (sfgupd_bind with "[R]"); last done.
    iIntros "P". iApply sfgupd_intro. by iFrame.
  Qed.

  Global Instance sfgupd_ent_proper E : Proper ((⊢) ==> (⊢)) (sfgupd E).
  Proof. intros P Q PQ. by apply sfgupd_mono. Qed.
  Global Instance sfgupd_flip_ent_proper E : Proper (flip (⊢) ==> flip (⊢)) (sfgupd E).
  Proof. intros P Q PQ; by apply sfgupd_mono. Qed.
  Global Instance sfgupd_equiv_proper E : Proper ((≡) ==> (≡)) (sfgupd E) := ne_proper _.

  Lemma sfgupd_fupd_l E P :
    (|={E}=> |={E}=>g P) ⊢ (|={E}=>g P).
  Proof.
    by erewrite fupd_sfgupd, sfgupd_trans.
  Qed.
  Lemma sfgupd_fupd_r E P :
    (|={E}=>g |={E}=> P) ⊢ (|={E}=>g P).
  Proof.
    by erewrite fupd_sfgupd, sfgupd_trans.
  Qed.

  Lemma sfgupd_frame_l E R Q : (R ∗ |={E}=>g Q) ⊢ |={E}=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply sfgupd_frame_r. Qed.
  Lemma sfgupd_wand_l E P Q : (P -∗ Q) ∗ (|={E}=>g P) ⊢ |={E}=>g Q.
  Proof. by rewrite sfgupd_frame_l wand_elim_l. Qed.
  Lemma sfgupd_wand_r E P Q : (|={E}=>g P) ∗ (P -∗ Q) ⊢ |={E}=>g Q.
  Proof. by rewrite sfgupd_frame_r wand_elim_r. Qed.
  Lemma sfgupd_sep E P Q : (|={E}=>g P) ∗ (|={E}=>g Q) ⊢ |={E}=>g P ∗ Q.
  Proof. by rewrite sfgupd_frame_r sfgupd_frame_l sfgupd_trans. Qed.
  Lemma sfgupd_idemp E P : (|={E}=>g |={E}=>g P) ⊣⊢ |={E}=>g P.
  Proof.
    apply: anti_symm.
    - apply sfgupd_trans.
    - apply sfgupd_intro.
  Qed.

  Global Instance sfgupd_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (sfgupd E).
  Proof. split; [split|]; try apply _; [apply sfgupd_sep | apply sfgupd_intro]. Qed.

  Lemma big_sepL_sfgupd {A} (Φ : nat → A → iProp Σ) E l :
    ([∗ list] k↦x ∈ l, |={E}=>g Φ k x) ⊢ |={E}=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_sfgupd {A} `{Countable K} (Φ : K → A → iProp Σ) E l :
    ([∗ map] k↦x ∈ l, |={E}=>g Φ k x) ⊢ |={E}=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_sfgupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ set]  x ∈ l, |={E}=>g Φ x) ⊢ |={E}=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_sfgupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ mset] x ∈ l, |={E}=>g Φ x) ⊢ |={E}=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_sfgupd E P : ◇ (|={E}=>g P) ⊢ (|={E}=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using sfgupd_mono, or_intro_r.
    by rewrite -sfgupd_intro -or_intro_l.
  Qed.

  Lemma sfgupd_fupd_acc E1 E2 P :
    (|={E1,E2}=> |={E2}=>g |={E2,E1}=> P) ⊢ (|={E1}=>g P).
  Proof.
    iIntros "H %%% I". iMod "H". iPoseProof ("H" with "I") as "H".
    iMod "H". iModIntro. iMod "H". iModIntro. iMod "H" as "[$ H]".
    auto.
  Qed.

  (** Modality instances *)
  Global Instance elim_fupd_sfgupd (p : bool) E P Q :
    ElimModal True p false (|={E}=> P) P (|={E}=>g Q) (|={E}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_sfgupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_sfgupd E P Q :
    AddModal (|={E}=> P) P (|={E}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_sfgupd; iIntros "[HP HPQ]".
    iApply (sfgupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_sfgupd p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E}=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply sfgupd_intro. Qed.

  Global Instance from_pure_sfgupd a E P φ :
    FromPure a P φ → FromPure a (|={E}=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply sfgupd_intro. Qed.

  Global Instance into_wand_sfgupd p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E}=>g R) (|={E}=>g P) (|={E}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfgupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_sfgupd_persistent p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E}=>g R) P (|={E}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfgupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_sfgupd_args p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E}=>g P) (|={E}=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim sfgupd_wand_r.
  Qed.

  Global Instance from_sep_sfgupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=>g P) (|={E}=>g Q1) (|={E}=>g Q2).
  Proof. rewrite /FromSep=><-. apply sfgupd_sep. Qed.

  Global Instance from_or_sfgupd E P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E}=>g P) (|={E}=>g Q1) (|={E}=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply sfgupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_sfgupd {A} E P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E}=>g P) (λ a, |={E}=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_sfgupd E P : IsExcept0 P → IsExcept0 (|={E}=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_sfgupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_sfgupd E P :
    FromModal True modality_id (|={E}=>g P) (|={E}=>g P) P.
  Proof. by rewrite /FromModal /= -sfgupd_intro. Qed.

  Global Instance elim_modal_sfgupd p E P Q :
    ElimModal True p false (|={E}=>g P) P (|={E}=>g Q) (|={E}=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim sfgupd_frame_r wand_elim_r sfgupd_trans.
  Qed.

  Global Instance add_modal_sfgupd E P Q : AddModal (|={E}=>g P) P (|={E}=>g Q).
  Proof. by rewrite /AddModal sfgupd_frame_r wand_elim_r sfgupd_trans. Qed.

  Global Instance frame_sfgupd p E R P Q :
    Frame p R P Q → Frame p R (|={E}=>g P) (|={E}=>g Q).
  Proof. rewrite /Frame=><-. by rewrite sfgupd_frame_l. Qed.

  (** Update rules *)
  Lemma gl_alloc_obl E i G q ℓ μ N v P Q R :
    th_obls i G q -∗
    (▷ P) -∗
    |={E}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                 th_obls i (<[k:=v]>G) q ∗
                 gl_layer k ℓ ∗ gl k v ∗ gl_fuel k ℓ μ ∗
                 gl_variant N k v P Q R ∗
                 wit_layer k v ℓ ∗
                 ([∗ set] u ∈ set_seq 0 v, gl_done k u).
  Proof.
    iIntros "Tb HP %%% $". iApply (gl_alloc_obl_0 _ Θ with "Tb HP").
  Qed.

  Lemma gl_alloc_done E ℓ μ N v P Q R :
    (▷ Q) -∗
    |={E}=>g ∃ k, gl_layer k ℓ ∗ gl k v ∗ gl_current k v ∗ gl_done k v ∗ gl_fuel k ℓ μ ∗
                 gl_variant N k v P Q R ∗
                 wit_layer k v ℓ ∗
                 ([∗ set] u ∈ set_seq 0 (S v), gl_done k u).
  Proof.
    iIntros "HQ %%% $". iApply (gl_alloc_done_0 _ Θ with "HQ").
  Qed.

  Lemma gl_lock E0 E i G q k ℓ μ N v1 v2 (P1 Q1 R1 P2 Q2 R2 : iProp Σ) :
    v1 < v2 →
    ↑N ⊆ E →
    gl_current k v1 -∗
    gl_done k v1 -∗
    gl_variant N k v1 P1 Q1 R1 -∗
    |={E,E ∖ ↑N}=> (▷ (gl_current k v1 ∗ Q1)) ∗
                  (th_obls i G q -∗
                   gl_current k v1 -∗
                   gl_layer k ℓ -∗
                   (▷ R1) -∗
                   (▷ P2) -∗
                   |={E0}=>g |={E ∖ ↑N,E}=> 
                     (th_obls i (<[k:=v2]>G) q ∗
                      gl k v2 ∗ gl_fuel k ℓ μ ∗
                      gl_variant N k v2 P2 Q2 R2 ∗
                      wit_layer k v2 ℓ ∗
                      ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit_layer k u ℓ) ∗
                      ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u))).
  Proof.
    iIntros (Hv Mask) "Gc Gd Gv". iMod (gl_lock_0 with "Gc Gd Gv") as "[$ H]". 1,2: eauto.
    iIntros "!> Tb Gc Gw HR HP". iPoseProof ("H" with "Tb Gc Gw HR HP") as "H".
    iIntros "%%% $". iMod ("H" $! Θ) as "H". iModIntro. eauto.
  Qed.

  Lemma gl_unlock E0 E i G q N k v P Q R :
    ↑N ⊆ E →
    G !! k = Some v →
    th_obls i G q -∗
    gl_variant N k v P Q R -∗
    |={E,E ∖ ↑N}=> (▷ (th_obls i G q ∗ gl_locked k v ∗ P)) ∗
                  (th_obls i G q -∗
                   gl_locked k v -∗
                   (▷ Q) -∗
                   |={E0}=>g |={E ∖ ↑N,E}=>
                     (th_obls i (delete k G) q ∗ gl_current k v ∗ gl_done k v)).
  Proof.
    iIntros (Mask LUGk) "Tb Gv". iMod (gl_unlock_0 with "Tb Gv") as "[$ H]". 1,2: eauto.
    iIntros "!> Tb Gl HQ". iPoseProof ("H" with "Tb Gl HQ") as "H".
    iIntros "%%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
  Qed.

  Lemma gl_change_owner E i1 i2 G1 G2 q1 q2 k v ℓ0 :
    G1 !! k = Some v →
    th_obls i1 G1 q1 -∗
    th_obls i2 G2 q2 -∗
    gl_fuel k ℓ0 1 -∗
    |={E}=>g th_obls i1 (delete k G1) q1 ∗ th_obls i2 (<[k:=v]>G2) q2 ∗ ⌜ G2 !! k = None ⌝.
  Proof.
    iIntros (LUG1) "Tb1 Tb2 Gf %%% $".
    iMod (gl_change_owner_0 with "Tb1 Tb2 Gf") as "H". 1: eauto.
    by iModIntro.
  Qed.

  Lemma gl_terminate E i :
    th_obls i ∅ 1 -∗ |={E}=>g th_term i.
  Proof.
    iIntros "Tb %%% $". iMod (gl_terminate_0 with "Tb") as "#Tt". auto.
  Qed.

  Lemma gl_check_witnesses E R :
    ([∗ map] r ↦ v ∈ R, gl r v) -∗
    |={E}=>g ([∗ map] r ↦ v ∈ R, wit r v Ord.O ∨ gl_done r v).
  Proof.
    iIntros "Rs %%% $". iMod (gl_check_witnesses_0 with "Rs") as "H". auto.
  Qed.

End sfgupd.

Definition lift_term `{SI : indexT} `{!lirisGS Λ Σ} (i :thread_id) (Φ : thread_id → val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (th_term i ∗ Φ i v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Liris, postcondition of a thread i must include othreadG_term i. *)
Definition lwp_pre `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => (|={E}=>g Φ v)
     | None => (lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef (lift_term j fork_post)))
     end)%I.

Lemma lwp_pre_mono `{SI : indexT} `{!lirisGS Λ Σ} s
  (lwp1 lwp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, lwp1 i E e Φ -∗ lwp2 i E e Φ) →
     ∀ i E e Φ, lwp_pre s lwp1 i E e Φ -∗ lwp_pre s lwp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Hlwp". rewrite /lwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (lwp_step_mono with "[] Hlwp"). iModIntro.
  iIntros (e efs) "[Hlwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  iApply (@big_sepM_impl with "Hefs"); iIntros "!#" (k e' _) "Hlwp". by iApply "Hmono".
Qed.

(* Uncurry [lwp_pre] and equip its type with an OFE structure *)
Definition lwp_pre' `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : indexT} `{!lirisGS Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step.
    do 27 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition lwp_def `{SI : indexT} `{!lirisGS Λ Σ} : Lwp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, ((bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ))%I.
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI Λ Σ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : indexT} `{!lirisGS Λ Σ} : lwp = @lwp_def SI Λ Σ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.

Section lwp.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma lwp_pre_lwp_pre' s _lwp i E e Φ :
  lwp_pre s _lwp i E e Φ = lwp_pre' s (λ '(i,E,e,Φ), _lwp i E e Φ) (i,E,e,Φ).
Proof. rewrite /lwp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.
Lemma lwp_unfold s i E e Φ :
  lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ).
Proof.
  rewrite lwp_unseal. rewrite lwp_pre_lwp_pre' /lwp_def.
  rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
  - iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. done.
  - iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. done.
Qed.

(* Lemma lwp_cond s i E e Φ : *)
(*   lWP e @ s; i; E {{ Φ }} ⊣⊢ (ς -∗ lWP e @ s; emp; i; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite !lwp_unfold. iSplit; iIntros "H Hc". *)
(*   - iIntros "_". by iApply "H". *)
(*   - by iApply ("H" with "Hc"). *)
(* Qed. *)
(* Lemma lwp_cond_intro s i E e Φ : *)
(*   (ς -∗ lWP e @ s; emp; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   rewrite (lwp_cond _ ς). iIntros "H Hc". by iApply "H". *)
(* Qed. *)
(* Lemma lwp_cond_elim s i E e Φ : *)
(*   lWP e @ s; i; E {{ Φ }} -∗ ς -∗ lWP e @ s; emp; i; E {{ Φ }}. *)
(* Proof. *)
(*   rewrite (lwp_cond _ ς). iIntros "H Hc". by iApply "H". *)
(* Qed. *)

Lemma lwp_ind_strong s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ ∧ lWP e @ s; i; E {{ Φ }}) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (i e E Φ) "H". rewrite lwp_unseal.
  set (Ψ' := uncurry4 Ψ :
         prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[[i1 E1] e1] Φ1] [[[i2 E2] e2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=.
    etransitivity; first apply HΨ, H2. done. }
  iApply (least_fixpoint_ind _ Ψ' with "[] H").
  iIntros "!#" ([[[? ?] ?] ?]) "H". iApply "IH". rewrite lwp_pre_lwp_pre'.
  iApply (bi_mono_pred with "[] H").
  { repeat intro. do 3 (f_equiv || done). }
  { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
    inv H0; simpl in *. inv H1; simpl in *. inv H0; simpl in *.
    apply leibniz_equiv in H3, H1, H4. subst. f_equiv.
    { f_equiv. done. }
    { rewrite /lwp_def. f_equiv. done. }
  }
  iIntros "!>" (?) "H". destruct x as [[[? ?] ?] ?].
  iSplit.
  - iDestruct "H" as "[H _]". done.
  - iDestruct "H" as "[_ H]". done.
Qed.

Lemma lwp_ind s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply lwp_ind_strong. iIntros "!>" (i e E Φ) "Hrwp".
  iApply "H". iApply (lwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (i E e Φ) "[$ _]".
Qed.

Global Instance lwp_ne s i E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !lwp_unseal /lwp_def.
  by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance lwp_proper s i E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (lwp (PROP:=iProp Σ) s i E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_ne=>v; apply equiv_dist.
Qed.

(* Global Instance lwp_ne_2 s i E e Φ n : *)
(*   Proper ((dist n) ==> dist n) (λ ς, lwp (PROP:=iProp Σ) s i E e Φ). *)
(* Proof. *)
(*   intros ?? HΦ. rewrite !lwp_unseal /lwp_def. f_equiv. done. *)
(* Qed. *)
(* Global Instance lwp_proper_2 s i E e Φ : *)
(*   Proper ((≡) ==> (≡)) (λ ς, lwp (PROP:=iProp Σ) s i E e Φ). *)
(* Proof. *)
(*   intros ???. apply equiv_dist=>n. apply lwp_ne_2. by apply equiv_dist. *)
(* Qed. *)

Lemma sfgupd_elim_lwp s i E e Φ :
  (|={E}=>g lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_unfold. rewrite /lwp_pre /lwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (???) "SI". iMod ("H" with "SI") as "[SI H]".
    rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo.
    iMod ("H" with "SI") as "H". iModIntro. done.
  }
  iIntros (????) "SI". iMod ("H" with "SI") as "H".
  iModIntro. iMod "H" as ">[SI H]".
  rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo.
  iMod ("H" with "SI") as "H". iModIntro. iMod "H" as "[$ H]".
  iModIntro. done.
Qed.

Lemma lwp_value_fupd' s i E Φ v :
  lWP of_val v @ s; i; E {{ Φ }} ⊣⊢ (|={E}=>g (Φ v)).
Proof.
  iSplit; iIntros "H".
  - rewrite lwp_unfold /lwp_pre to_of_val. done.
  - rewrite lwp_unfold /lwp_pre to_of_val. done.
Qed.

Lemma lwp_stuckness_mono s1 s2 i E e Φ :
  s1 ⊑ s2 →
  lWP e @ s1; i; E {{ Φ }} -∗ lWP e @ s2; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iRevert (i e E Φ) "H".
  iApply lwp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
  rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:?; first done.
  iIntros (????) "H". iMod ("IH" with "[$]") as "H".
  iModIntro. iMod "H" as "[% IH]".
  iModIntro. iSplit; [by destruct s1, s2|clear H0].
  iIntros (????). iMod ("IH" with "[//]") as ">IH".
  iMod "IH" as "IH". iModIntro.
  iMod "IH" as "($& [IH Efs])". iDestruct "IH" as "[IH _]".
  iModIntro. iFrame.
  iApply (big_sepM_impl with "Efs"). iIntros "!>" (k ef _). iIntros "[H _]". done.
Qed.

Lemma lwp_strong_mono_sfgupd s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  lWP e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v -∗ |={E2}=>g Ψ v) -∗ lWP e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
  iApply lwp_ind_strong; [solve_proper| ].
  iIntros "!>" (i e E1 Φ) "IH % %HE HΦ".
  rewrite !lwp_unfold /lwp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (???) "SI".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod ("IH" with "SI") as "IH".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose2". iMod "IH". iMod "Hclose2" as "_". iMod "IH" as "[SI IH]".
    iMod "Hclose" as "_".
    iMod ("HΦ" with "IH SI") as "$". done.
  }
  iIntros (????) "H". iSpecialize ("IH" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "IH". iModIntro. iMod "IH" as "(%& IH)". iModIntro.
  iSplit; [by destruct s1, s2|clear H0].
  iIntros (????). iMod ("IH" with "[//]") as ">IH".
  iMod "IH". iModIntro. iMod "IH" as "[$ IH]".
  iMod "Hclose" as "_". iModIntro.
  iDestruct "IH" as "([IH _]& Efs)".
  iSplitR "Efs".
  + by iApply "IH".
  + iApply (big_sepM_impl with "Efs"); iIntros "!>" (k ef _).
    iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
Qed.

Lemma lwp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  lWP e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ lWP e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iApply (lwp_strong_mono_sfgupd with "H [HΦ]"). all: auto.
  iIntros "% H". iMod ("HΦ" with "H") as "$". done.
Qed.

Lemma fupd_lwp s i E e Φ :
  (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply sfgupd_elim_lwp. iMod "H". by iModIntro.
Qed.
Lemma lwp_fupd s i E e Φ :
  lWP e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
Proof. iIntros "H". iApply (lwp_strong_mono s s i E with "H"); auto. Qed.

Lemma lwp_sfgupd s i E e Φ :
  lWP e @ s; i; E {{ v, |={E}=>g Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
Proof. iIntros "H". iApply (lwp_strong_mono_sfgupd s s i E with "H"); auto. Qed.

Lemma lwp_atomic s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})
  ⊢ lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !lwp_unfold /lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros (???) "SI". iMod ("H" with "SI") as ">H".
    iModIntro. iMod "H". iModIntro. iMod "H" as "[$ H]".
    done.
  }
  iIntros (????) "SI". iMod ("H" with "SI") as "H". iMod "H".
  iModIntro. iMod "H" as "[$ H]". iModIntro.
  iIntros (??? STEP). iMod ("H" with "[//]") as "H".
  iMod "H". iMod "H" as ">(SI& H& Efs)".
  destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iMod ("H" with "SI") as "H".
      iModIntro. iMod "H" as ">(SI& >H)". iFrame "Efs SI".
      iModIntro. iModIntro. done.
    + iMod ("H" $! _ _ [] _ with "SI") as "H".
      iModIntro. iMod "H" as "[Red H]".
      iDestruct "Red" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ _ _ STEP).
  - destruct (atomic _ _ _ _ _ _ _ STEP) as [v <-%of_to_val].
    rewrite lwp_value_fupd'. iMod ("H" with "SI") as "H".
    iModIntro. iMod "H". iModIntro.
    iMod "H" as "(SI& >H)". iModIntro. iFrame.
    iApply lwp_value_fupd'. iModIntro. done.
Qed.

Lemma lwp_step_fupd s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1,E2}=> |={E2,E1}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (? ?) "[HP Hwp]". iApply (lwp_strong_mono with "Hwp"); [done..|].
  iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
Qed.

Lemma lwp_bind K `{!LanguageCtx K} s i E e Φ :
  (lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }})
  ⊢ lWP K e @ s; i; E {{ Φ }}.
Proof.
  revert Φ.
  cut (∀ Φ', lWP e @ s; i; E {{ Φ' }} -∗ ∀ Φ, (∀ v, (Φ' v) -∗ (lWP K (of_val v) @ s; i; E {{ Φ }})) -∗ lWP K e @ s; i; E {{ Φ }}).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (i e E Φ') "H".
  iApply lwp_ind_strong; first solve_proper.
  iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /lwp_pre /lwp_step. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply sfgupd_elim_lwp.
    iIntros (???) "SI". iMod ("IH" with "SI") as "[SI IH]".
    iModIntro. iFrame. by iApply "HΦ".
  }
  rewrite lwp_unfold /lwp_pre /lwp_step fill_not_val; last auto.
  iIntros (????) "SI". iMod ("IH" with "SI") as "IH".
  iModIntro. iMod "IH" as "(%& IH)". iModIntro. iSplit.
  { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv i e σ1 Θ κ e2 σ2 efs) as (e2'&->&?); auto.
  iDestruct ("IH" with "[//]") as ">IH".
  iMod "IH" as ">IH". iModIntro. iMod "IH".
  iModIntro. iDestruct "IH" as "(SI& IH& Efs)".
  iFrame. iSplitL "IH HΦ".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

Lemma lwp_bind_inv K `{!LanguageCtx K} s i E e Φ :
  lWP K e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}.
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (i e' E Φ) "H". iApply lwp_ind_strong; first solve_proper.
  iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->).
  rewrite !lwp_unfold {2}/lwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-.
    iModIntro. rewrite !lwp_unfold.
    iApply (lwp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]".
  }
  rewrite /lwp_pre fill_not_val; [|done].
  iIntros (????) "SI". iMod ("IH" with "[$]") as "IH".
  iModIntro. iMod "IH" as "(%& IH)". iSplitR.
  { destruct s; eauto using reducible_fill_inv. }
  iModIntro. iIntros (e2 σ2 efs Hstep). iDestruct ("IH" with "[]") as ">IH".
  { eauto using fill_step. }
  iMod "IH" as ">IH". iModIntro. iMod "IH" as "(SI& IH& Efs)".
  iModIntro. iFrame. iSplitR "Efs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

(** * Derived rules *)
Lemma lwp_mono s i E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (lwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma lwp_stuck_mono s1 s2 i E e Φ :
  s1 ⊑ s2 → lWP e @ s1; i; E {{ Φ }} ⊢ lWP e @ s2; i; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (lwp_strong_mono with "H"); auto. Qed.
Lemma lwp_stuck_weaken s i E e Φ :
  lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ i; E ?{{ Φ }}.
Proof. apply lwp_stuck_mono. by destruct s. Qed.
Lemma lwp_mask_mono s i E1 E2 e Φ : E1 ⊆ E2 → lWP e @ s; i; E1 {{ Φ }} ⊢ lWP e @ s; i; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (lwp_strong_mono with "H"); auto. Qed.
Global Instance lwp_mono' s i E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (lwp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.
Global Instance lwp_flip_mono' s i E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (lwp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.

Lemma lwp_value_sfgupd s i E Φ e v :
  IntoVal e v →
  lWP e @ s; i; E {{ Φ }} ⊣⊢ (|={E}=>g (Φ v)).
Proof. intros <-. by apply lwp_value_fupd'. Qed.
Lemma lwp_value' s i E Φ v : (Φ v) ⊢ lWP (of_val v) @ s; i; E {{ Φ }}.
Proof.
  rewrite lwp_value_fupd'. iIntros "H". by iApply sfgupd_intro.
Qed.
Lemma lwp_value s i E Φ e v : IntoVal e v → (Φ v) ⊢ lWP e @ s; i; E {{ Φ }}.
Proof. intros <-. apply lwp_value'. Qed.

Lemma lwp_frame_l s i E e Φ R :
  R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma lwp_frame_r s i E e Φ R :
  lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the lWP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma lwp_step_fupd_2 s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1∖E2,∅}=> |={∅,E1∖E2}=> P) ∗
   lWP e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (lwp_step_fupd with "[H]"); [done|].
  iApply (sep_mono_l with "H"). iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply fupd_mask_frame; [|iMod "HP"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.

Lemma lwp_frame_step_l s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1,E2}=> |={E2,E1}=> R) ∗ lWP e @ s; i; E2 {{ Φ }} ⊢ lWP e @ s; i; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply lwp_step_fupd; first done.
  iFrame "Hu". iApply (lwp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma lwp_frame_step_r s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  lWP e @ s; i; E2 {{ Φ }} ∗ (|={E1,E2}=> |={E2,E1}=> R) ⊢ lWP e @ s; i; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(lWP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply lwp_frame_step_l.
Qed.
Lemma lwp_frame_step_l' s i E e Φ R :
  TCEq (to_val e) None →
  R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s i E E); try iFrame; eauto. Qed.
Lemma lwp_frame_step_r' s i E e Φ R :
  TCEq (to_val e) None →
  lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_r s i E E); try iFrame; eauto. Qed.

Lemma lwp_wand s i E e Φ Ψ :
  lWP e @ s; i; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ lWP e @ s; i; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (lwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma lwp_wand_l s i E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_wand_r s i E e Φ Ψ :
  lWP e @ s; i; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ lWP e @ s; i; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_frame_wand s i E e Φ R :
  R -∗ lWP e @ s; i; E {{ v, R -∗ Φ v }} -∗ lWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (lwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_lwp p s i E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite lwp_frame_l. apply lwp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_lwp s i E e Φ : IsExcept0 (lWP e @ s; i; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_lwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_lwp p s i E e P Φ :
    ElimModal True p false (|==> P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  Global Instance elim_modal_fupd_lwp p s i E e P Φ :
    ElimModal True p false (|={E}=> P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  Global Instance elim_modal_sfgupd_lwp p s i E e P Φ :
    ElimModal True p false (|={E}=>g P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (_) "[P H]". iApply sfgupd_elim_lwp. iMod "P".
    iModIntro. by iApply ("H" with "P").
  Qed.

  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_lwp_wrong_mask p s i E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_lwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (lWP e @ s; i; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_lwp_atomic p s i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (lWP e @ s; i; E1 {{ Φ }}) (lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r lwp_atomic.
  Qed.

  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_lwp_atomic_wrong_mask p s i E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (lWP e @ s; i; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_lwp s i E e P Φ :
    AddModal (|={E}=> P) P (lWP e @ s; i; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_lwp. Qed.

  Global Instance add_modal_ghost_step_lwp s i E e P Φ :
    AddModal (|={E}=>g P) P (lWP e @ s; i; E {{ Φ }}).
  Proof. rewrite /AddModal. iIntros "[H1 H2]". iMod "H1". by iApply "H2". Qed.

  Global Instance elim_acc_lwp_atomic {X} i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (lWP e @ s; i; E1 {{ Φ }})
            (λ x, lWP e @ s; i; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_lwp_nonatomic {X} i E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (lWP e @ s; i; E {{ Φ }})
            (λ x, lWP e @ s; i; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_fupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
