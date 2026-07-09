(** From the artifact of
    Later Credits: Resourceful Reasoning for the Later Modality
    by Spies et al. 2022
 *)

From iris.prelude Require Import options.
From iris.algebra Require Export auth.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Export own.
From transfinite.stepindex Require Export utils.
(* From transfinite.stepindex Require Import ordinal_arith. *)
(* From transfinite.algebra Require Import ordinals. *)
From lantana.algebra Require Import ordinal_ucmra.
From lantana.base_logic Require Export relational_updates.

Section aux.

  (* existential property preserved over injections *)
  Lemma type_inj_existential@{i j} (X : Type@{i}) (Y : Type@{j}) (SI : indexT) (f : X → Y) :
    TypeExistentialProperty Y SI →
    Inj eq eq f →
    TypeExistentialProperty X SI.
  Proof.
    intros Hex Hsur P Hdown Hwit.
    edestruct (Hex (λ y n, ∃ x, f x = y ∧ P x n)) as [y Hy].
    - intros y a b Hlt [x [fx HP]]. exists x; split; eauto.
    - intros n; destruct (Hwit n) as [x HP]. exists (f x), x.
      by split.
    - specialize (Hy index_zero) as Hzero.
      destruct Hzero as [x [fx HP]].
      exists x. intros n. destruct (Hy n) as [x' [fx' HP']].
      rewrite -fx' in fx. by rewrite (inj f x x' fx).
  Qed.

End aux.

(** This file contains the definition of later credits. In the Transfinite Iris
   developement, this one, the file contains two instantiations of later
   credits: one with natural numbers and one with ordinals. Both instantiations
   share some common theory, which can be found at the beginning of this file.
   After the shared theory, we derive the concrete instantiations.

   Parts of the general theory and the instantiation with natural numbers are
   the same for the finite Iris development of later credits.
  *)

(** To be able to work with ordinals and natural numbers generically for large
   parts of this file, we fix the abstraction [auth_rupd]. The abstraction
   bundles a discrete camera A (i.e., one of Iris's resource algebras) together
   with a well-founded relation [auth_rupd_rel], a successor operation
   [auth_rupd_next], a number of compatibility properties.
*)

Class auth_rupd `{SI : indexT} (A : ucmra) := {
    auth_rupd_discrete :: CmraDiscrete A;
    auth_rupd_rel : relation A;
    auth_rupd_next : A → A;
    auth_rupd_rel_wf : well_founded auth_rupd_rel;
    auth_rupd_rel_proper :: Proper (equiv ==> equiv ==> iff) auth_rupd_rel;
    auth_rupd_rel_frame (a a' f : A) : auth_rupd_rel a' a → auth_rupd_rel (a' ⋅ f) (a ⋅ f);
    auth_rupd_op_cancel (a f f' : A) : a ⋅ f ≡ a ⋅ f' → f ≡ f';
    auth_rupd_next_step x : auth_rupd_rel x (auth_rupd_next x);
    auth_valid_trivial (x : A) : ✓ x
  }.

Class auth_rupd_GpreS `{SI : indexT} (Σ : gFunctors) (A : ucmra) := {
    #[global] auth_rupd_GpreS_auth :: inG Σ (authR A);
  }.

Class auth_rupdGS `{SI : indexT} (Σ : gFunctors) (A : ucmra) :=
  Auth_rupdG {
      #[global] auth_rupd_inG :: auth_rupd_GpreS Σ A;
      auth_rupd_name : gname;
    }.

Definition auth_rupdΣ `{SI : indexT} (A : ucmra): gFunctors :=
  #[GFunctor (authR A)].

Global Instance subG_auth_rupdΣ `{SI : indexT} {Σ : gFunctors} {A : ucmra} : subG (auth_rupdΣ A) Σ → auth_rupd_GpreS Σ A.
Proof. solve_inG. Qed.

(** In the following section, we prove abstractly the properties of finite and
   transfinite later credits. To do so, we assume an instance of [auth_rupd]. *)
Section auth_rupd.
  Context `{SI : indexT} (Σ : gFunctors) (X : ucmra) `{!auth_rupd X}.

  (** We instantiate the relational updates with the relation from [auth_rupd]. *)
  Global Instance auth_rupdGS_instance `{!auth_rupdGS Σ X} : rupdG Σ X :=
    {|
      rupd_pred := λ x, own auth_rupd_name (● x);
      rupd_rel := auth_rupd_rel;
      rupd_rel_wf := auth_rupd_rel_wf;
    |}.

  (** the connective for the total supply of credits *)
  Definition rupdA `{!auth_rupdGS Σ X} (a : X) : iProp Σ := own auth_rupd_name (● a).
  (** the connective for the later credits *)
  Definition rupdF `{!auth_rupdGS Σ X} (a : X) : iProp Σ := own auth_rupd_name (◯ a).

  (** We prove a generic lemma about updating the ghost state of [auth_rupd] in Iris.
     It effectively says that if we are willing to decrease our later credits (the [b]s),
     then we can also decrease the total supply of later credits (the [a]s).
   *)
  Lemma auth_rupd_rel_update `{!auth_rupdGS Σ X} (a b b' : X) :
    ✓ a → b ≼ a → auth_rupd_rel b' b → ∃ a', (a, b) ~l~> (a', b') ∧ auth_rupd_rel a' a.
  Proof.
    intros Hv Hincl Hstep.
    destruct Hincl as [f Heq].
    eapply (auth_rupd_rel_frame _ _ f) in Hstep.
    exists (b' ⋅ f). split; rewrite Heq.
    - intros α [f'|]; simpl; intros ? Heq'; split.
      + apply cmra_valid_validN, auth_valid_trivial.
      + f_equiv. eapply discrete_iff; first apply _.
        eapply discrete_iff in Heq'; last apply _.
        eapply auth_rupd_op_cancel; last eauto; eauto.
      + apply cmra_valid_validN, auth_valid_trivial.
      + specialize (ucmra_unit_right_id  b') as H'. rewrite -{2}H'. f_equiv.
        eapply discrete_iff; first apply _.
        eapply discrete_iff in Heq'; last apply _.
        eapply auth_rupd_op_cancel.
        by rewrite ucmra_unit_right_id.
    - eapply Hstep.
  Qed.

  (** We lift the generic ghost state update lemma to Iris propositions. The
     generic version says that if we can decrease [a] later credits to [a'] later
     credits (e.g., by going from 1 to 0 credits), then we are allowed to
     eliminate a later modality (because it appears in front of our goal).
     *)
  Lemma auth_rupd_step `{!auth_rupdGS Σ X} (a a' : X) P :
    auth_rupd_rel a' a →
    rupdF a ∗ (rupdF a' -∗ ▷ |==>r P) ⊢ |==>r P.
  Proof.
    intros Hstep. iIntros "[Hf Hupd]".
    iApply rupd_step; simpl. iIntros (x) "Hx".
    iCombine "Hx Hf" as "Hown".
    iPoseProof (own_valid_l with "Hown") as (Hv) "Hown".
    apply auth_both_valid in Hv as [Hincl Hv].
    specialize (Hincl stepindex.zero). apply cmra_discrete_included_iff in Hincl.
    eapply auth_rupd_rel_update in Hv as [x' [Hl Hstep']]; [| apply Hincl | apply Hstep].
    iMod (own_update _ _ (● x' ⋅ ◯ a') with "Hown") as "Hown"; first by apply auth_update.
    iModIntro. iExists (x'). iDestruct "Hown" as "($ & Hf)".
    iSpecialize ("Hupd" with "Hf").
    iFrame. iPureIntro. by apply tc_once.
  Qed.

  (** A corollary of the definition of relational updates
     is that we can always weaken the number of credits,
     meaning we can drop some if we want to.  *)
  Lemma auth_rupd_weaken `{!auth_rupdGS Σ X} (a a' : X):
    rc auth_rupd_rel a' a → (rupdF a ⊢ |==>r rupdF a').
  Proof.
    destruct 1 as [->|Hstep]; first by apply rupd_intro.
    iIntros "Hf". iApply (auth_rupd_step with "[Hf]"); first done.
    iFrame. iIntros "Hf". iNext. by iApply rupd_intro.
  Qed.

  (** We can split and combine credits as we see fit. The [⋅]
     operation will be instantiated with the right notion of
     plus for each kind of later credit further below. *)
  Lemma rupdF_split `{!auth_rupdGS Σ X} x y :
    rupdF (x ⋅ y) ⊣⊢ rupdF x ∗ rupdF y.
  Proof.
    rewrite /rupdF -own_op auth_frag_op //=.
  Qed.

  Lemma rupdF_equiv `{!auth_rupdGS Σ X} x y :
    (x ≡ y) → rupdF x ⊣⊢ rupdF y.
  Proof.
    intros He. rewrite /rupdF. rewrite He. done.
  Qed.

  (** In Transfinite Iris, we define a modality for allocating new later credits.
     We use this modality in the definition of the weakest precondition. It is
     essentially just an existential quantifier over the additional number of
     later credits that we would like to allocate for the rest of the proof.
  *)
  Section allocation.
    Context `{!auth_rupdGS Σ X}.

    Definition ALC P := (∃ x : X, rupdF x -∗ |==>r P)%I.

    (* some laws for the allocation modality *)
    Lemma ALC_later P : ALC P ⊣⊢ ALC (▷ P).
    Proof.
      rewrite /ALC; apply bi.equiv_entails; split.
      - iDestruct 1 as (x) "Hwand". iExists x. by rewrite -(bi.later_intro P).
      - iDestruct 1 as (x) "Hwand". iExists (x ⋅ auth_rupd_next ε).
        rewrite rupdF_split. iIntros "[Hx Hnext]".
        iMod ("Hwand" with "Hx") as "HP".
        iApply (auth_rupd_step with "[Hnext HP]"); first apply auth_rupd_next_step.
        iFrame "Hnext". iIntros "_". iNext. by iApply rupd_intro.
    Qed.

    Lemma ALC_rupd P : ALC P ⊣⊢ ALC (|==>r P).
    Proof.
      rewrite /ALC; apply bi.equiv_entails; split.
      - iDestruct 1 as (x) "Hwand". iExists x.
        iIntros "Hupd". iApply rupd_intro. by iApply "Hwand".
      - iDestruct 1 as (x) "Hwand". iExists x.
        by rewrite rupd_trans.
    Qed.
 
    Lemma ALC_bupd P : ALC P ⊣⊢ ALC (|==> P).
    Proof.
      rewrite /ALC; apply bi.equiv_entails; split.
      - iDestruct 1 as (x) "Hwand". iExists x.
        iIntros "Hupd". iMod ("Hwand" with "Hupd"). by iFrame.
      - iDestruct 1 as (x) "Hwand". iExists x.
        by rewrite rupd_bupd_r.
    Qed.

    Lemma ALC_credits x P : ALC P ⊣⊢ ALC (rupdF x -∗ P).
    Proof.
      rewrite /ALC; apply bi.equiv_entails; split.
      - iDestruct 1 as (y) "Hwand". iExists y.
        iIntros "Hupd". iMod ("Hwand" with "Hupd").
        iModIntro. by iIntros "_".
      - iDestruct 1 as (y) "Hwand". iExists (x ⋅ y).
        rewrite rupdF_split. iIntros "[Hx Hy]".
        iMod ("Hwand" with "Hy") as "P".
        iModIntro. by iApply "P".
    Qed.

    Lemma ALC_fmap P Q : ALC (P -∗ Q) ⊢ ALC P -∗ ALC Q.
    Proof.
      iIntros "APQ AP".
      iDestruct "APQ" as (x1) "APQ".
      iDestruct "AP" as (x2) "AP".
      iExists (x1 ⋅ x2). rewrite rupdF_split.
      iIntros "[Hx1 Hx2]". iMod ("AP" with "Hx2") as "P".
      iMod ("APQ" with "Hx1") as "PQ".
      iApply rupd_intro. by iApply "PQ".
    Qed.

    Lemma ALC_intro P : P ⊢ ALC P.
    Proof.
      iIntros "P". iExists ε. iIntros "_". by iApply rupd_intro.
    Qed.

    Lemma ALC_alloc x P : (rupdF x -∗ |==>r P) ⊢ ALC P.
    Proof. by rewrite ALC_rupd ALC_credits -ALC_intro. Qed.

    Lemma ALC_wand P Q : (P -∗ Q) ⊢ ALC P -∗ ALC Q.
    Proof.
      iIntros "HPQ HP". iApply (ALC_fmap with "[HPQ] HP").
      by iApply ALC_intro.
    Qed.

    Lemma ALC_mono P Q : (P ⊢ Q) → ALC P ⊢ ALC Q.
    Proof.
      iIntros (HPQ) "HP". iApply ALC_wand; last eauto.
      iApply HPQ.
    Qed.

    Global Instance ALC_ent_proper : Proper ((⊢) ==> (⊢)) ALC.
    Proof.
      intros P Q PQ. by apply ALC_mono.
    Qed.

    Global Instance ALC_flip_ent_proper : Proper (flip (⊢) ==> flip (⊢)) ALC.
    Proof.
      intros P Q PQ. by apply ALC_mono.
    Qed.

    Global Instance ALC_ne : NonExpansive ALC.
    Proof.
      intros n P Q EQ; rewrite /ALC. by do 4 f_equiv.
    Qed.

    Global Instance ALC_equiv_proper : Proper ((≡) ==> (≡)) ALC := ne_proper _.

    Global Instance ALC_contractive : Contractive ALC.
    Proof.
      intros n P Q Heq.
      rewrite (ALC_later P) (ALC_later Q). f_equiv.
      by f_contractive.
    Qed.

    Global Instance from_modal_ALC P : FromModal True modality_id P (ALC P) P.
    Proof.
      rewrite /FromModal //=. intros. apply ALC_intro.
    Qed.

    Global Instance from_pure_ALC a φ P :
      FromPure a P φ → FromPure a (ALC P) φ.
    Proof. rewrite /FromPure. intros <-. apply ALC_intro. Qed.

    Global Instance elim_rupd_ALC (p : bool) P Q :
      ElimModal True p false (ALC P) P (ALC Q) Q.
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim //=.
      iIntros "_ [HP HPQ]". by iApply (ALC_wand with "HPQ").
    Qed.

    Global Instance frame_ALC b R P Q :
      Frame b R P Q → Frame b R (ALC P) (ALC Q).
    Proof.
      rewrite /Frame. iIntros (Hent) "[R Q]". iMod "Q".
      iApply Hent; iFrame.
    Qed.

    Global Instance into_wand_ALC R P Q :
      IntoWand false false R P Q → IntoWand false false (ALC R) (ALC P) (ALC Q).
    Proof.
      rewrite /IntoWand /= => HR; simpl in *.
      iIntros "R P". rewrite HR.
      iApply (ALC_fmap with "R P").
    Qed.

    Lemma sat_ALC {sat : iProp Σ → Prop}
      `{!Satisfiable sat} `{!SatisfiableRUpd sat} `{!SatisfiableRUpdUpdate sat} `{!SatisfiableExists X sat} P :
      sat (ALC P) → sat P.
    Proof.
      rewrite /ALC. intros Hsat.
      eapply sat_exists in Hsat as [x Hsat].
      eapply sat_pred_upd with (Q := rupdF x) in Hsat.
      { eapply sat_rupd, sat_mono, Hsat. iIntros "[HP Hx]". by iApply "HP". }
      simpl; intros z. iIntros "H●".
      iMod (own_update _ (● z) with "H●") as "[? ?]".
      - apply (auth_update_alloc z (x ⋅ z)).
        apply (op_local_update_discrete z ε x).
        intros ?. apply auth_valid_trivial.
      - iModIntro. iExists _. iFrame. by rewrite (right_id ε).
    Qed.

    Notation "'ALC?' p P" := (Nat.iter (Nat.b2n p) ALC P) (at level 20, p at level 9, P at level 20) : bi_scope.

    Global Instance from_modal_ALCb b P : FromModal True modality_id P (ALC? b P) P.
    Proof. destruct b; simpl. 1: apply _. done. Qed.

    Global Instance from_pure_ALCb a φ b P :
      FromPure a P φ → FromPure a (ALC? b P) φ.
    Proof. destruct b; simpl; intros. 1: apply _. done. Qed.

    Global Instance elim_rupd_ALCb (p : bool) b P Q :
      ElimModal True p false (ALC? b P) P (ALC? b Q) Q.
    Proof.
      destruct b; simpl. 1: apply _.
      rewrite /ElimModal bi.intuitionistically_if_elim //=.
      iIntros "_ [HP HPQ]". by iApply ("HPQ" with "HP").
    Qed.

  End allocation.

  (** Later credits admit an induction principle that is similar to Löb
       induction. Löb induction means (▷ P ⊢ P) implies ⊢ P. In other words, we
       can assume our goal underneath a later. The corresponding principle for
       later credits is:
          (£1 -∗ P) ⊢ P implies ⊢ P
     It means that if we are willing to spend one credit, then we can get access
     to our goal.

     Since later credits can only be spent at specific places (e.g., updates
     |==>r and weakest preconditions), the principle only applies to certain
     kinds of propositions P. We call them the CreditExchange propositions P
     below.
  *)

  (* credits induction *)
  Class CreditExchange `{!auth_rupdGS Σ X} (P : iProp Σ) := {
      credit_to_later:
      rupdF (auth_rupd_next ε) ∗ ▷ P ⊢ P
    }.

  Lemma credit_ind `{!auth_rupdGS Σ X} P `{!CreditExchange P} :
    □ ((rupdF (auth_rupd_next ε) -∗ P) → P) ⊢ P.
  Proof.
    iIntros "#H". iLöb as "IH".
    iApply "H". iIntros "Hc".
    iApply (credit_to_later with "[Hc]"). by iFrame.
  Qed.


  Global Instance rupd_credit_exchange `{!auth_rupdGS Σ X} P : CreditExchange (|==>r P).
  Proof.
    econstructor. iIntros "[Hf Hl]".
    iApply (auth_rupd_step with "[Hf Hl]"); first apply auth_rupd_next_step.
    iFrame. by iIntros "_".
  Qed.

  Global Instance forall_credit_exchange `{!auth_rupdGS Σ X} {Y} (Φ : Y → iProp Σ) :
    (∀ x, CreditExchange (Φ x)) → (CreditExchange (∀ x, Φ x)).
  Proof.
    intros HC. econstructor. iIntros "[Hc Hl]" (x).
    destruct (HC x) as [HC0]. iApply (HC0 with "[Hc Hl]").
    iFrame. iNext. iApply "Hl".
  Qed.

  Global Instance exists_credit_exchange `{@FiniteIndex SI} `{!auth_rupdGS Σ X} {Y} `{!Inhabited Y} (Φ : Y → iProp Σ) :
    (∀ x, CreditExchange (Φ x)) → (CreditExchange (∃ x, Φ x)).
  Proof.
    intros HC. econstructor. iIntros "[Hc Hl]".
    iPoseProof (bi.later_exist with "Hl") as "[%x Hl]".
    iExists x. destruct (HC x) as [HC0]. iApply (HC0 with "[Hc Hl]"). iFrame.
  Qed.

  Global Instance and_credit_exchange `{!auth_rupdGS Σ X} P Q :
    (CreditExchange P) → (CreditExchange Q) → CreditExchange (P ∧ Q).
  Proof.
    intros HP HQ. destruct HP as [HP0], HQ as [HQ0]. econstructor.
    rewrite bi.later_and. iIntros "[Hc HPQ]".
    iCombine "Hc HPQ" as "R". iApply bi.and_intro; last by iAssumption.
    - rewrite bi.and_elim_l. auto.
    - rewrite bi.and_elim_r. auto.
  Qed.

  Global Instance or_credit_exchange `{@FiniteBoundedExistential SI} `{!auth_rupdGS Σ X} P Q :
    (CreditExchange P) → (CreditExchange Q) → CreditExchange (P ∨ Q).
  Proof.
    intros HP HQ. destruct HP as [HP0], HQ as [HQ0]. econstructor.
    rewrite bi.later_or_1. iIntros "[Hc [HP|HQ]]".
    - iLeft. iApply (HP0 with "[Hc HP]"). iFrame.
    - iRight. iApply (HQ0 with "[Hc HQ]"). iFrame.
  Qed.

  Global Instance wand_credit_exchange `{!auth_rupdGS Σ X} P Q :
    (CreditExchange Q) → CreditExchange (P -∗ Q).
  Proof.
    intros HP. destruct HP as [HP]. econstructor.
    iIntros "[Hc HPQ] P". iApply (HP with "[Hc P HPQ]").
    iFrame. iNext. by iApply "HPQ".
  Qed.

  (* Global Instance fupd_credit_exchange `{!auth_rupdGS Σ X} `{!invG Σ} E1 E2 P : CreditExchange (|={E1, E2}=> P)%I. *)
  (* Proof. *)
  (*   rewrite fupd_eq /fupd_def. apply _. *)
  (* Qed. *)

End auth_rupd.

Global Arguments rupdF {SI Σ X _} a.
Global Arguments rupdA {SI Σ X _} a.

(** The notation for later credits that we use in the rest of this developemnt. *)
Notation "£ a" := (rupdF a) (at level 60).
Notation "●£ a" := (rupdA a) (at level 60).

Global Arguments ALC {SI Σ X _ _} P.
Global Arguments sat_ALC {_ _ _ _ _ _ _ _ _ _} P.
Notation "'ALC?' p P" := (Nat.iter (Nat.b2n p) ALC P) (at level 20, p at level 9, P at level 20) : bi_scope.


Lemma auth_rupd_rel_irrefl `{SI : indexT} {M: ucmra} `{!auth_rupd M} x: ¬ auth_rupd_rel x x.
Proof.
  intros Hlt. induction (auth_rupd_rel_wf x); eauto.
Qed.

Global Instance rupd_type_exists_finite `{SI : indexT} {M: ucmra}
  `{!auth_rupd M} `{!TypeExistentialProperty M SI}: FiniteExistential SI.
Proof.
  eapply (type_inj_existential bool M) with (f := λ b: bool, if b then ε else auth_rupd_next ε); first done.
  intros [] []; auto; intros Heq; exfalso; eapply (auth_rupd_rel_irrefl ε).
  - rewrite {2}Heq; eapply auth_rupd_next_step.
  - rewrite -{2}Heq; eapply auth_rupd_next_step.
Qed.

(* Initial allocation *)
Lemma auth_rupd_alloc `{SI : indexT} {Σ : gFunctors} M `{!auth_rupd M} `{!auth_rupd_GpreS Σ M} k :
  ⊢ |==> ∃ _ : auth_rupdGS Σ M, (●£ k ∗ £ k).
Proof.
  iIntros.
  iMod (own_alloc ((● k ⋅ ◯ k) : authR M)) as (γA) "HA".
  { apply auth_both_valid_2; eauto using auth_valid_trivial. }
  iExists (Auth_rupdG _ Σ M _ γA). iDestruct "HA" as "($& $)". done.
Qed.

(** ** Transfinite Later Credits *)
(** We now instantiate the generic definition from above with ordinals to *)
(*    obtain a transfinite version of later credits £ (α: ord). *)
Notation tlcGS Σ := (auth_rupdGS Σ OrdUR).
Notation tlcGpreS Σ := (auth_rupd_GpreS Σ OrdUR).
Notation tlcΣ := (auth_rupdΣ OrdUR).

Notation "'£ω'" := (£ ω%ord) (at level 60).
Notation "'£n' a" := (£ (Ord.from_nat a)) (at level 60).

Section transfinite_lc.
  Context `{SI : indexT} `{!tlcGS Σ}.
  Local Open Scope ord.

  Lemma ord_auth_step_frame (a a' f : OrdR) :
    a' < a → (a' ⋅ f) < (a ⋅ f).
  Proof.
    intros Hαβ. by eapply Hessenberg.lt_add_l.
  Qed.

  Lemma ord_auth_op_cancel (a f f' : OrdR) :
    a ⋅ f ≡ a ⋅ f' → f ≡ f'.
  Proof using SI.
    rewrite comm [a ⋅ f']comm.
    by apply Hessenberg_add_cancel.
  Qed.

  Lemma ord_valid_trivial (a : OrdR) : ✓ a.
  Proof. done. Qed.

  (* we define an auth rupd instance for ordinals *)
  Global Instance ord_auth_rupd : auth_rupd (OrdUR) :=
    {|
      auth_rupd_discrete := _;
      auth_rupd_rel := Ord.lt;
      auth_rupd_next := Ord.S;
      auth_rupd_rel_wf := Ord.lt_well_founded;
      auth_rupd_rel_proper := _;
      auth_rupd_rel_frame := ord_auth_step_frame;
      auth_rupd_op_cancel := ord_auth_op_cancel;
      auth_rupd_next_step := Ord.S_lt;
      auth_valid_trivial := ord_valid_trivial
    |}.

  Lemma tlc_equiv (α β : Ord.t) :
    α == β → £ α ⊣⊢ £ β.
  Proof. intros. by apply rupdF_equiv. Qed.

  Lemma tlc_split (α β : Ord.t) :
    £ (α ⊕ β) ⊣⊢ £ α ∗ £ β.
  Proof. apply rupdF_split. Qed.

  Lemma tlc_succ (α : Ord.t) :
    £ (Ord.S α) ⊣⊢ £ Ord.one ∗ £ α.
  Proof.
    rewrite -tlc_split. symmetry. rewrite tlc_equiv; first reflexivity.
    rewrite Hessenberg.add_S_l Hessenberg.add_O_l. reflexivity.
  Qed.

  Lemma tlc_later_strong α β P :
    β < α →
    £ α ∗ (£ β -∗ ▷ |==>r P) ⊢ |==>r P.
  Proof.
    intros Hlt; apply auth_rupd_step. apply Hlt.
  Qed.

  Lemma tlc_later P :
    £ Ord.one ∗ (▷ |==>r P) ⊢ |==>r P.
  Proof.
    iIntros "[Hf Hupd]". iApply (tlc_later_strong (Ord.S Ord.O) Ord.O with "[Hf Hupd]").
    - apply Ord.S_lt.
    - iFrame. by iIntros "_".
  Qed.

  Lemma tlc_laterN P n :
    £(Ord.from_nat n) ∗ (▷^n |==>r P) ⊢ |==>r P.
  Proof.
    iIntros "[Hc Hu]". iInduction n as [ | n ] "IH"; first done.
    simpl. rewrite tlc_succ. iDestruct "Hc" as "[Hc0 Hc]".
    iApply (tlc_later with "[Hc0 Hu Hc]").
    iFrame. iNext. iApply ("IH" with "Hc Hu").
  Qed.

  Lemma tlc_weaken (α β : Ord.t) :
    β <= α → (£ α ⊢ |==>r £ β).
  Proof.
    intros Hle. apply ClassicOrd.le_eq_or_lt in Hle. destruct Hle.
    - eapply auth_rupd_weaken. apply rc_subrel; auto.
    - rewrite tlc_equiv; eauto. done.
  Qed.

  Lemma tlc_zero : ⊢ |==> £ Ord.O.
  Proof. iApply own_unit. Qed.

  Lemma tlc_loeb P `{!CreditExchange Σ OrdUR P} :
    □ ((£ Ord.one -∗ P) → P) ⊢ P.
  Proof.
    exact (credit_ind Σ OrdUR P).
  Qed.

  (* For natural numbers *)
  Lemma tlc_omega (n : nat) :
    £ω ⊢ |==>r £n n.
  Proof. apply tlc_weaken, Ord.lt_le, Ord.omega_upperbound. Qed.

  Lemma tlc_split_nat (n m : nat) :
    £n (n + m) ⊣⊢ £n n ∗ £n m.
  Proof.
    rewrite tlc_equiv. 2: eapply Hessenberg.add_from_nat.
    apply tlc_split.
  Qed.

  Lemma tlc_split_one (n m : nat) :
    n = (1 + m)%nat →
    £n n -∗ £n m ∗ £n 1.
  Proof.
    rewrite -tlc_split_nat. intros ->. rewrite Nat.add_comm. auto.
  Qed.

  Lemma tlc_one_nat :
    £n 1 ⊣⊢ £ Ord.one.
  Proof. by rewrite Ord.from_nat_1. Qed.

  Lemma tlc_succ_nat (n : nat) :
    £n (S n) ⊣⊢ £ Ord.one ∗ £n n.
  Proof. rewrite Ord.from_nat_S. apply tlc_succ. Qed.

End transfinite_lc.

(** Use one of two. *)
(* (** ** Transfinite Later Credits *) *)
(* (** We now instantiate the generic definition from above with ordinals to *)
(*    obtain a transfinite version of later credits £ (α: ord). *) *)
(* Notation tlcGS Σ := (auth_rupdGS Σ ordUR). *)
(* Notation tlcGpreS Σ := (auth_rupd_GpreS Σ ordUR). *)
(* Notation tlcΣ := (auth_rupdΣ ordUR). *)

(* (* Notation "'£ω'" := (£ ω%O) (at level 60). *) *)
(* (* Notation "'£n' a" := (£ (n2o a)) (at level 60). *) *)

(* Section transfinite_lc. *)
(*   Context `{SI : indexT} `{!tlcGS Σ}. *)
(*   Local Open Scope O. *)

(*   Lemma ord_auth_step_frame (a a' f : ordR): *)
(*     a' ≺ a → (a' ⋅ f) ≺ (a ⋅ f). *)
(*   Proof. *)
(*     intros Hαβ. *)
(*     by eapply natural_addition_strict_compat. *)
(*   Qed. *)

(*   Lemma ord_auth_op_cancel (a f f' : ordR): *)
(*     a ⋅ f = a ⋅ f' → f = f'. *)
(*   Proof using SI. *)
(*     rewrite comm_L [a ⋅ f']comm_L. *)
(*     by apply natural_addition_cancel. *)
(*   Qed. *)

(*   Lemma ord_valid_trivial (a: ordR): ✓ a. *)
(*   Proof. done. Qed. *)

(*   (* we define an auth rupd instance for ordinals *) *)
(*   Global Instance ord_auth_rupd : auth_rupd (ordUR) := {| *)
(*     auth_rupd_discrete := _; *)
(*     auth_rupd_rel := ord_lt; *)
(*     auth_rupd_next := succ_def; *)
(*     auth_rupd_rel_wf := wf_ord_lt; *)
(*     auth_rupd_rel_proper := _; *)
(*     auth_rupd_rel_frame := ord_auth_step_frame; *)
(*     auth_rupd_op_cancel := ord_auth_op_cancel; *)
(*     auth_rupd_next_step := succ_greater; *)
(*     auth_valid_trivial := ord_valid_trivial *)
(*   |}. *)

(*   Lemma tlc_split `{!tlcGS Σ} (α β: ord): *)
(*     £ (α ⊕ β) ⊣⊢ £ α ∗ £ β. *)
(*   Proof. apply rupdF_split. Qed. *)

(*   Lemma tlc_succ `{!tlcGS Σ} (α: ord): *)
(*     £ (succ α) ⊣⊢ £ (succ zero) ∗ £ α. *)
(*   Proof. *)
(*     by rewrite -tlc_split natural_addition_succ natural_addition_zero_left_id. *)
(*   Qed. *)

(*   Lemma tlc_later_strong `{!tlcGS Σ} α β P: *)
(*     β ≺ α → *)
(*     £ α -∗ (£ β -∗ ▷ |==>r P) -∗ |==>r P. *)
(*   Proof. *)
(*     intros Hlt. iIntros "H1 H2". iApply (auth_rupd_step with "[$H1 $H2]"). done. *)
(*   Qed. *)

(*   Lemma tlc_later `{!tlcGS Σ} P: *)
(*     £ (succ zero) -∗ (▷ |==>r P) -∗ |==>r P. *)
(*   Proof. *)
(*     iIntros "Hf Hupd". iApply (tlc_later_strong (succ zero) zero with "Hf [Hupd]"). *)
(*     - apply succ_greater. *)
(*     - by iIntros "_". *)
(*   Qed. *)

(*   Lemma tlc_laterN `{!tlcGS Σ} P n : *)
(*     £(Nat.iter n succ_def zero) -∗ (▷^n |==>r P) -∗ |==>r P. *)
(*   Proof. *)
(*     iIntros "Hc Hu". iInduction n as [ | n ] "IH"; first done. *)
(*     simpl. rewrite tlc_succ. iDestruct "Hc" as "[Hc0 Hc]". *)
(*     iApply (tlc_later with "Hc0"). *)
(*     iNext. iApply ("IH" with "Hc Hu"). *)
(*   Qed. *)

(*   Lemma tlc_weaken `{!tlcGS Σ} (α β: ord): *)
(*     β ⪯ α → (£ α -∗ |==>r £ β). *)
(*   Proof. *)
(*     intros Hle. iIntros "H". iApply (auth_rupd_weaken with "H"). done. *)
(*   Qed. *)

(*   Lemma tlc_zero `{!tlcGS Σ}: ⊢ |==> £ zero. *)
(*   Proof. *)
(*     iApply own_unit. *)
(*   Qed. *)


(*   Lemma tlc_loeb `{!tlcGS Σ} P `{!CreditExchange Σ (ordUR) P}: *)
(*     □ ((£(succ zero) -∗ P) → P) ⊢ P. *)
(*   Proof. *)
(*     exact (credit_ind Σ (ordUR) P). *)
(*   Qed. *)

(* End transfinite_lc. *)
