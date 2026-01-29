From iris.proofmode Require Import base proofmode classes.
From liris Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From liris.base_logic Require Export fancy_updates.
From liris.program_logic Require Export gupd weakestpre.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.
Import uPred.

(* Update gproto's thread pool. *)
Definition gtp `{SI : indexT} `{!lirisGS Λ Σ} Θ1 Θ2 : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ (Ω : ghost_locks) (W : witnesses),
     (gproto Ω W Θ1) ={∅}=∗ (gproto Ω W Θ2) ∗ P)%I.

Notation "'@={' Θ1 , Θ2 '}=>' P" := (gtp Θ1 Θ2 P) (at level 99, P at level 200, format "@={ Θ1 , Θ2 }=>  P").

Section gtp.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  Global Instance gtp_ne Θ1 Θ2 :
    NonExpansive (gtp Θ1 Θ2).
  Proof.
    intros n P1 P2 HP. rewrite /gtp. do 10 (f_equiv || done).
  Qed.
  Global Instance gtp_proper Θ1 Θ2 :
    Proper ((≡) ==> (≡)) (gtp Θ1 Θ2).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply gtp_ne. apply equiv_dist. done.
  Qed.

  Lemma gtp_mono Θ1 Θ2 P Q : (P ⊢ Q) → (@={Θ1,Θ2}=> P) ⊢ (@={Θ1,Θ2}=> Q).
  Proof.
    intros Hent. rewrite /gtp. iIntros "P % % I".
    iMod ("P" with "I") as "[$ H]". iModIntro.
    by iApply Hent.
  Qed.
  Lemma gtp_wand_l Θ1 Θ2 P Q : (P -∗ Q) ∗ (@={Θ1,Θ2}=> P) ⊢ (@={Θ1,Θ2}=> Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /gtp. iIntros "% % I".
    iMod ("P" with "I") as "($& P)". iModIntro.
    by iApply "PQ".
  Qed.

  Global Instance gtp_ent_proper Θ1 Θ2 : Proper ((⊢) ==> (⊢)) (gtp Θ1 Θ2).
  Proof. intros P Q PQ. by apply gtp_mono. Qed.
  Global Instance gtp_flip_ent_proper Θ1 Θ2 : Proper (flip (⊢) ==> flip (⊢)) (gtp Θ1 Θ2).
  Proof. intros P Q PQ; by apply gtp_mono. Qed.
  Global Instance gtp_equiv_proper Θ1 Θ2 : Proper ((≡) ==> (≡)) (gtp Θ1 Θ2) := ne_proper _.

  Global Instance elim_gtp (p : bool) Θ1 Θ2 P Q :
    ElimModal True p false (@={Θ1,Θ2}=> P) P (@={Θ1,Θ2}=> Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (gtp_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_gtp Θ1 Θ2 P : (|={∅}=> @={Θ1,Θ2}=> P) ⊢ @={Θ1,Θ2}=> P.
  Proof.
    rewrite /gtp. iIntros "H % % IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_gtp (p : bool) Θ1 Θ2 P Q :
    ElimModal True p false (|={∅}=> P) P (@={Θ1,Θ2}=> Q) (@={Θ1,Θ2}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_gtp. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

  (** Relation with gprog *)
  Lemma gtp_gprog Θ1 Θ2 i P :
    (@={Θ1,Θ2}=> @={Θ2,Θ2,i}=↓ P)
    ⊢ @={Θ1,Θ2,i}=↓ P.
  Proof.
    iIntros "H %% I". iMod ("H" with "I") as "[I H]". iApply ("H" with "I").
  Qed.

End gtp.

(** Predicates we take the fixpoint of in order to define the tWP. *)
Definition twp_step `{SI : indexT} `{!lirisGS Λ Σ}
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ Θ σ1 κ κs,
      (state_interp σ1 Θ (κ ++ κs)) ={E,∅}=∗
      |=[Θ]=>g
      (⌜if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
      ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
      @={Θ,(Θ ∪ dom efs)}=>
      (|=[(Θ ∪ dom efs)]=>g
       |={∅,E}=> (state_interp σ2 (Θ ∪ dom efs) κs) ∗ ν e2 efs))%I.

Section twp_step.

  Global Instance twp_step_ne `{SI : indexT} `{!lirisGS Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (twp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /twp_step.
    do 30 (f_equiv || done).
  Qed.
  Global Instance twp_step_proper `{SI : indexT} `{!lirisGS Λ Σ} s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (twp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply twp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma twp_step_mono `{SI : indexT} `{!lirisGS Λ Σ} s
    (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, twp_step s i E e ν1 -∗ twp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /twp_step.
    iIntros (????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp". iModIntro. iMod "Hwp" as "($& Hwp)".
    iModIntro.
    iIntros (???) "H0".
    iDestruct ("Hwp" with "[$]") as ">>Hwp".
    iModIntro. iMod "Hwp" as "Hwp".
    iModIntro. iDestruct "Hwp" as "[$ H]".
    by iApply "Hmono".
  Qed.

  Lemma fupd_twp_step `{SI : indexT} `{!lirisGS Λ Σ} s i E e twp :
    (|={E}=> twp_step s i E e twp) ⊢ twp_step s i E e twp.
  Proof.
    iIntros "Hf". rewrite /twp_step.
    iMod "Hf" as "Hf". done.
  Qed.

End twp_step.

(* pre-definition of twp of which we take a least fixpoint *)
(** lwp proofs for forked off threads. *)
Definition twp_pre `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness)
  (twp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => (|={E}=>g Φ v)
     | None => (twp_step s i E e1 (λ e2 efs, (twp i E e2 Φ) ∗
                                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     end)%I.

Lemma twp_pre_mono `{SI : indexT} `{!lirisGS Λ Σ} s
  (twp1 twp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, twp1 i E e Φ -∗ twp2 i E e Φ) →
     ∀ i E e Φ, twp_pre s twp1 i E e Φ -∗ twp_pre s twp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Htwp". rewrite /twp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (twp_step_mono with "[] Htwp"). iModIntro.
  iIntros (e efs) "[Htwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  auto.
Qed.

(* Uncurry [twp_pre] and equip its type with an OFE structure *)
Definition twp_pre' `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ twp_pre s ∘ curry4.

Local Instance twp_pre_mono' `{SI : indexT} `{!lirisGS Λ Σ} s :
  BiMonoPred (twp_pre' s).
Proof.
  constructor.
  - iIntros (twp1 twp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply twp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros twp Htwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /twp_pre /twp_step.
    do 26 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition twp_def `{SI : indexT} `{!lirisGS Λ Σ} : Twp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, ((bi_least_fixpoint (twp_pre' s)) (i,E,e,Φ))%I.
Local Definition twp_aux : seal (@twp_def). by eexists. Qed.
Definition twp' := twp_aux.(unseal).
Global Arguments twp' {SI Λ Σ _}.
Global Existing Instance twp'.
Local Lemma twp_unseal `{SI : indexT} `{!lirisGS Λ Σ} : twp = @twp_def SI Λ Σ _.
Proof. rewrite -twp_aux.(seal_eq) //. Qed.

Section twp.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma twp_pre_twp_pre' s _twp i E e Φ :
  twp_pre s _twp i E e Φ = twp_pre' s (λ '(i,E,e,Φ), _twp i E e Φ) (i,E,e,Φ).
Proof. rewrite /twp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.
Lemma twp_unfold s i E e Φ :
  tWP e @ s; i; E {{ Φ }} ⊣⊢ (twp_pre s (twp (PROP:=iProp Σ) s) i E e Φ).
Proof.
  rewrite twp_unseal. rewrite twp_pre_twp_pre' /twp_def.
  rewrite (least_fixpoint_unfold (twp_pre' s)). iSplit; iIntros "H".
  - iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. done.
  - iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. done.
Qed.

(* Lemma twp_cond s i E e Φ : *)
(*   twp e @ s; i; E {{ Φ }} ⊣⊢ (ς -∗ twp e @ s; emp; i; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite !twp_unfold. iSplit; iIntros "H Hc". *)
(*   - iIntros "_". by iApply "H". *)
(*   - by iApply ("H" with "Hc"). *)
(* Qed. *)
(* Lemma twp_cond_intro s i E e Φ : *)
(*   (ς -∗ twp e @ s; emp; i; E {{ Φ }}) -∗ twp e @ s; i; E {{ Φ }}. *)
(* Proof. *)
(*   rewrite (twp_cond _ ς). iIntros "H Hc". by iApply "H". *)
(* Qed. *)
(* Lemma twp_cond_elim s i E e Φ : *)
(*   twp e @ s; i; E {{ Φ }} -∗ ς -∗ twp e @ s; emp; i; E {{ Φ }}. *)
(* Proof. *)
(*   rewrite (twp_cond _ ς). iIntros "H Hc". by iApply "H". *)
(* Qed. *)

Lemma twp_ind_strong s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, twp_pre s (λ i E e Φ, Ψ i E e Φ ∧ tWP e @ s; i; E {{ Φ }}) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, tWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (i e E Φ) "H". rewrite twp_unseal.
  set (Ψ' := uncurry4 Ψ :
         prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[[i1 E1] e1] Φ1] [[[i2 E2] e2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=.
    etransitivity; first apply HΨ, H2. done. }
  iApply (least_fixpoint_ind _ Ψ' with "[] H").
  iIntros "!#" ([[[? ?] ?] ?]) "H". iApply "IH". rewrite twp_pre_twp_pre'.
  iApply (bi_mono_pred with "[] H").
  { repeat intro. do 3 (f_equiv || done). }
  { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
    inv H0; simpl in *. inv H1; simpl in *. inv H0; simpl in *.
    apply leibniz_equiv in H3, H1, H4. subst. f_equiv.
    { f_equiv. done. }
    { rewrite /twp_def. f_equiv. done. }
  }
  iIntros "!>" (?) "H". destruct x as [[[? ?] ?] ?].
  iSplit.
  - iDestruct "H" as "[H _]". done.
  - iDestruct "H" as "[_ H]". done.
Qed.

Lemma twp_ind s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, twp_pre s (λ i E e Φ, Ψ i E e Φ) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, tWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply twp_ind_strong. iIntros "!>" (i e E Φ) "Hrwp".
  iApply "H". iApply (twp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (i E e Φ) "[$ _]".
Qed.

Global Instance twp_ne s i E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (twp (PROP:=iProp Σ) s i E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !twp_unseal /twp_def.
  by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance twp_proper s i E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (twp (PROP:=iProp Σ) s i E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply twp_ne=>v; apply equiv_dist.
Qed.

(* Global Instance twp_ne_2 s i E e Φ n : *)
(*   Proper ((dist n) ==> dist n) (λ ς, twp (PROP:=iProp Σ) s i E e Φ). *)
(* Proof. *)
(*   intros ?? HΦ. rewrite !twp_unseal /twp_def. f_equiv. done. *)
(* Qed. *)
(* Global Instance twp_proper_2 s i E e Φ : *)
(*   Proper ((≡) ==> (≡)) (λ ς, twp (PROP:=iProp Σ) s i E e Φ). *)
(* Proof. *)
(*   intros ???. apply equiv_dist=>n. apply twp_ne_2. by apply equiv_dist. *)
(* Qed. *)

Lemma sfgupd_elim_twp s i E e Φ :
  (|={E}=>g tWP e @ s; i; E {{ Φ }}) ⊢ tWP e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply twp_unfold. rewrite /twp_pre /twp_step.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (???) "SI". iMod ("H" with "SI") as "[SI H]".
    rewrite twp_unfold /twp_pre /twp_step. rewrite Heqo.
    iMod ("H" with "SI") as "H". iModIntro. done.
  }
  iIntros (????) "SI". iMod ("H" with "SI") as "H".
  iModIntro. iMod "H" as ">[SI H]".
  rewrite twp_unfold /twp_pre /twp_step. rewrite Heqo.
  iMod ("H" with "SI") as "H". iModIntro. iMod "H" as "[$ H]".
  iModIntro. done.
Qed.

Lemma twp_value_fupd' s i E Φ v :
  tWP of_val v @ s; i; E {{ Φ }} ⊣⊢ (|={E}=>g (Φ v)).
Proof.
  iSplit; iIntros "H".
  - rewrite twp_unfold /twp_pre to_of_val. done.
  - rewrite twp_unfold /twp_pre to_of_val. done.
Qed.

Lemma twp_stuckness_mono s1 s2 i E e Φ :
  s1 ⊑ s2 →
  tWP e @ s1; i; E {{ Φ }} -∗ tWP e @ s2; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iRevert (i e E Φ) "H".
  iApply twp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
  rewrite !twp_unfold /twp_pre /=.
  destruct (to_val e) as [v|] eqn:?; first done.
  iIntros (????) "H". iMod ("IH" with "[$]") as "H".
  iModIntro. iMod "H" as "[% IH]".
  iModIntro. iSplit; [by destruct s1, s2|clear H0].
  iIntros (????). iMod ("IH" with "[//]") as ">IH".
  iModIntro.
  iMod "IH" as "($& [IH Efs])". iDestruct "IH" as "[IH _]".
  iModIntro. iFrame.
  iApply (big_sepM_impl with "Efs"). iIntros "!>" (k ef _).
  iIntros "H". iApply (lwp_stuckness_mono with "H"). auto.
Qed.

Lemma twp_strong_mono_sfgupd s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  twp e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v -∗ |={E2}=>g Ψ v) -∗ twp e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
  iApply twp_ind_strong; [solve_proper| ].
  iIntros "!>" (i e E1 Φ) "IH % %HE HΦ".
  rewrite !twp_unfold /twp_pre /=.
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
    iIntros "[_ H]". by iApply (twp_stuckness_mono with "H").
Qed.

Lemma twp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  twp e @ s1; i; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ twp e @ s2; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iApply (twp_strong_mono_sfgupd with "H [HΦ]"). all: auto.
  iIntros "% H". iMod ("HΦ" with "H") as "$". done.
Qed.

Lemma fupd_twp s i E e Φ :
  (|={E}=> twp e @ s; i; E {{ Φ }}) ⊢ twp e @ s; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply sfgupd_elim_twp. iMod "H". by iModIntro.
Qed.
Lemma twp_fupd s i E e Φ :
  twp e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ twp e @ s; i; E {{ Φ }}.
Proof. iIntros "H". iApply (twp_strong_mono s s i E with "H"); auto. Qed.

Lemma twp_sfgupd s i E e Φ :
  twp e @ s; i; E {{ v, |={E}=>g Φ v }} ⊢ twp e @ s; i; E {{ Φ }}.
Proof. iIntros "H". iApply (twp_strong_mono_sfgupd s s i E with "H"); auto. Qed.

Lemma twp_atomic s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> twp e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})
  ⊢ twp e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !twp_unfold /twp_pre.
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
  - rewrite !twp_unfold /twp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iMod ("H" with "SI") as "H".
      iModIntro. iMod "H" as ">(SI& >H)". iFrame "Efs SI".
      iModIntro. iModIntro. done.
    + iMod ("H" $! _ _ [] _ with "SI") as "H".
      iModIntro. iMod "H" as "[Red H]".
      iDestruct "Red" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ _ _ STEP).
  - destruct (atomic _ _ _ _ _ _ _ STEP) as [v <-%of_to_val].
    rewrite twp_value_fupd'. iMod ("H" with "SI") as "H".
    iModIntro. iMod "H". iModIntro.
    iMod "H" as "(SI& >H)". iModIntro. iFrame.
    iApply twp_value_fupd'. iModIntro. done.
Qed.

Lemma twp_step_fupd s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1,E2}=> |={E2,E1}=> P) ∗
   twp e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  twp e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (? ?) "[HP Hwp]". iApply (twp_strong_mono with "Hwp"); [done..|].
  iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
Qed.

Lemma twp_bind K `{!LanguageCtx K} s i E e Φ :
  (twp e @ s; i; E {{ v, twp K (of_val v) @ s; i; E {{ Φ }} }})
  ⊢ twp K e @ s; i; E {{ Φ }}.
Proof.
  revert Φ.
  cut (∀ Φ', twp e @ s; i; E {{ Φ' }} -∗ ∀ Φ, (∀ v, (Φ' v) -∗ (twp K (of_val v) @ s; i; E {{ Φ }})) -∗ twp K e @ s; i; E {{ Φ }}).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (i e E Φ') "H".
  iApply twp_ind_strong; first solve_proper.
  iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /twp_pre /twp_step. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply sfgupd_elim_twp.
    iIntros (???) "SI". iMod ("IH" with "SI") as "[SI IH]".
    iModIntro. iFrame. by iApply "HΦ".
  }
  rewrite twp_unfold /twp_pre /twp_step fill_not_val; last auto.
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

Lemma twp_bind_inv K `{!LanguageCtx K} s i E e Φ :
  twp K e @ s; i; E {{ Φ }} ⊢ twp e @ s; i; E {{ v, twp K (of_val v) @ s; i; E {{ Φ }} }}.
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (i e' E Φ) "H". iApply twp_ind_strong; first solve_proper.
  iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->).
  rewrite !twp_unfold {2}/twp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-.
    iModIntro. rewrite !twp_unfold.
    iApply (twp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]".
  }
  rewrite /twp_pre fill_not_val; [|done].
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
Lemma twp_mono s i E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → twp e @ s; i; E {{ Φ }} ⊢ twp e @ s; i; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (twp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma twp_stuck_mono s1 s2 i E e Φ :
  s1 ⊑ s2 → twp e @ s1; i; E {{ Φ }} ⊢ twp e @ s2; i; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (twp_strong_mono with "H"); auto. Qed.
Lemma twp_stuck_weaken s i E e Φ :
  twp e @ s; i; E {{ Φ }} ⊢ twp e @ i; E ?{{ Φ }}.
Proof. apply twp_stuck_mono. by destruct s. Qed.
Lemma twp_mask_mono s i E1 E2 e Φ : E1 ⊆ E2 → twp e @ s; i; E1 {{ Φ }} ⊢ twp e @ s; i; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (twp_strong_mono with "H"); auto. Qed.
Global Instance twp_mono' s i E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (twp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply twp_mono. Qed.
Global Instance twp_flip_mono' s i E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (twp (PROP:=iProp Σ) s i E e).
Proof. by intros Φ Φ' ?; apply twp_mono. Qed.

Lemma twp_value_sfgupd s i E Φ e v :
  IntoVal e v →
  twp e @ s; i; E {{ Φ }} ⊣⊢ (|={E}=>g (Φ v)).
Proof. intros <-. by apply twp_value_fupd'. Qed.
Lemma twp_value' s i E Φ v : (Φ v) ⊢ twp (of_val v) @ s; i; E {{ Φ }}.
Proof.
  rewrite twp_value_fupd'. iIntros "H". by iApply sfgupd_intro.
Qed.
Lemma twp_value s i E Φ e v : IntoVal e v → (Φ v) ⊢ twp e @ s; i; E {{ Φ }}.
Proof. intros <-. apply twp_value'. Qed.

Lemma twp_frame_l s i E e Φ R :
  R ∗ twp e @ s; i; E {{ Φ }} ⊢ twp e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.
Lemma twp_frame_r s i E e Φ R :
  twp e @ s; i; E {{ Φ }} ∗ R ⊢ twp e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the twp or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma twp_step_fupd_2 s i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1∖E2,∅}=> |={∅,E1∖E2}=> P) ∗
   twp e @ s; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  twp e @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (twp_step_fupd with "[H]"); [done|].
  iApply (sep_mono_l with "H"). iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply fupd_mask_frame; [|iMod "HP"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.

Lemma twp_frame_step_l s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1,E2}=> |={E2,E1}=> R) ∗ twp e @ s; i; E2 {{ Φ }} ⊢ twp e @ s; i; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply twp_step_fupd; first done.
  iFrame "Hu". iApply (twp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma twp_frame_step_r s i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  twp e @ s; i; E2 {{ Φ }} ∗ (|={E1,E2}=> |={E2,E1}=> R) ⊢ twp e @ s; i; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(twp _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply twp_frame_step_l.
Qed.
Lemma twp_frame_step_l' s i E e Φ R :
  TCEq (to_val e) None →
  R ∗ twp e @ s; i; E {{ Φ }} ⊢ twp e @ s; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (twp_frame_step_l s i E E); try iFrame; eauto. Qed.
Lemma twp_frame_step_r' s i E e Φ R :
  TCEq (to_val e) None →
  twp e @ s; i; E {{ Φ }} ∗ R ⊢ twp e @ s; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (twp_frame_step_r s i E E); try iFrame; eauto. Qed.

Lemma twp_wand s i E e Φ Ψ :
  twp e @ s; i; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ twp e @ s; i; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (twp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma twp_wand_l s i E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ twp e @ s; i; E {{ Φ }} ⊢ twp e @ s; i; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (twp_wand with "Hwp H"). Qed.
Lemma twp_wand_r s i E e Φ Ψ :
  twp e @ s; i; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ twp e @ s; i; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (twp_wand with "Hwp H"). Qed.
Lemma twp_frame_wand s i E e Φ R :
  R -∗ twp e @ s; i; E {{ v, R -∗ Φ v }} -∗ twp e @ s; i; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (twp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End twp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_twp p s i E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (twp e @ s; i; E {{ Φ }}) (twp e @ s; i; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite twp_frame_l. apply twp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_twp s i E e Φ : IsExcept0 (twp e @ s; i; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_twp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_twp p s i E e P Φ :
    ElimModal True p false (|==> P) P (twp e @ s; i; E {{ Φ }}) (twp e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_twp.
  Qed.

  Global Instance elim_modal_fupd_twp p s i E e P Φ :
    ElimModal True p false (|={E}=> P) P (twp e @ s; i; E {{ Φ }}) (twp e @ s; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_twp.
  Qed.

  Global Instance elim_modal_sfgupd_twp p s i E e P Φ :
    ElimModal True p false (|={E}=>g P) P (twp e @ s; i; E {{ Φ }}) (twp e @ s; i; E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (_) "[P H]". iApply sfgupd_elim_twp. iMod "P".
    iModIntro. by iApply ("H" with "P").
  Qed.

  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_twp_wrong_mask p s i E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_twp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (twp e @ s; i; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_twp_atomic p s i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (twp e @ s; i; E1 {{ Φ }}) (twp e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r twp_atomic.
  Qed.

  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_twp_atomic_wrong_mask p s i E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (twp e @ s; i; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_twp s i E e P Φ :
    AddModal (|={E}=> P) P (twp e @ s; i; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_twp. Qed.

  Global Instance add_modal_ghost_step_twp s i E e P Φ :
    AddModal (|={E}=>g P) P (twp e @ s; i; E {{ Φ }}).
  Proof. rewrite /AddModal. iIntros "[H1 H2]". iMod "H1". by iApply "H2". Qed.

  Global Instance elim_acc_twp_atomic {X} i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (twp e @ s; i; E1 {{ Φ }})
            (λ x, twp e @ s; i; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (twp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_twp_nonatomic {X} i E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (twp e @ s; i; E {{ Φ }})
            (λ x, twp e @ s; i; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply twp_fupd.
    iApply (twp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
