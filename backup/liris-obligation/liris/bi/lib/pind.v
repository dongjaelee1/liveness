From iris.bi Require Export bi fixpoint.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(** ** Predicates of Arity 1 *)

Section Arg1_def.

  Context `{SI : indexT}.
  Context {PROP : bi}.

  Variable T : ofe.
  (* Notation rel1 := (∀ (x : T), PROP). *)
  Notation rel1 := (T -d> PROP).
  Variable gf : rel1 -> rel1.
  Arguments gf : clear implicits.
  Notation "p <1= q" := (∀ x, p x -∗ q x)%I (at level 50, no associativity).
  Notation "p ∗1 q" := (λ x, p x ∗ q x)%I (at level 50, no associativity).
  Notation "p /1\ q" := (λ x, p x ∧ q x)%I (at level 50, no associativity).

  Definition pind_pre (pind : rel1 → T → PROP) : rel1 → T → PROP :=
    (λ r x, ∃ (ϕ : T → PROP), (ϕ <1= (pind r /1\ r)) ∗ (gf ϕ x))%I.

  Lemma pind_pre_mono (pind1 pind2 : rel1 → T → PROP) :
    ⊢ ((□ ∀ r x, pind1 r x -∗ pind2 r x) →
       ∀ r x, pind_pre pind1 r x -∗ pind_pre pind2 r x)%I.
  Proof.
    iIntros "#H"; iIntros (r x) "Hpind". rewrite /pind_pre.
    iDestruct "Hpind" as "(%ϕ&Hpind&Hgf)".
    iExists ϕ. iFrame. iIntros (x0) "Hx0". iSpecialize ("Hpind" with "Hx0").
    iSplit.
    - iDestruct "Hpind" as "[Hp _]". by iApply "H".
    - iDestruct "Hpind" as "[_ Hp]". done.
  Qed.

  Definition pind_pre' : ((prodO rel1 (leibnizO T)) → PROP) → (prodO rel1 (leibnizO T)) → PROP := uncurry ∘ pind_pre ∘ curry.

  Local Instance pind_pre_mono' : BiMonoPred pind_pre'.
  Proof.
  constructor.
  - iIntros (pind1 pind2 NE1 NE2) "#H"; iIntros ([r x]); iRevert (r x).
    iApply pind_pre_mono. iIntros "!#" (r x). iApply ("H" $! (r, x)).
  - intros pind Hpind n [r1 x1] [r2 x2]. intros H. inv H. simplify_eq/=.
    rewrite /uncurry /pind_pre. do 7 (f_equiv || done).
    + rewrite /curry. f_equiv. constructor; simpl; auto.
    + f_equiv.
  Qed.

  Definition pind (r : rel1) (x : T) : PROP := bi_least_fixpoint (pind_pre') (r, x).
  Definition pind_aux : seal (pind). by eexists. Qed.

  Lemma pind_unfold r x :
    pind r x ⊣⊢ pind_pre pind r x.
  Proof. by rewrite /pind least_fixpoint_unfold. Qed.

  Definition upind (r : rel1) := pind r ∗1 r.

  Theorem pind_acc : ∀ l r,
    (□ ∀ rr, (rr <1= r) -∗ (rr <1= l) -∗ pind rr <1= l)
      ⊢
    (pind r <1= l).
  Proof.
    iIntros (l r) "#IH". iIntros (x) "H".
    iAssert (pind (r /1\ l) x) with "[H]" as "H".
    { iRevert "IH".
      iPoseProof (least_fixpoint_ind pind_pre'
                    ((λ '(r, x), □ (∀ rr : T → PROP, rr <1= r -∗ rr <1= l -∗ pind rr <1= l) -∗ pind (r /1\ l) x)%I)
                   with "[] [H]") as "HH".
      2:{ iApply "H". }
      2:{ simpl. done. }
      clear r x. iModIntro. iIntros ([r x]) "H". iIntros "#IH". simpl.
      iDestruct "H" as "(%ϕ&H&Hgf)". rewrite /curry.
      iEval (rewrite pind_unfold). iExists ϕ. iFrame.
      iIntros (x0) "Hp". iSpecialize ("H" with "Hp"). iSplit; [|iSplit].
      - iDestruct "H" as "[[H _] _]".  iApply "H". done.
      - iDestruct "H" as "[_ H]". done.
      - iAssert (∀ rr : T → PROP, rr <1= r -∗ rr <1= l -∗ pind rr <1= l)%I as "IH2".
        { done. }
        iSpecialize ("IH" $!(r /1\ l)). iApply ("IH" with "[] [] [H]").
        + iIntros (?) "[H _]". done.
        + iIntros (?) "[_ H]". done.
        + iDestruct "H" as "[[H _] _]". iApply "H". iModIntro. done.
    }
    iApply ("IH" $!(r /1\ l) with "[] [] H").
    - iIntros (?) "[H _]". done.
    - iIntros (?) "[_ H]". done.
      Unshelve.
      intros n [r1 x1] [r2 x2]. intros. inv H. simplify_eq/=.
      (* rewrite H1. *)
      do 1 f_equiv.
      { do 8 f_equiv. }
      { rewrite /pind. f_equiv. constructor; simpl; auto.
        solve_proper.
      }
  Qed.


  (* Definition pind_pre (pind : rel1 → T → PROP) : rel1 → T → PROP := *)
  (*   (λ r x, ∃ (ϕ : T → PROP), (ϕ <1= (pind r ∗1 r)) ∗ (gf ϕ x))%I. *)

  (* Lemma pind_pre_mono (pind1 pind2 : rel1 → T → PROP) : *)
  (*   ⊢ ((□ ∀ r x, pind1 r x -∗ pind2 r x) → *)
  (*      ∀ r x, pind_pre pind1 r x -∗ pind_pre pind2 r x)%I. *)
  (* Proof. *)
  (*   iIntros "#H"; iIntros (r x) "Hpind". rewrite /pind_pre. *)
  (*   iDestruct "Hpind" as "(%ϕ&Hpind&Hgf)". *)
  (*   iExists ϕ. iFrame. iIntros (x0) "Hx0". iSpecialize ("Hpind" with "Hx0"). iDestruct "Hpind" as "[Hpind Hr]". *)
  (*   iFrame. iApply "H". done. *)
  (* Qed. *)

  (* Definition pind_pre' : ((prodO rel1 (leibnizO T)) → PROP) → (prodO rel1 (leibnizO T)) → PROP := uncurry ∘ pind_pre ∘ curry. *)

  (* Local Instance pind_pre_mono' : BiMonoPred pind_pre'. *)
  (* Proof. *)
  (* constructor. *)
  (* - iIntros (pind1 pind2 NE1 NE2) "#H"; iIntros ([r x]); iRevert (r x). *)
  (*   iApply pind_pre_mono. iIntros "!#" (r x). iApply ("H" $! (r, x)). *)
  (* - intros pind Hpind n [r1 x1] [r2 x2]. intros H. inv H. simplify_eq/=. *)
  (*   rewrite /uncurry /pind_pre. do 7 (f_equiv || done). *)
  (*   + rewrite /curry. f_equiv. constructor; simpl; auto. *)
  (*   + f_equiv. *)
  (* Qed. *)

  (* Definition pind (r : rel1) (x : T) : PROP := bi_least_fixpoint (pind_pre') (r, x). *)
  (* Definition pind_aux : seal (pind). by eexists. Qed. *)

  (* Lemma pind_unfold r x : *)
  (*   pind r x ⊣⊢ pind_pre pind r x. *)
  (* Proof. by rewrite /pind least_fixpoint_unfold. Qed. *)

  (* Lemma pind_proper *)
  (*   r (P : T → PROP) *)
  (*   : *)
  (*   (□ (∀ x ϕ, (ϕ <1= ((pind r /1\ P) ∗1 r)) -∗ *)
  (*              (gf ϕ x) -∗ *)
  (*              P x)) *)
  (*   ⊢ *)
  (*     ∀ x, pind r x -∗ P x. *)
  (* Proof. *)
  (*   iIntros "#IH" (x) "H". *)
  (*   rewrite /pind. *)
  (*   set (P' := λ (x : (rel1 * T)%type), P x.2). *)
  (*   set (P'' := P' : prodO rel1 (leibnizO T) → PROP). *)
  (*   (* replace (P x) with (P'' (r, x)). *) *)
  (*   (* 2:{ subst P'' P'. done. } *) *)
  (*   assert (NEP : NonExpansive P''). *)
  (*   { subst P'' P'. simpl. intros n [r1 x1] [r2 x2]. intros. inv H. simplify_eq/=. rewrite H1. done. } *)
  (*   iRevert "IH". *)
  (*   iPoseProof (least_fixpoint_ind pind_pre' *)
  (*     ((λ '(r, x), □ (∀ (x0 : T) (ϕ : T → PROP), (∀ x1 : T, ϕ x1 -∗ (bi_least_fixpoint pind_pre' (r, x1) ∧ P x1) ∗ r x1) -∗ gf ϕ x0 -∗ P x0) -∗ P x))%I *)
  (*                with "[] [H]") as "HH". *)
  (*   (* iPoseProof (least_fixpoint_ind pind_pre' *) *)
  (*   (*   ((λ '(r, x), □ (∀ (x0 : T) (ϕ : T → PROP), (∀ x1 : T, ϕ x1 -∗ (bi_least_fixpoint pind_pre' (r, x1) ∗ r x1) ∗ P x1) -∗ gf ϕ x0 -∗ P x0) -∗ P x))%I *) *)
  (*   (*              with "[] [H]") as "HH". *) *)
  (*   2:{ iApply "H". } *)
  (*   2:{ simpl. done. } *)
  (*   clear r x. iModIntro. iIntros ([r x]) "H". iIntros "#IH". simpl. *)
  (*   iDestruct "H" as "(%ϕ&H&Hgf)". rewrite /curry. *)
  (*   iApply ("IH" with "[H] Hgf"). *)
  (*   iIntros (x0) "Hp". iSpecialize ("H" with "Hp"). iDestruct "H" as "[H Hr]". *)
  (*   iFrame. iSplit. *)
  (*   { iDestruct "H" as "[_ H]". done. } *)
  (*   { iDestruct "H" as "[H _]". iApply "H". done. } *)
  (*   Unshelve.  *)
  (*   intros n [r1 x1] [r2 x2]. intros. inv H. simplify_eq/=. rewrite H1. *)
  (*   do 13 f_equiv. constructor; done. *)
  (* Qed. *)

  (* Definition upind (r : rel1) := pind r ∗1 r. *)

  (* Theorem pind_acc : ∀ l r, *)
  (*   (□ ∀ rr, (rr <1= r) -∗ (rr <1= l) -∗ pind rr <1= l) *)
  (*     ⊢ *)
  (*   (pind r <1= l). *)
  (* Proof. *)
  (*   iIntros (l r) "#IH". iIntros (x) "H". *)
  (*   iAssert (pind (r /1\ l) x) with "[H]" as "H". *)
  (*   { iRevert "IH". *)
  (*     iPoseProof (least_fixpoint_ind pind_pre' *)
  (*                   ((λ '(r, x), □ (∀ rr : T → PROP, rr <1= r -∗ rr <1= l -∗ pind rr <1= l) -∗ pind (r /1\ l) x)%I) *)
  (*                  with "[] [H]") as "HH". *)
  (*     2:{ iApply "H". } *)
  (*     2:{ simpl. done. } *)
  (*     clear r x. iModIntro. iIntros ([r x]) "H". iIntros "#IH". simpl. *)
  (*     iDestruct "H" as "(%ϕ&H&Hgf)". rewrite /curry. *)
  (*     iEval (rewrite pind_unfold). iExists ϕ. iFrame. *)
  (*     iIntros (x0) "Hp". iSpecialize ("H" with "Hp"). iDestruct "H" as "[H Hr]". *)

  (* Lemma pind_strong_ind Ψ : *)
  (*   ⊢ (□ (∀ r x, pind_pre s (λ E e Φ, Ψ E e Φ ∧ PIND e @ s; E ⟨⟨ Φ ⟩⟩) E e Φ -∗ Ψ E e Φ) *)
  (*      → ∀ e E Φ, PIND e @ s; E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I. *)
  (* Proof. *)
  (*   iIntros (HΨ). iIntros "#IH" (e E Φ) "H". rewrite pind_eq. *)
  (*   set (Ψ' := curry3 Ψ : *)
  (*          prodO (prodO (leibnizO SI coPset) (exprO SI Λ)) (val Λ -d> iProp Σ) → iProp Σ). *)
  (*   assert (NonExpansive Ψ'). *)
  (*   { intros n [[E1 e1] Φ1] [[E2 e2] Φ2] *)
  (*       [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. } *)
  (*   iApply (least_fixpoint_strong_ind _ Ψ' with "[] H"). *)
  (*   iIntros "!#" ([[??] ?]) "H". by iApply "IH". *)
  (* Qed. *)

  (* Lemma pind_ind s Ψ : *)
  (*   (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) *)
  (*   → ⊢ (□ (∀ e E Φ, pind_pre s (λ E e Φ, Ψ E e Φ) E e Φ -∗ Ψ E e Φ) *)
  (*        → ∀ e E Φ, PIND e @ s; E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I. *)
  (* Proof. *)
  (*   iIntros (HΨ) "#H". iApply pind_strong_ind. iIntros "!>" (e E Φ) "Hpind". *)
  (*   iApply "H". iApply (pind_pre_mono with "[] Hpind"). clear. *)
  (*   iIntros "!>" (E e Φ) "[$ _]". *)
  (* Qed. *)



  (* Inductive pind (r: rel1 T0) x0 : Prop := *)
  (* | pind_pfold pin *)
  (*     (* (GE : (pind r /1\ r) <1= pin) *) *)
  (*     (LE : pin <1= (pind r /1\ r)) *)
  (*     (SIM: gf pin x0) *)
  (* . *)

  (* Lemma pind_proper *)
  (*   r (P: T0 -> Prop) *)
  (*   (PIND: forall x0 pin *)
  (*            (LE: pin <1= (pind r /1\ r)) *)
  (*            (IH: pin <1= P) *)
  (*            (SIM: gf pin x0), *)
  (*      P x0) *)
  (*   : *)
  (*   forall x0 (PR: pind r x0), P x0. *)
  (* Proof. *)
  (*   fix IH 2. intros. destruct PR. eapply PIND; eauto. *)
  (*   intros. apply IH. apply LE in PR. destruct PR. auto. *)
  (* Qed. *)

  (* Definition upind (r: rel1 T0) := pind r /1\ r. *)

End Arg1_def.

Arguments pind [ T0 ] gf r x0.
Arguments upind [ T0 ] gf r x0.
#[export] Hint Unfold upind : core.

(* Less than or equal - internal use only *)
Notation "p <_pind_1= q" :=
  (forall _pind_x0 (PR: p _pind_x0 : Prop), q _pind_x0 : Prop)
  (at level 50, no associativity).

(* (* coinduction automation - internal use only *) *)
(* Ltac pind_cofix_auto := *)
(*   let CIH := fresh "CIH" in cofix CIH; repeat intro; *)
(*   match goal with [H: _ |- _] => apply pind_observe in H; destruct H as [] end; do 2 econstructor; *)
(*   try (match goal with [H: _|-_] => apply H end); intros; *)
(*   lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end; *)
(*   repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10]. *)

Definition monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall r r' (LE: r <1= r'), gf r <1== gf r'.

Lemma monotone_eq T0 (gf: rel1 T0 -> rel1 T0) :
  monotone gf <-> _monotone gf.
Proof. unfold monotone, _monotone, le1. split; eauto. Qed.

Lemma pind_mon_gen T0 gf gf' r r' x
      (PR: @pind T0 gf r x)
      (LElf: gf <2= gf')
      (LEr: r <1= r'):
  pind gf' r' x.
Proof.
  generalize dependent gf'. generalize dependent r'. induction PR using pind_proper; intros.
  econstructor.
  2: eauto.
  intros. specialize (LE _ PR). destruct LE. split.
  2: eauto.
  eapply IH; eauto.
Qed.

Section Arg1.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem pind_acc: forall
  l r (OBG: forall rr (DEC: rr <1= r) (IH: rr <1= l), pind gf rr <1= l),
  pind gf r <1= l.
Proof.
  intros. assert (SIM: pind gf (r /1\ l) x0).
  { generalize dependent l. induction PR using pind_proper; intros.
    econstructor. 2: eauto.
    intros. specialize (LE _ PR). destruct LE.
    repeat split; eauto.
    eapply (OBG (r /1\ l)); eauto. all: intros x2 AND; destruct AND; eauto.
  }
  clear PR. eapply (OBG (r /1\ l)); eauto. all: intros x1 AND; destruct AND; eauto.
Qed.

Theorem pind_mon: monotone (pind gf).
Proof.
  unfold monotone. intros. generalize dependent r'. induction IN using pind_proper; intros.
  econstructor. 2: eauto.
  intros. specialize (LE _ PR). destruct LE. split; eauto.
Qed.

Theorem pind_mult_strong: forall r,
    pind gf r <1= pind gf (upind gf r).
Proof.
  intros. unfold upind. induction PR using pind_proper. econstructor. 2: eauto.
  intros. specialize (LE _ PR). destruct LE. repeat split; eauto.
Qed.

Corollary pind_mult: forall r,
    pind gf r <1= pind gf (pind gf r).
Proof.
  intros. eapply pind_mult_strong in PR. eapply pind_mon; eauto. unfold upind. intros x1 AND; destruct AND; eauto.
Qed.

Theorem pind_fold: forall r,
  gf (upind gf r) <1= pind gf r.
Proof.
  intros. econstructor. 2: eauto. intros. destruct PR0. auto.
Qed.

Theorem pind_unfold: forall (MON: monotone gf) r,
  pind gf r <1= gf (upind gf r).
Proof.
  intros. unfold upind. induction PR using pind_proper. eapply MON; eauto.
Qed.

Theorem _pind_acc: forall
  l r (OBG: forall rr (DEC: rr <1== r) (IH: rr <1== l), pind gf rr <1== l),
  pind gf r <1== l.
Proof. unfold le1. eapply pind_acc. Qed.

Theorem _pind_mon: _monotone (pind gf).
Proof. apply monotone_eq. eapply pind_mon. Qed.

Theorem _pind_mult_strong: forall r,
  pind gf r <1== pind gf (upind gf r).
Proof. unfold le1. eapply pind_mult_strong. Qed.

Theorem _pind_fold: forall r,
  gf (upind gf r) <1== pind gf r.
Proof. unfold le1. eapply pind_fold. Qed.

Theorem _pind_unfold: forall (MON: _monotone gf) r,
  pind gf r <1== gf (upind gf r).
Proof.
  unfold le1. intro.
  eapply pind_unfold; apply monotone_eq; eauto.
Qed.

End Arg1.

#[export] Hint Unfold monotone : core.
#[export] Hint Resolve pind_fold : core.

Arguments pind_mon_gen        [ T0 ] gf gf' r r' x PR LElf LEr.
Arguments pind_acc            [ T0 ] gf l r OBG x0 PR.
Arguments pind_mon            [ T0 ] gf x0 r r' IN LE.
Arguments pind_mult_strong    [ T0 ] gf r x0 PR.
Arguments pind_mult           [ T0 ] gf r x0 PR.
Arguments pind_fold           [ T0 ] gf r x0 PR.
Arguments pind_unfold         [ T0 ] gf MON r x0 PR.
