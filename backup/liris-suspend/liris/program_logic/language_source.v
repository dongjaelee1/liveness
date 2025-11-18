From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth.
From transfinite.base_logic.lib Require Export fancy_updates.

Set Default Proof Using "Type".

Class source `{SI : indexT} (Σ : gFunctors) (A : Type) := mkSource {
  source_concrete_rel : relation A;
  source_abstract_rel : relation A;
  source_interp : A → iProp Σ;
}.

Definition source_rel `{SRC : source} : relation A :=
  λ a b, source_concrete_rel a b ∨ source_abstract_rel a b.

Infix "↪" := (source_concrete_rel) (at level 60).
Infix "↪ₐ" := (source_abstract_rel) (at level 60).
Infix "↪ₒ" := (source_rel) (at level 60).

(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Infix "↪⁺" := (tc source_concrete_rel) (at level 60).
Infix "↪ₐ⁺" := (tc source_abstract_rel) (at level 60).
Infix "↪ₒ⁺" := (tc source_rel) (at level 60).

Infix "↪⋆" := (rtc source_concrete_rel) (at level 60).
Infix "↪ₐ⋆" := (rtc source_abstract_rel) (at level 60).
Infix "↪ₒ⋆" := (rtc source_rel) (at level 60).

Lemma sn_tc {X} (R : X → X → Prop) (x : X): sn R x ↔ sn (tc R) x.
Proof.
  split.
  - induction 1 as [x _ IH]; constructor; simpl; intros y Hy; revert IH; simpl.
    destruct Hy as [x y Honce|x y z Honce Hsteps]; intros IH; eauto.
    destruct (IH _ Honce) as [Hy]; eauto.
  - induction 1 as [z _ IH]; constructor; intros ??; apply IH; simpl in *; eauto using tc_once.
Qed.

Section src_update.
  Context `{SI : indexT} `{!source Σ A} `{!invGS_gen hlc Σ}.

  Definition src_concrete_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪⁺ b⌝ ∗ source_interp b ∗ P)%I.
  Definition src_abstract_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪ₐ⁺ b⌝ ∗ source_interp b ∗ P)%I.
  Definition src_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪ₒ⁺ b⌝ ∗ source_interp b ∗ P)%I.

  Definition weak_src_concrete_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪⋆ b⌝ ∗ source_interp b ∗ P)%I.
  Definition weak_src_abstract_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪ₐ⋆ b⌝ ∗ source_interp b ∗ P)%I.
  Definition weak_src_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, source_interp a -∗ |={E}=> ∃ b : A, ⌜a ↪ₒ⋆ b⌝ ∗ source_interp b ∗ P)%I.

  Lemma src_concrete_update_bind E P Q :
    src_concrete_update E P ∗ (P -∗ src_concrete_update E Q) ⊢ src_concrete_update E Q.
  Proof.
    rewrite /src_concrete_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c. iFrame. iPureIntro.
    by trans b.
  Qed.
  Lemma src_abstract_update_bind E P Q :
    src_abstract_update E P ∗ (P -∗ src_abstract_update E Q) ⊢ src_abstract_update E Q.
  Proof.
    rewrite /src_abstract_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c. iFrame. iPureIntro.
    by trans b.
  Qed.
  Lemma src_update_bind E P Q :
    src_update E P ∗ (P -∗ src_update E Q) ⊢ src_update E Q.
  Proof.
    rewrite /src_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c. iFrame. iPureIntro.
    by trans b.
  Qed.

  TODO

  Lemma src_update_mono_fupd E P Q: src_update E P ∗ (P ={E}=∗ Q) ⊢ src_update E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b; by iFrame.
  Qed.

  Lemma src_update_mono E P Q: src_update E P ∗ (P -∗ Q) ⊢ src_update E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (src_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_src_update E P : (|={E}=> src_update E P) ⊢ src_update E P.
  Proof.
    iIntros "H". rewrite /src_update. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Lemma src_update_weak_src_update E P: src_update E P ⊢ weak_src_update E P.
  Proof.
    rewrite /src_update /weak_src_update. iIntros "P" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iModIntro. iExists b. iFrame. iPureIntro.
    by apply tc_rtc.
  Qed.

  Lemma weak_src_update_return E P: P ⊢ weak_src_update E P.
  Proof.
    rewrite /src_update. iIntros "P" (a) "Ha".
    iModIntro. iExists (a). iFrame. iPureIntro.
    reflexivity.
  Qed.

  Lemma weak_src_update_bind_l E P Q: weak_src_update E P ∗ (P -∗ src_update E Q) ⊢ src_update E Q.
  Proof.
    rewrite /src_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c. iFrame. iPureIntro.
    by eapply tc_rtc_l.
  Qed.

  Lemma weak_src_update_bind_r E P Q: src_update E P ∗ (P -∗ weak_src_update E Q) ⊢ src_update E Q.
  Proof.
    rewrite /src_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c. iFrame. iPureIntro.
    by eapply tc_rtc_r.
  Qed.

  Lemma weak_src_update_bind E P Q : weak_src_update E P ∗ (P -∗ weak_src_update E Q) ⊢ weak_src_update E Q.
  Proof.
    iIntros "[H1 H2]". rewrite /weak_src_update.
    iIntros (a) "HS". iMod ("H1" with "HS") as (b Hb) "[HS HP]".
    iMod ("H2" with "HP HS") as (c Hc) "[HS HQ]". iModIntro.
    iExists c. iFrame. iPureIntro. by etrans.
  Qed.

  Lemma weak_src_update_mono_fupd E P Q: weak_src_update E P ∗ (P ={E}=∗ Q) ⊢ weak_src_update E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b; by iFrame.
  Qed.

  Lemma weak_src_update_mono E P Q: weak_src_update E P ∗ (P -∗ Q) ⊢ weak_src_update E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (weak_src_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_weak_src_update E P : (|={E}=> weak_src_update E P) ⊢ weak_src_update E P.
  Proof.
    iIntros "H". rewrite /weak_src_update. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

End src_update.


Section auth_source.

  Structure auth_source SI := {
    auth_sourceUR :> ucmraT SI;
    auth_source_discrete : CmraDiscrete auth_sourceUR;
    auth_source_trans : relation auth_sourceUR;
    auth_source_trans_proper: Proper (equiv ==> equiv ==> iff) auth_source_trans;
    auth_source_step_frame (a a' f: auth_sourceUR):
      auth_source_trans a a' → ✓ (a ⋅ f) → ✓ (a' ⋅ f) ∧ auth_source_trans (a ⋅ f) (a' ⋅ f);
    auth_source_op_cancel (a f f': auth_sourceUR):
      ✓ (a ⋅ f) → a ⋅ f ≡ a ⋅ f' → f ≡ f'
  }.
  Existing Instance auth_source_trans_proper.
  Existing Instance auth_source_discrete.

  Class auth_sourceG {SI} (Σ: gFunctors SI) (S: auth_source SI) := {
    sourceG_inG :> inG Σ (authR S);
    sourceG_name : gname;
  }.

  Global Instance source_auth_source {SI} (Σ: gFunctors SI) (S: auth_source SI) `{!auth_sourceG Σ S} : source Σ S  :=
  {|
    source_rel := auth_source_trans _ S;
    source_interp a := own sourceG_name (● a)
  |}.

  Definition srcA {SI} {Σ: gFunctors SI} (S: auth_source SI) `{!auth_sourceG Σ S} (s: S) : iProp Σ := own sourceG_name (● s).
  Definition srcF {SI} {Σ: gFunctors SI} (S: auth_source SI) `{!auth_sourceG Σ S} (s: S) : iProp Σ := own sourceG_name (◯ s).


  Section auth_updates.
    Context {SI} {Σ: gFunctors SI} (S: auth_source SI) `{!auth_sourceG Σ S}.

    Lemma source_step_update (E_s e_s e_s': S):
      ✓ E_s → e_s ≼ E_s → e_s ↪ e_s' → ∃ E_s', (E_s, e_s) ~l~> (E_s', e_s') ∧ E_s ↪ E_s'.
    Proof.
      intros Hv Hincl Hstep.
      destruct Hincl as [e_f Heq]. erewrite Heq in Hv.
      specialize (auth_source_step_frame _ S _ _ _ Hstep Hv) as [Hv' Hstep'].
      exists (e_s' ⋅ e_f). split; rewrite Heq.
      - intros α [e_f'|]; simpl; intros ? Heq'; split.
        + by apply cmra_valid_validN.
        + f_equiv. eapply discrete_iff; first apply _.
          eapply discrete_iff in Heq'; last apply _.
          eapply auth_source_op_cancel; last eauto; eauto.
        + by apply cmra_valid_validN.
        + specialize (ucmra_unit_right_id  e_s') as H'. rewrite -{2}H'. f_equiv.
          eapply discrete_iff; first apply _.
          eapply discrete_iff in Heq'; last apply _.
          eapply auth_source_op_cancel; first apply Hv.
          by rewrite ucmra_unit_right_id.
      - eapply Hstep'.
    Qed.

    Lemma auth_src_update `{!invG Σ} E s s':
      s ↪ s' → srcF S s ⊢ src_update E (srcF S s').
    Proof.
      intros Hstep. unfold src_update. iIntros "SF" (E_s). iIntros "SA".
      iCombine "SA SF" as "S".
      iPoseProof (own_valid_l with "S") as (Hv) "S".
      apply auth_both_valid in Hv as [Hincl Hv].
      eapply source_step_update in Hv as [E_s' [Hl Hstep']]; eauto.
      iMod (own_update _ _ (● E_s' ⋅ ◯ s') with "S") as "S".
      - by apply auth_update.
      - iModIntro. iExists (E_s'); iDestruct "S" as "($ & $)".
        iPureIntro; eauto using tc_once.
    Qed.


    Lemma srcF_split s t:
      srcF S (s ⋅ t) ⊣⊢ srcF S s ∗ srcF S t.
    Proof.
      rewrite /srcF -own_op auth_frag_op //=.
    Qed.
  End auth_updates.

End auth_source.

Class Credit (SI: indexT) := credit_source: auth_source SI.
Notation "$ a" := (srcF credit_source a) (at level 60).
Notation "●$ a" := (srcA credit_source a) (at level 60).


(* nat auth source *)
Section nat_auth_source.

  Context (SI: indexT).

  Lemma nat_source_step_frame (a a' f : natR SI):
    a' < a → ✓ (a ⋅ f) → ✓ (a' ⋅ f) ∧ (a' ⋅ f) < (a ⋅ f).
  Proof.
    intros Hαβ _; split; first done.
    rewrite !nat_op_plus. lia.
  Qed.

  Lemma nat_source_op_cancel (a f f' : natR SI):
      ✓ (a ⋅ f) → a ⋅ f = a ⋅ f' → f = f'.
  Proof using SI.
    intros _; rewrite !nat_op_plus. by intros H% Nat.add_cancel_l.
  Qed.


  (* we define an auth structure for ordinals *)
  Program Canonical Structure natA : auth_source SI := {|
    auth_sourceUR := natUR SI;
    auth_source_trans := flip lt;
    auth_source_discrete := _;
    auth_source_trans_proper := _;
    auth_source_step_frame := nat_source_step_frame;
    auth_source_op_cancel := nat_source_op_cancel
  |}.

  Lemma nat_srcF_split `{!auth_sourceG Σ natA} (n m: nat):
    srcF natA (n + m) ⊣⊢ srcF natA n ∗ srcF natA m.
  Proof. apply srcF_split. Qed.

  Lemma nat_srcF_succ `{!auth_sourceG Σ natA} (n: nat):
    srcF natA (S n) ⊣⊢ srcF natA 1 ∗ srcF natA n.
  Proof. rewrite -srcF_split //=. Qed.

  Global Instance nat_credit `{!auth_sourceG Σ natA}: Credit SI := natA.

End nat_auth_source.

(* ord auth source *)
Section ord_auth_source.

  Context (SI: indexT).
  Lemma ord_source_step_frame (a a' f : OrdR SI):
    a' ≺ a → ✓ (a ⋅ f) → ✓ (a' ⋅ f) ∧ (a' ⋅ f) ≺ (a ⋅ f).
  Proof.
    intros Hαβ _; split; first done.
    by eapply natural_addition_strict_compat.
  Qed.

  Lemma ord_source_op_cancel (a f f' : OrdR SI):
      ✓ (a ⋅ f) → a ⋅ f = a ⋅ f' → f = f'.
  Proof using SI.
    intros _; rewrite comm_L [a ⋅ f']comm_L.
    by apply natural_addition_cancel.
  Qed.

  (* we define an auth structure for ordinals *)
  Program Canonical Structure ordA : auth_source SI := {|
    auth_sourceUR := OrdUR SI;
    auth_source_trans := flip (index_lt ordI);
    auth_source_discrete := _;
    auth_source_trans_proper := _;
    auth_source_step_frame := ord_source_step_frame;
    auth_source_op_cancel := ord_source_op_cancel
  |}.

  Lemma ord_srcF_split `{!auth_sourceG Σ ordA} (n m: Ord):
    srcF ordA (n ⊕ m) ⊣⊢ srcF ordA n ∗ srcF ordA m.
  Proof. apply srcF_split. Qed.

  Definition one : ordA := succ (zero).
  Lemma ord_srcF_succ `{!auth_sourceG Σ ordA} (n: Ord):
    srcF ordA (succ n) ⊣⊢ srcF ordA one ∗ srcF ordA n.
  Proof.
    rewrite -ord_srcF_split //= natural_addition_succ natural_addition_zero_left_id //=.
  Qed.

  Global Instance ord_credit `{!auth_sourceG Σ ordA}: Credit SI := ordA.

End ord_auth_source.

Global Arguments one {_}.

Inductive lex {X Y} (R: X → X → Prop) (S: Y → Y → Prop) : (X * Y) → (X * Y) -> Prop :=
| lex_left x x' y y': R x x' → lex R S (x, y) (x', y')
| lex_right x y y': S y y' → lex R S (x, y) (x, y').

Lemma sn_lex {X Y} (R: X → X → Prop) (S: Y → Y → Prop) x y: sn R x -> (forall y, sn S y) → sn (lex R S) (x, y).
Proof.
  intros Sx Sy. revert y; induction Sx as [x _ IHx]; intros y.
  induction (Sy y) as [y _ IHy].
  constructor. intros [x' y']; simpl; inversion 1; subst.
  - apply IHx; auto.
  - apply IHy; auto.
Qed.

Lemma tc_lex_left {X Y} (R: X → X → Prop) (S: Y → Y → Prop) x x' y y': tc R x x' → tc (lex R S) (x, y) (x', y').
Proof.
  induction 1 as [x x' Hstep| x x' x'' Hstep Hsteps] in y, y'.
  - constructor 1. by constructor.
  - econstructor 2; eauto. by eapply (lex_left _ _ _ _ y y).
Qed.

Lemma tc_lex_right {X Y} (R: X → X → Prop) (S: Y → Y → Prop) x y y': tc S y y' → tc (lex R S) (x, y) (x, y').
Proof.
  induction 1 as [y y' Hstep|y y' y'' Hstep Hsteps].
  - constructor 1. by constructor.
  - econstructor 2; eauto. by constructor 2.
Qed.

Lemma lex_rtc {X Y} (R: X → X → Prop) (S: Y → Y → Prop) x x' y y': rtc (lex R S) (x, y) (x', y') → rtc R x x'.
Proof.
  remember (x, y) as p1. remember (x', y') as p2. intros Hrtc.
  revert x x' y y' Heqp1 Heqp2. induction Hrtc as [p|p1 p2 p3 Hstep Hsteps IH]; intros x x' y y' -> Heq.
  - injection Heq. by intros -> ->.
  - subst p3. inversion Hstep; subst.
    + etransitivity; last by eapply IH.
      eapply rtc_l; by eauto.
    + by eapply IH.
Qed.


(* stuttering: we can stutter with any auth source *)
Section lexicographic.

  Context {SI A B} {Σ: gFunctors SI} `{src1: !source Σ A} `{src2: !source Σ B}.

  Global Instance lex_source : source Σ (A * B) := {|
    source_rel := lex source_rel source_rel;
    source_interp := (λ '(a, b), source_interp a ∗ source_interp b)%I;
  |}.

  Lemma source_update_embed_l_strong `{!invG Σ} E P Q:
  @src_update _ _ Σ src1 _ E P ∗
  (∀ b: B, source_interp b ={E}=∗ ∃ b': B, source_interp b' ∗ Q)
  ⊢ @src_update _ _ Σ lex_source _ E (P ∗ Q).
  Proof.
    rewrite /src_update; simpl. iIntros "[H Hupd]".
    iIntros ([a b]) "[Hs Hsrc]". iMod ("H" with "Hs") as (a' Hstep) "[SI P]".
    iFrame. iMod ("Hupd" with "Hsrc") as (b') "[Hsrc $]". iModIntro. iExists (a', b'); iFrame.
    iPureIntro. by apply tc_lex_left.
  Qed.

  Lemma source_update_embed_l `{!invG Σ} E P:
    @src_update _ _ Σ src1 _ E P ⊢ @src_update _ _ Σ lex_source _ E P.
  Proof.
    iIntros "H". iPoseProof (source_update_embed_l_strong _ _ True%I with "[$H]") as "H".
    - iIntros (b) "Hsrc". iModIntro. iExists b. iFrame.
    - iApply src_update_mono; iFrame; iIntros "[$ _]".
  Qed.

  Lemma source_update_embed_r `{!invG Σ} E P:
    @src_update _ _ Σ src2 _ E P ⊢ @src_update _ _ Σ lex_source _ E P.
  Proof.
    rewrite /src_update; simpl. iIntros "H".
    iIntros ([a b]) "[Ha Hb]". iMod ("H" with "Hb") as (b' Hstep) "[SI P]".
    iFrame. iModIntro. iExists (a, b'); iFrame.
    iPureIntro. by apply tc_lex_right.
  Qed.


End lexicographic.
