From iris.proofmode Require Import base proofmode classes.
From lantana.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From lantana.bi Require Export weakestpre.
From iris.prelude Require Import options.
From lantana.program_logic Require Export sfmupd model_physical_updates.
Import uPred.

(* TODO: move to somewhere else *)
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

Class temporalGpreS `{SI : indexT} (Λ : language) (Σ : gFunctors) :=
  TemporalGpreS {
      #[local] temporalGpreS_mupd :: mupdGpreS Σ;
      #[local] temporal_histGpreS :: histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ));
    }.

Class temporalGS `{SI : indexT} (Λ : language) (Σ : gFunctors) :=
  TemporalG {
      (** Obligation model protocol, including invariants. *)
      #[global] temporal_mupdGS :: mupdGS Σ;
      #[global] temporal_histGS :: histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ));
    }.
Global Opaque temporal_mupdGS temporal_histGS.
Global Arguments TemporalG {SI Λ Σ}.

Definition temporalΣ `{SI : indexT} (Λ : language) : gFunctors :=
  #[mupdΣ; histGS.histΣ (state Λ * thread_pool Λ * list (observation Λ))].
Global Instance subG_temporalΣ `{SI : indexT} {Λ} {Σ} : subG (temporalΣ Λ) Σ → temporalGpreS Λ Σ.
Proof. solve_inG. Qed.

Local Definition lwpupd_def `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  i E e : iPropO Σ -d> iPropO Σ :=
  (λ P, ∀ K h n σ Θ κs,
     (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e))⌝) →
     (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) -∗
     |={E:n,dom Θ}=>m (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ P)%I.
Local Definition lwpupd_aux : seal (@lwpupd_def). Proof. by eexists. Qed.
Definition lwpupd := lwpupd_aux.(unseal).
Global Arguments lwpupd {SI Λ Σ _ _}.
Local Lemma lwpupd_unseal `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} :
  lwpupd = @lwpupd_def SI Λ Σ _ _.
Proof. rewrite -lwpupd_aux.(seal_eq) //. Qed.

Ltac unfold_lwpupd := rewrite lwpupd_unseal /lwpupd_def.

Section lwpupd.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance lwpupd_ne i E e : NonExpansive (lwpupd i E e).
  Proof. intros n P1 P2 HP. unfold_lwpupd. do 18 (f_equiv || done). Qed.
  Global Instance lwpupd_proper i E e : Proper ((≡) ==> (≡)) (lwpupd i E e).
  Proof. intros P P' ?. apply equiv_dist=>n. apply lwpupd_ne. apply equiv_dist. done. Qed.

  Lemma sfmupd_lwpupd i E e P : (|={E}=>m P) ⊢ (lwpupd i E e P).
  Proof.
    unfold_lwpupd. iIntros "Hupd %%%%%% %% [SI $]".
    unfold_sfmupd. iMod ("Hupd" with "SI") as "$". done.
  Qed.
  Lemma fupd_lwpupd i E e P : (|={E}=> P) ⊢ (lwpupd i E e P).
  Proof. iIntros "H". iApply sfmupd_lwpupd. iMod "H". done. Qed.

  Lemma lwpupd_intro i E e P : P ⊢ lwpupd i E e P.
  Proof. unfold_lwpupd. iIntros "$ %%%%%% %% $". done. Qed.

  Lemma sfmupd_lwpupd_elim i E e P : (|={E}=>m lwpupd i E e P) ⊢ lwpupd i E e P.
  Proof.
    iIntros "H". unfold_lwpupd. iIntros (?????? ??) "[SI SIa]".
    unfold_sfmupd. iMod ("H" with "SI") as "[SI H]". iApply "H"; eauto. iFrame.
  Qed.

  (** Change to a larger mask. *)
  Lemma lwpupd_mask_mono i e E1 E2 P :
    E1 ⊆ E2 →
    (lwpupd i E1 e P) ⊢ lwpupd i E2 e P.
  Proof.
    unfold_lwpupd. iIntros (Sub) "H %%%%%% %% SI". iPoseProof ("H" $! K with "[//] [//] SI") as "H".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod "H". iMod "close" as "_". iModIntro. auto.
  Qed.

  (** Expression and context. *)
  Lemma lwpupd_ctx i E e K P :
    LanguageCtx K →
    (lwpupd i E e P) ⊢ lwpupd i E (K e) P.
  Proof.
    unfold_lwpupd. iIntros (HK) "H %%%%%% %% SI". iPoseProof ("H" $! (K0 ∘ K) with "[] [] SI") as "H".
    { iPureIntro. apply _. }
    { done. }
    done.
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma lwpupd_bind i E e P Q :
    (P -∗ lwpupd i E e Q) ⊢ (lwpupd i E e P) -∗ (lwpupd i E e Q).
  Proof.
    iIntros "H HP". unfold_lwpupd. iIntros "%%%%%% %% SI".
    iMod ("HP" $! K with "[//] [//] SI") as "[SI HP]".
    iPoseProof ("H" with "HP [//] [//] SI") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma lwpupd_mono i E e P Q : (P ⊢ Q) → (lwpupd i E e P) ⊢ (lwpupd i E e Q).
  Proof.
    intros Hent. iApply lwpupd_bind.
    iIntros "P"; iApply lwpupd_intro; by iApply Hent.
  Qed.
  Lemma lwpupd_trans i E e P :  (lwpupd i E e (lwpupd i E e P)) ⊢ lwpupd i E e P.
  Proof.
    iIntros "HP". iApply lwpupd_bind; eauto.
  Qed.
  Lemma lwpupd_frame_r i E e P R : (lwpupd i E e P) ∗ R ⊢ lwpupd i E e (P ∗ R).
  Proof.
    iIntros "[Hupd R]". iApply (lwpupd_bind with "[R]"); last done.
    iIntros "P". iApply lwpupd_intro. by iFrame.
  Qed.

  Global Instance lwpupd_ent_proper i E e : Proper ((⊢) ==> (⊢)) (lwpupd i E e).
  Proof. intros P Q PQ. by apply lwpupd_mono. Qed.
  Global Instance lwpupd_flip_ent_proper i E e : Proper (flip (⊢) ==> flip (⊢)) (lwpupd i E e).
  Proof. intros P Q PQ; by apply lwpupd_mono. Qed.
  Global Instance lwpupd_equiv_proper i E e : Proper ((≡) ==> (≡)) (lwpupd i E e) := ne_proper _.

  Lemma lwpupd_fupd_l i E e P :
    (|={E}=> lwpupd i E e P) ⊢ (lwpupd i E e P).
  Proof. iIntros "H". iApply sfmupd_lwpupd_elim. iMod "H". done. Qed.
  Lemma lwpupd_fupd_r i E e P :
    (lwpupd i E e (|={E}=> P)) ⊢ (lwpupd i E e P).
  Proof. iIntros "H". rewrite fupd_sfmupd sfmupd_lwpupd. iApply (lwpupd_trans with "H"). Qed.

  Lemma lwpupd_frame_l i E e R Q : (R ∗ lwpupd i E e Q) ⊢ lwpupd i E e (R ∗ Q).
  Proof. rewrite !(comm _ R); apply lwpupd_frame_r. Qed.
  Lemma lwpupd_wand_l i E e P Q : (P -∗ Q) ∗ (lwpupd i E e P) ⊢ lwpupd i E e Q.
  Proof. by rewrite lwpupd_frame_l wand_elim_l. Qed.
  Lemma lwpupd_wand_r i E e P Q : (lwpupd i E e P) ∗ (P -∗ Q) ⊢ lwpupd i E e Q.
  Proof. by rewrite lwpupd_frame_r wand_elim_r. Qed.
  Lemma lwpupd_sep i E e P Q : (lwpupd i E e P) ∗ (lwpupd i E e Q) ⊢ lwpupd i E e (P ∗ Q).
  Proof. by rewrite lwpupd_frame_r lwpupd_frame_l lwpupd_trans. Qed.
  Lemma lwpupd_idemp i E e P : (lwpupd i E e (lwpupd i E e P)) ⊣⊢ lwpupd i E e P.
  Proof.
    apply: anti_symm.
    - apply lwpupd_trans.
    - apply lwpupd_intro.
  Qed.

  Global Instance lwpupd_homomorphism i E e :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (lwpupd i E e).
  Proof. split; [split|]; try apply _; [apply lwpupd_sep | apply lwpupd_intro]. Qed.

  Lemma big_sepL_lwpupd {A} (Φ : nat → A → iProp Σ) i E e l :
    ([∗ list] k↦x ∈ l, lwpupd i E e (Φ k x)) ⊢ lwpupd i E e ([∗ list] k↦x ∈ l, Φ k x).
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_lwpupd {A} `{Countable K} (Φ : K → A → iProp Σ) i E e l :
    ([∗ map] k↦x ∈ l, lwpupd i E e (Φ k x)) ⊢ lwpupd i E e ([∗ map] k↦x ∈ l, Φ k x).
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_lwpupd `{Countable A} (Φ : A → iProp Σ) i E e l :
    ([∗ set]  x ∈ l, lwpupd i E e (Φ x)) ⊢ lwpupd i E e ([∗ set] x ∈ l, Φ x).
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_lwpupd `{Countable A} (Φ : A → iProp Σ) i E e l :
    ([∗ mset] x ∈ l, lwpupd i E e (Φ x)) ⊢ lwpupd i E e ([∗ mset] x ∈ l, Φ x).
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_lwpupd i E e P : ◇ (lwpupd i E e P) ⊢ (lwpupd i E e (◇ P)).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using lwpupd_mono, or_intro_r.
    by rewrite -lwpupd_intro -or_intro_l.
  Qed.

  Lemma lwpupd_fupd_acc i e E1 E2 P :
    (|={E1,E2}=> lwpupd i E2 e (|={E2,E1}=> P)) ⊢ (lwpupd i E1 e P).
  Proof.
    unfold_lwpupd. iIntros "H %%%%%% %% I". iMod "H". iPoseProof ("H" $! K with "[//] [//] I") as "H".
    iApply fmupd_fupd_r. iMod "H". iModIntro.
    iDestruct "H" as "[$ H]". auto.
  Qed.

  (** Elim rule. *)
  Lemma all_interp_lwpupd_steps (γ : thread_id → nat) i E e h n σ Θ κs g v Ω W (P : iProp Σ) :
    (Θ !! i = Some e) →
    (owit_inv_lb (fair_sched_fun γ) Ω W) →
    (lwpupd i E e P) -∗ (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) -∗ model_interp g v Ω W n (dom Θ) ={E}=∗
    (P ∗ (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb (fair_sched_fun γ) Ω' W' ⌝ ∗ model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (HTh LB) "HP HI MI". unfold_lwpupd. iPoseProof ("HP" $! id with "[] [//] HI") as ">HP".
    { iPureIntro. apply _. }
    iMod (model_interp_mupd_steps with "HP MI") as "(>($& $)& $)"; auto.
    split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub].
  Qed.

  Lemma all_interp_lwpupd_steps_gmap (γ : thread_id → nat) E h n σ Θ κs g v Ω W
    (A : Type) (TQ : gmap thread_id ((expr Λ) * A)) (P : thread_id → (expr Λ) → A → iProp Σ) :
    (fst <$> TQ) ⊆ Θ →
    (owit_inv_lb (fair_sched_fun γ) Ω W) →
    ([∗ map] i ↦ '(e, a) ∈ TQ, lwpupd i E e (P i e a)) -∗
    (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) -∗ model_interp g v Ω W n (dom Θ) ={E}=∗
    (([∗ map] i ↦ '(e, a) ∈ TQ, (P i e a)) ∗
     (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb (fair_sched_fun γ) Ω' W' ⌝ ∗ model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    revert h n σ Θ κs g v Ω W. induction TQ using map_ind; iIntros (h n σ Θ κs g v Ω W EQTQ LB) "PS HI MI".
    { iModIntro. iSplitR; first done. iFrame. iExists [], 0, _, _. rewrite app_nil_r Nat.add_0_r. iFrame. done. }
    iPoseProof (big_sepM_insert with "PS") as "[HP PS]". 1: auto.
    destruct x as (e& a). iMod (IHTQ with "PS HI MI") as "(PS& HI& %&%&%&%&%& MI)". 1: auto.
    { rewrite fmap_insert in EQTQ. simpl in EQTQ. etrans; last eauto. apply insert_subseteq.
      rewrite lookup_fmap H. done. }
    1: auto.
    destruct H0 as (OLE2& LB2).
    iMod (all_interp_lwpupd_steps with "HP HI MI") as "(HP& HI& %&%&%&%&%& MI)".
    { rewrite fmap_insert in EQTQ. simpl in EQTQ. eapply lookup_weaken; last eauto. apply lookup_insert_eq. }
    1: eapply LB2.
    iModIntro. rewrite big_sepM_insert; last auto. iFrame. iExists (g' ++ g'0), (v' + v'0), _, _.
    rewrite app_assoc Nat.add_assoc. iFrame. iPureIntro. destruct H0. split; auto. etrans; eauto.
  Qed.

  (** Later credits. *)
  Lemma lc_lwpupd_add_later i E e P :
    £n 1 -∗ (▷ lwpupd i E e P) -∗ lwpupd i E e P.
  Proof.
    iIntros "LC H". iApply sfmupd_lwpupd_elim. iApply (lc_sfmupd_add_later with "LC"). by iNext.
  Qed.
  Lemma lc_lwpupd_add_laterN n i E e P :
    £n n -∗ (▷^n lwpupd i E e P) -∗ lwpupd i E e P.
  Proof.
    iIntros "LC H". iApply sfmupd_lwpupd_elim. iApply (lc_sfmupd_add_laterN with "LC"). by iNext.
  Qed.

End lwpupd.

Class lantanaGS `{SI : indexT} (Λ : language) (Σ : gFunctors) :=
  LantanaG {
      (** Ghost states for temporal properties. *)
      #[global] lantana_temporalGS :: temporalGS Λ Σ;

      (** The state (and history) interpretation is an invariant that should hold in
          between each step of reduction.
          Here [state] is the global state, [thread_ids] is the allocated thread ids,
          and [list (observation Λ)] are the remaining observations. *)
      #[global] lantana_state_interp_class :: state_interp_class Λ Σ;

      (** A fixed postcondition for any forked-off thread. For most languages, e.g.
          heap_lang, this will simply be [True]. However, it is useful if one wants to
          keep track of resources precisely, as in e.g. Iron. *)
      fork_post : thread_id → val Λ → iProp Σ;
    }.

Global Opaque lantana_temporalGS lantana_state_interp_class.
Global Arguments LantanaG {SI Λ Σ}.

(** Predicates we take the fixpoint of in order to define the lWP. *)
(* Ω must make strict progress for every step (to bound step-index) *)
(* W witnesses progress of obligations; it relies on the fair scheduler for soundness *)
Definition lwp_step `{SI : indexT} `{!lantanaGS Λ Σ}
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ K h n σ1 Θ κ κs,
     (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
     (history_interp h n σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
      (** ** No discharge allowed for pre-state *)
      |=[n,dom Θ]=>g
      (⌜if s is NotStuck then reducible i e1 σ1 (dom Θ) else True⌝) ∗
      ∀ e2 σ2 (efs : thread_pool Λ), (⌜ prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs ⌝) -∗
      @={n,(dom Θ),i}=↓ (@={n,(S n),(dom Θ),(dom (<[i:=K e2]>Θ) ∪ dom efs)}=>
      (** ** Discharge allowed for post-state *)
      (ALC (|=[(S n),(dom (<[i:=K e2]>Θ) ∪ dom efs)]=>m |={∅,E}=>
              ((history_interp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)]) (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
               state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
              ν e2 efs))))%I.

Section lwp_step.
  Context `{SI : indexT} `{!lantanaGS Λ Σ}.

  Global Instance lwp_step_ne s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step. do 34 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono s (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (?????????) "H". iSpecialize ("Hwp" $! K with "[//] [//] [$]").
    iMod "Hwp". iModIntro. iMod "Hwp" as "($& Hwp)". iModIntro.
    iIntros (???) "H0".
    iDestruct ("Hwp" with "[$]") as ">>>Hwp".
    iMod "Hwp" as "Hwp". iModIntro. iMod "Hwp" as "[$ H]".
    by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros (?????????). iMod "Hf" as "Hf". iApply ("Hf" $! K with "[//] [//]").
  Qed.

  Lemma sfgupd_lwp_step s i E e lwp :
    (|={E}=>g lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros (?????????) "[HI HA]".
    unfold_sfgupd. iPoseProof ("Hf" with "HI") as ">Hf".
    iModIntro. iMod "Hf". iApply fupd_gupd_elim. iMod "Hf" as "(HI& Hf)".
    iApply ("Hf" with "[//] [//] [$HI $HA]").
  Qed.

  Lemma lwp_step_lwpupd s i E e ν :
    lwp_step s i E e ν ⊣⊢ lwp_step s i E e (λ e' efs, lwpupd i E e' (ν e' efs)).
  Proof.
    iSplit; iIntros "H".
    - iIntros "%%%%%%%%% HI". iMod ("H" $! K with "[//] [//] HI") as "H".
      iModIntro. iMod "H" as "[$ H]".
      iIntros "!> %%% Hs". iMod ("H" with "Hs") as ">>>H".
      iDestruct "H" as ">(HI& H)". iModIntro. iFrame. iApply lwpupd_intro. done.
    - iIntros "%%%%%%% %% HI". iMod ("H" $! K with "[//] [//] HI") as "H".
      iModIntro. iMod "H" as "[$ H]".
      iIntros "!> %%% Hs". iMod ("H" with "Hs") as ">>>H".
      iDestruct "H" as ">(HI& H)". unfold_lwpupd. iMod ("H" $! K with "[//] [] HI") as "H".
      { iPureIntro. rewrite -insert_union_l lookup_insert_eq. auto. }
      rewrite dom_union_L. iModIntro. iMod "H". iFrame. done.
  Qed.

End lwp_step.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lantanaGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  (** Modality instances for lwpupd *)
  Global Instance elim_bupd_lwpupd (p : bool) i E e P Q :
    ElimModal True p false (|==> P) P (lwpupd i E e Q) (lwpupd i E e Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfmupd_lwpupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_fupd_lwpupd (p : bool) i E e P Q :
    ElimModal True p false (|={E}=> P) P (lwpupd i E e Q) (lwpupd i E e Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfmupd_lwpupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_sfgupd_lwpupd (p : bool) i E e P Q :
    ElimModal True p false (|={E}=>g P) P (lwpupd i E e Q) (lwpupd i E e Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfmupd_lwpupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_sfmupd_lwpupd (p : bool) i E e P Q :
    ElimModal True p false (|={E}=>m P) P (lwpupd i E e Q) (lwpupd i E e Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfmupd_lwpupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_lwpupd i E e P Q :
    AddModal (|={E}=> P) P (lwpupd i E e Q).
  Proof.
    rewrite /AddModal; rewrite fupd_lwpupd; iIntros "[HP HPQ]".
    iApply (lwpupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_lwpupd p i E e P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (lwpupd i E e Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply lwpupd_intro. Qed.

  Global Instance from_pure_lwpupd a i E e P φ :
    FromPure a P φ → FromPure a (lwpupd i E e P) φ.
  Proof. rewrite /FromPure=> <-. apply lwpupd_intro. Qed.

  Global Instance into_wand_lwpupd p q i E e R P Q :
    IntoWand false false R P Q → IntoWand p q (lwpupd i E e R) (lwpupd i E e P) (lwpupd i E e Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite lwpupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_lwpupd_persistent p q i E e R P Q :
    IntoWand false q R P Q → IntoWand p q (lwpupd i E e R) P (lwpupd i E e Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite lwpupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_lwpupd_args p q i E e R P Q :
    IntoWand p false R P Q → IntoWand' p q R (lwpupd i E e P) (lwpupd i E e Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim lwpupd_wand_r.
  Qed.

  Global Instance from_sep_lwpupd i E e P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (lwpupd i E e P) (lwpupd i E e Q1) (lwpupd i E e Q2).
  Proof. rewrite /FromSep=><-. apply lwpupd_sep. Qed.

  Global Instance from_or_lwpupd i E e P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (lwpupd i E e P) (lwpupd i E e Q1) (lwpupd i E e Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply lwpupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_lwpupd {A} i E e P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (lwpupd i E e P) (λ a, lwpupd i E e (Φ a))%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_lwpupd i E e P : IsExcept0 P → IsExcept0 (lwpupd i E e P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_lwpupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_lwpupd i E e P :
    FromModal True modality_id (lwpupd i E e P) (lwpupd i E e P) P.
  Proof. by rewrite /FromModal /= -lwpupd_intro. Qed.

  Global Instance elim_modal_lwpupd p i E e P Q :
    ElimModal True p false (lwpupd i E e P) P (lwpupd i E e Q) (lwpupd i E e Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim lwpupd_frame_r wand_elim_r lwpupd_trans.
  Qed.

  (* This instance makes iMod unstable. *)
  (* Global Instance elim_lwpupd_lwpupd_ctx (p : bool) i E K e P Q : *)
  (*   ElimModal (LanguageCtx K) p false (lwpupd i E e P) P (lwpupd i E (K e) Q) (lwpupd i E (K e) Q)%I. *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim //=. *)
  (*   iIntros "%HK [HP HPQ]". iPoseProof (lwpupd_ctx _ _ _ K with "HP") as "HP". *)
  (*   iMod "HP". by iApply "HPQ". *)
  (* Qed. *)

  Global Instance elim_modal_fupd_lwpupd_acc p i E1 E2 e P Q :
    ElimModal True p false
      (|={E1,E2}=> P) P
      (lwpupd i E1 e Q) (lwpupd i E2 e (|={E2,E1}=> Q))%I | 100.
  Proof.
    intros ?. rewrite intuitionistically_if_elim fupd_frame_r wand_elim_r.
    iIntros "H". iApply (lwpupd_fupd_acc with "H").
  Qed.

  Global Instance add_modal_lwpupd i E e P Q : AddModal (lwpupd i E e P) P (lwpupd i E e Q).
  Proof. by rewrite /AddModal lwpupd_frame_r wand_elim_r lwpupd_trans. Qed.

  Global Instance frame_lwpupd p i E e R P Q :
    Frame p R P Q → Frame p R (lwpupd i E e P) (lwpupd i E e Q).
  Proof. rewrite /Frame=><-. by rewrite lwpupd_frame_l. Qed.

End proofmode_classes.

(** Wrapper for the termination condition for soundness. *)
Definition lift_term `{SI : indexT} `{!lantanaGS Λ Σ} (i :thread_id) (Φ : thread_id → val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (thP_done i ∗ Φ i v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Lantana, postcondition of a thread i must include othreadG_term i. *)
Definition lwp_pre `{SI : indexT} `{!lantanaGS Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => |={E}=>g (Φ v)
     | None =>
         (lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwpupd j ⊤ ef (lwp j ⊤ ef (lift_term j fork_post))))
     end)%I.

Lemma lwp_pre_mono `{SI : indexT} `{!lantanaGS Λ Σ} s
  (lwp1 lwp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, lwp1 i E e Φ -∗ lwp2 i E e Φ) →
     ∀ i E e Φ, lwp_pre s lwp1 i E e Φ -∗ lwp_pre s lwp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Hlwp". rewrite /lwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (lwp_step_mono with "[] Hlwp"). iModIntro.
  iIntros (e efs) "[Hlwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  iApply (@big_sepM_impl with "Hefs"); iIntros "!#" (k e' _) "Hlwp".
  iApply (lwpupd_wand_l with "[$Hlwp]"). iApply "Hmono".
Qed.

(* Uncurry [lwp_pre] and equip its type with an OFE structure *)
Definition lwp_pre' `{SI : indexT} `{!lantanaGS Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : indexT} `{!lantanaGS Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step.
    do 36 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition; we can also just take fixpoint. *)
Definition lwp_fix `{SI : indexT} `{!lantanaGS Λ Σ} : stuckness -> thread_id -> coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E e Φ, ((bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ))%I.

Local Definition lwp_def `{SI : indexT} `{!lantanaGS Λ Σ} : Lwp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s i E e Φ, (lwp_fix s i E e Φ)%I.
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI Λ Σ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : indexT} `{!lantanaGS Λ Σ} : lwp = @lwp_def SI Λ Σ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.

Section lwp.
  Context `{SI : indexT} `{!lantanaGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance lwp_fix_ne s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_fix s i E e).
  Proof. intros Φ Ψ HΦ. rewrite /lwp_fix. f_equiv. by apply pair_ne. Qed.
  Global Instance lwp_fix_proper s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_fix s i E e).
  Proof. by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_fix_ne=>v; apply equiv_dist. Qed.

  (* Weakest pre *)
  Lemma lwp_pre_lwpupd s i E e Φ Ψ :
    lwp_pre s (λ i E e Φ, Ψ i E e Φ) i E e Φ ⊣⊢ lwp_pre s (λ i E e Φ, lwpupd i E e (Ψ i E e Φ)) i E e Φ.
  Proof.
    rewrite /lwp_pre. destruct (to_val e) eqn:He; first auto.
    iSplit; iIntros "H".
    - iApply (lwp_step_mono with "[] H"); iIntros "!> %% H".
      iDestruct "H" as "[H1 H2]". iSplitL "H1"; first (by iApply lwpupd_intro).
      iApply (big_sepM_impl with "H2"). iIntros "!> %%% H". iModIntro. auto.
    - iApply lwp_step_lwpupd. iApply (lwp_step_mono with "[] H"); iIntros "!> %% H".
      iDestruct "H" as "[>$ H2]". iModIntro.
      iApply (big_sepM_impl with "H2"). iIntros "!> %%% >H". auto.
  Qed.

  Lemma lwp_pre_lwp_pre' s _lwp i E e Φ :
    lwp_pre s _lwp i E e Φ = lwp_pre' s (λ '(i,E,e,Φ), _lwp i E e Φ) (i,E,e,Φ).
  Proof. rewrite /lwp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.

  Lemma lwp_fix_unfold_fix s i E e Φ :
    lwp_fix s i E e Φ ⊣⊢ (lwp_pre s (lwp_fix s) i E e Φ).
  Proof.
    rewrite /lwp_fix. rewrite lwp_pre_lwp_pre'.
    rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
    - done.
    - done.
  Qed.
  Lemma lwp_fix_unfold s i E e Φ :
    lwp_fix s i E e Φ ⊣⊢ (lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ).
  Proof.
    rewrite /lwp_fix lwp_unseal. rewrite lwp_pre_lwp_pre' /lwp_def.
    rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
    - done.
    - done.
  Qed.

  Lemma lwp_unfold s i E e Φ :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_pre s (lwp (PROP:=iProp Σ) s) i E e Φ).
  Proof.
    rewrite lwp_unseal /lwp_def. rewrite lwp_fix_unfold lwp_unseal /lwp_def. auto.
  Qed.
  Lemma lwp_unfold_upd s i E e Φ :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_pre s (λ i E e Φ, lwpupd i E e (lwp (PROP:=iProp Σ) s i E e Φ)) i E e Φ).
  Proof.
    rewrite lwp_unfold lwp_pre_lwpupd. done.
  Qed.
  Lemma lwp_unfold_fix s i E e Φ :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ (lwp_fix s i E e Φ).
  Proof. rewrite lwp_unfold lwp_fix_unfold. done. Qed.

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
      { rewrite /lwp_def. f_equiv. f_equiv. done. }
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

  Lemma fupd_elim_lwp s i E e Φ :
    (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_unfold. rewrite /lwp_pre /lwp_step.
    destruct (to_val e) as [v|] eqn:?.
    { iMod "H". rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo. done. }
    iIntros (?????????) "SI". iMod "H".
    rewrite lwp_unfold /lwp_pre /lwp_step. rewrite Heqo.
    iMod ("H" $! K with "[//] [//] SI") as "H". iModIntro. iMod "H" as "[$ h]". done.
  Qed.

  Lemma sfgupd_elim_lwp s i E e Φ :
    (|={E}=>g lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iPoseProof (lwp_unfold with "H") as "H".
    iApply lwp_unfold. rewrite /lwp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { by iMod "H". }
    { by iApply sfgupd_lwp_step. }
  Qed.

  Lemma lwp_value_sfgupd' s i E Φ v :
    lWP of_val v @ s; i; E {{ Φ }} ⊣⊢ (|={E}=>g (Φ v)).
  Proof.
    iSplit; iIntros "H".
    - by rewrite lwp_unfold /lwp_pre to_of_val.
    - by rewrite lwp_unfold /lwp_pre to_of_val.
  Qed.

  Lemma lwp_stuckness_mono s1 s2 i E e Φ :
    s1 ⊑ s2 →
    lWP e @ s1; i; E {{ Φ }} -∗ lWP e @ s2; i; E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iRevert (i e E Φ) "H". iApply lwp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
    rewrite !lwp_unfold /lwp_pre /=.
    destruct (to_val e) as [v|] eqn:?; first done.
    iIntros (??????? ??) "H". iMod ("IH" $! K with "[//] [//] [$]") as "H".
    iModIntro. iMod "H". iModIntro.
    iPoseProof "H" as "[% IH]".
    iSplit; [by destruct s1, s2|clear H0].
    iIntros (????). iMod ("IH" with "[//]") as ">>IH".
    iMod "IH" as "IH". iModIntro.
    iMod "IH" as "($& [IH Efs])". iDestruct "IH" as "[IH _]".
    iModIntro. iFrame.
    iApply (big_sepM_impl with "Efs"). iIntros "!>" (k ef _). iIntros ">[H _]". done.
  Qed.

  Lemma lwp_strong_mono_sfgupd s1 s2 i E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    (lWP e @ s1; i; E1 {{ Φ }}) -∗ (∀ v, Φ v -∗ |={E2}=>g (Ψ v)) -∗ (lWP e @ s2; i; E2 {{ Ψ }}).
  Proof.
    iIntros (? HE) "H HΦ".
    iRevert "HΦ". iRevert (E2 HE). iRevert (i e E1 Φ) "H".
    iApply lwp_ind_strong; [solve_proper| ].
    iIntros "!>" (i e E1 Φ) "IH % %HE HΦ".
    rewrite lwp_unfold /lwp_pre /=.
    destruct (to_val e) as [v|] eqn:?.
    { iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod "IH". iMod "Hclose" as "_". iApply ("HΦ" with "IH"). }
    iIntros (??????? ??) "H". iSpecialize ("IH" $! K with "[//] [//] [$]").
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod "IH". iModIntro. iMod "IH" as "(%& IH)".
    iModIntro.
    iSplit; [by destruct s1, s2|clear H0].
    iIntros (????). iMod ("IH" with "[//]") as ">>IH".
    iMod "IH". iModIntro. iMod "IH" as "[$ IH]".
    iMod "Hclose" as "_". iModIntro.
    iDestruct "IH" as "([IH _]& Efs)".
    iSplitR "Efs".
    + by iApply "IH".
    + iApply (big_sepM_impl with "Efs"); iIntros "!>" (k ef _).
      iIntros ">[_ H]". by iApply (lwp_stuckness_mono with "H").
  Qed.
  Lemma lwp_strong_mono s1 s2 i E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    (lWP e @ s1; i; E1 {{ Φ }}) -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ (lWP e @ s2; i; E2 {{ Ψ }}).
  Proof.
    iIntros (? HE) "H HΦ".
    iApply (lwp_strong_mono_sfgupd with "H [HΦ]"). all: auto.
    iIntros "% H". iMod ("HΦ" with "H") as "$". done.
  Qed.

  Lemma fupd_lwp s i E e Φ :
    (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply fupd_elim_lwp. iMod "H". by iModIntro. Qed.
  Lemma sfgupd_lwp s i E e Φ :
    (|={E}=>g lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply sfgupd_elim_lwp. iMod "H". by iModIntro. Qed.

  Lemma lwp_fupd s i E e Φ :
    lWP e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply (lwp_strong_mono s s i E with "H"); auto. Qed.
  Lemma lwp_sfgupd s i E e Φ :
    lWP e @ s; i; E {{ v, |={E}=>g Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. iIntros "H". iApply (lwp_strong_mono_sfgupd s s i E with "H"); auto. Qed.

  (* Not true unless atomic step. *)
  (* Lemma lwp_sfmupd s i E e Φ : *)
  (*   lWP e @ s; i; E {{ v, |={E}=>m Φ v }} ⊢ lWP e @ s; i; E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply (lwp_strong_mono_sfmupd s s i E with "H"); auto. Qed. *)
  (* Lemma lwp_lwpupd s i E e Φ : *)
  (*   lWP e @ s; i; E {{ v, ∀ e', lwpupd i E e' (Φ v) }} ⊢ lWP e @ s; i; E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply (lwp_strong_mono_lwpupd s s i E with "H"); auto. Qed. *)

  (* Lemma sfmupd_lwp s i E e Φ : *)
  (*   (|={E}=>m lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply sfmupd_elim_lwp. done. Qed. *)
  (* Lemma lwpupd_lwp s i E e Φ : *)
  (*   (lwpupd i E e (lWP e @ s; i; E {{ Φ }})) ⊢ lWP e @ s; i; E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply lwpupd_elim_lwp. done. Qed. *)

  Lemma lwp_atomic_sfgupd s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=>g lWP e @ s; i; E2 {{ v, |={E2,E1}=>g Φ v }})
    ⊢ lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". rewrite !lwp_unfold /lwp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { iMod "H" as ">H". done. }
    iIntros (??????? ??) "[HI HA]".
    unfold_sfgupd. iMod ("H" with "HI") as "H". iModIntro. iMod "H". iMod "H" as "[HI H]".
    iMod ("H" $! K with "[//] [//] [$HI $HA]") as "H".
    iModIntro. iMod "H".
    iModIntro. iPoseProof "H" as "[$ H]".
    iIntros (??? STEP). iMod ("H" with "[//]") as "H".
    iMod "H". iMod "H" as ">>(SI& H& Efs)".
    destruct s.
    - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iDestruct "SI" as "[HI HA]". unfold_sfgupd. iMod ("H" with "HI") as "H".
        assert (DomEq : dom (<[i:=K e2]> Θ ∪ efs) = dom (<[i:=K e2]> Θ) ∪ dom efs).
        { rewrite dom_union_L. auto. }
        rewrite !DomEq.
        iModIntro. iMod "H". iMod "H" as "(HI& H)". iMod ("H" with "HI") as "H".
        rewrite !DomEq.
        iModIntro. iMod "H". iModIntro. iMod "H" as "(HI& HΦ)". iFrame.
        iModIntro. iIntros (?????) "$". done.
      + iMod ("H" $! K _ _ _ _ [] with "[//] [] SI") as "H".
        { iPureIntro. rewrite -insert_union_l lookup_insert_eq; auto. }
        assert (DomEq : dom (<[i:=K e2]> Θ ∪ efs) = dom (<[i:=K e2]> Θ) ∪ dom efs).
        { rewrite dom_union_L. auto. }
        rewrite !DomEq.
        iModIntro. iMod "H" as "[Red H]".
        iDestruct "Red" as %(? & ? & ? & ? & ?).
        replace ((dom (<[i:=K e2]> Θ) ∪ dom efs)) with (dom Θ ∪ dom efs) in H1.
        1: by edestruct (atomic _ _ _ _ _ _ _ STEP).
        rewrite dom_insert_lookup_L; eauto.
    - destruct (atomic _ _ _ _ _ _ _ STEP) as [v <-%of_to_val].
      rewrite lwp_value_sfgupd'.
      iDestruct "SI" as "[HI HA]".
      unfold_sfgupd. iMod ("H" with "HI") as "H".
      iModIntro.
      assert (DomEq : dom (<[i:=K (of_val v)]> Θ ∪ efs) = dom (<[i:=K (of_val v)]> Θ) ∪ dom efs).
      { rewrite dom_union_L. auto. }
      rewrite !DomEq. iMod "H".
      iMod "H" as "(SI& H)". iMod ("H" with "SI") as "H".
      rewrite !DomEq. iModIntro. iMod "H". iModIntro.
      iMod "H" as "($& H)". iFrame.
      iApply lwp_value_sfgupd'. done.
  Qed.

  Lemma lwp_atomic s i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=> lWP e @ s; i; E2 {{ v, |={E2,E1}=> Φ v }})
    ⊢ lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_atomic_sfgupd. iMod "H". iModIntro.
    iApply (lwp_strong_mono with "H"). 1,2: done. iIntros (?) "H". iModIntro.
    by iApply fupd_sfgupd.
  Qed.

  Lemma lwp_step_sfgupd s i E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    ((|={E1,E2}=>g |={E2,E1}=>g P) ∗
     lWP e @ s; i; E2 {{ v, P -∗ |={E1}=>g Φ v }}) -∗
    lWP e @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros (? ?) "[HP Hwp]". iApply (lwp_strong_mono_sfgupd with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
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
    lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}
                  ⊢ (lWP K e @ s; i; E {{ Φ }}).
  Proof.
    revert Φ.
    cut (∀ Φ', (lWP e @ s; i; E {{ Φ' }}) -∗
               ∀ Φ, (∀ v, (Φ' v) -∗ (lWP K (of_val v) @ s; i; E {{ Φ }})) -∗
                    (lWP K e @ s; i; E {{ Φ }})).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". iIntros (Φ) "H2".
    iRevert (Φ) "H2".
    iRevert (i e E Φ') "H". iApply lwp_ind_strong; first solve_proper.
    iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
    iApply sfgupd_lwp.
    rewrite lwp_unfold /lwp_pre /lwp_step. destruct (to_val e) as [v|] eqn:He.
    { iMod "IH". iPoseProof ("HΦ" with "IH") as "H".
      rewrite lwp_unfold /lwp_pre /lwp_step.
      apply of_to_val in He as <-. by iFrame. }
    rewrite fill_not_val; last auto.
    iModIntro.
    iIntros (K1 ?????? HK1 LU1) "SI". iMod ("IH" $! (K1 ∘ K) with "[] [//] SI") as "IH".
    { iPureIntro. apply _. }
    iModIntro. iMod "IH" as "(%& IH)". iModIntro. iSplit.
    { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
    iIntros (e2 σ2 efs Hstep).
    destruct (fill_step_inv (K:=K) i e σ1 (dom Θ) κ e2 σ2 efs) as (e2'&->&?); auto.
    iDestruct ("IH" $! _ _ _ H0) as ">IH".
    iMod "IH" as ">>IH". iMod "IH". iDestruct "IH" as "(SI& IH& Efs)".
    rewrite (bi.sep_assoc). iSplitR "Efs"; cycle 1.
    { iModIntro. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% >[_ H]". done. }
    iDestruct "IH" as "[IH _]". iPoseProof ("IH" with "HΦ") as "IH".
    by iFrame.
  Qed.

  Lemma lwp_bind_step K `{!LanguageCtx K} s i E e Φ :
    TCEq (to_val e) None →
    lWP e @ s; i; E {{ v, lwpupd i E (K (of_val v)) (lWP K (of_val v) @ s; i; E {{ Φ }}) }}
    ⊢ lWP K e @ s; i; E {{ Φ }}.
  Proof.
    intros He.
    revert Φ.
    cut (∀ Φ', (lWP e @ s; i; E {{ Φ' }}) -∗
               ∀ Φ, (∀ v, (Φ' v) -∗ (lwpupd i E (K (of_val v)) (lWP K (of_val v) @ s; i; E {{ Φ }}))) -∗
                    (lWP K e @ s; i; E {{ Φ }})).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". iIntros (Φ) "H2".
    iRevert (He Φ) "H2".
    iRevert (i e E Φ') "H". iApply lwp_ind_strong; first solve_proper.
    iIntros "!#" (i e E1 Φ') "IH". iIntros (He Φ) "HΦ".
    rewrite lwp_unfold /lwp_pre /lwp_step. inv He. rename H0 into He. rewrite !He.
    rewrite fill_not_val; last auto.
    iIntros (K1 ?????? HK1 LU1) "SI". iMod ("IH" $! (K1 ∘ K) with "[] [//] SI") as "IH".
    { iPureIntro. apply _. }
    iModIntro. iMod "IH" as "(%& IH)". iModIntro. iSplit.
    { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
    iIntros (e2 σ2 efs Hstep).
    destruct (fill_step_inv (K:=K) i e σ1 (dom Θ) κ e2 σ2 efs) as (e2'&->&?); auto.
    iDestruct ("IH" $! _ _ _ H0) as ">IH".
    iMod "IH" as ">>IH". iMod "IH". iDestruct "IH" as "(SI& IH& Efs)".
    rewrite (bi.sep_assoc). iSplitR "Efs"; cycle 1.
    { iModIntro. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% >[_ H]". done. }
    destruct (to_val e2') eqn:He2.
    - iDestruct "IH" as "[_ IH]". rewrite lwp_unfold /lwp_pre. rewrite He2. iPoseProof ("HΦ" with "IH") as "IH".
      rewrite sfgupd_sfmupd sfmupd_lwpupd_elim.
      unfold_lwpupd. iPoseProof ("IH" $! (K1) with "[] [] SI") as "IH".
      { iPureIntro. apply _. }
      { iPureIntro. rewrite lookup_union_l.
        - rewrite lookup_insert_eq. apply of_to_val in He2. rewrite He2. done.
        - apply fork_thread_ids in Hstep. apply not_elem_of_dom. apply elem_of_dom_2 in LU1. set_solver. }
      rewrite !dom_union_L; auto.
      iMod "IH" as "[$ H]". apply of_to_val in He2. rewrite He2. by iFrame.
    - iDestruct "IH" as "[IH _]".
      iPoseProof ("IH" with "[//] HΦ") as "IH".
      iModIntro. iFrame.
  Qed.

  Lemma lwp_lwpupd s i E e Φ :
    TCEq (to_val e) None →
    lWP e @ s; i; E {{ v, lwpupd i E (of_val v) (Φ v) }}
    ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply (lwp_bind_step id).
    iApply (lwp_strong_mono with "H"). 1,2: done.
    iIntros (?) "H". iModIntro. iMod "H".
    rewrite lwp_value_sfgupd'. by iFrame.
  Qed.

  Lemma lwp_sfmupd s i E e Φ :
    TCEq (to_val e) None →
    lWP e @ s; i; E {{ v, |={E}=>m (Φ v) }}
    ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply lwp_lwpupd.
    iApply (lwp_strong_mono with "H"). 1,2: done.
    iIntros (?) "H". iModIntro. iMod "H". by iFrame.
  Qed.

  Lemma lwp_bind_lwpupd K `{!LanguageCtx K} s i E e Φ :
    (lwpupd i E e (lWP e @ s; i; E {{ v, lwpupd i E (K (of_val v)) (lWP K (of_val v) @ s; i; E {{ Φ }}) }} ))
    ⊢ lwpupd i E (K e) (lWP K e @ s; i; E {{ Φ }}).
  Proof.
    revert Φ.
    cut (∀ Φ', (lWP e @ s; i; E {{ Φ' }}) -∗
               ∀ Φ, (∀ v, (Φ' v) -∗ (lwpupd i E (K (of_val v)) (lWP K (of_val v) @ s; i; E {{ Φ }}))) -∗
                    lwpupd i E (K e) (lWP K e @ s; i; E {{ Φ }})).
    { iIntros (help Φ) "H". iPoseProof (lwpupd_ctx with "H") as "H". iMod "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". iIntros (Φ) "H2".
    iRevert (Φ) "H2".
    iRevert (i e E Φ') "H". iApply lwp_ind_strong; first solve_proper.
    iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
    rewrite lwp_unfold /lwp_pre /lwp_step. destruct (to_val e) as [v|] eqn:He.
    { iPoseProof (lwpupd_ctx with "IH") as "IH". iMod "IH".
      iApply sfmupd_lwpupd_elim. iMod "IH". iModIntro.
      iPoseProof ("HΦ" with "IH") as "H". rewrite lwp_unfold /lwp_pre /lwp_step.
      apply of_to_val in He as <-. iFrame. }
    rewrite fill_not_val; last auto.
    iModIntro.
    iIntros (K1 ?????? HK1 LU1) "SI". iMod ("IH" $! (K1 ∘ K) with "[] [//] SI") as "IH".
    { iPureIntro. apply _. }
    iModIntro. iMod "IH" as "(%& IH)". iModIntro. iSplit.
    { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
    iIntros (e2 σ2 efs Hstep).
    destruct (fill_step_inv (K:=K) i e σ1 (dom Θ) κ e2 σ2 efs) as (e2'&->&?); auto.
    iDestruct ("IH" $! _ _ _ H0) as ">IH".
    iMod "IH" as ">>IH". iMod "IH". iDestruct "IH" as "(SI& IH& Efs)".
    rewrite (bi.sep_assoc). iSplitR "Efs"; cycle 1.
    { iModIntro. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% >[_ H]". done. }
    iDestruct "IH" as "[IH _]". iPoseProof ("IH" with "HΦ") as "IH".
    unfold_lwpupd. iPoseProof ("IH" $! (K1) with "[] [] SI") as "IH".
    { iPureIntro. apply _. }
    { iPureIntro. rewrite lookup_union_l.
      - rewrite lookup_insert_eq. done.
      - apply fork_thread_ids in Hstep. apply not_elem_of_dom. apply elem_of_dom_2 in LU1. set_solver. }
    { simpl. rewrite dom_union_L. iFrame. }
  Qed.

  Lemma lwpupd_lwp_lwpupd s i E e Φ :
    (lwpupd i E e (lWP e @ s; i; E {{ v, lwpupd i E (of_val v) (Φ v) }} ))
    ⊢ lwpupd i E e (lWP e @ s; i; E {{ Φ }}).
  Proof.
    iIntros "H". iApply (lwp_bind_lwpupd id).
    iMod "H". iModIntro.
    iApply (lwp_strong_mono with "H"). 1,2: done.
    iIntros (?) "H". iModIntro. iMod "H".
    rewrite lwp_value_sfgupd'. by iFrame.
  Qed.

  Lemma lwpupd_lwp_sfmupd s i E e Φ :
    lwpupd i E e (lWP e @ s; i; E {{ v, |={E}=>m (Φ v) }})
    ⊢ lwpupd i E e (lWP e @ s; i; E {{ Φ }}).
  Proof.
    iIntros "H". iApply lwpupd_lwp_lwpupd.
    iMod "H". iModIntro.
    iApply (lwp_strong_mono with "H"). 1,2: done.
    iIntros (?) "H". iModIntro. iMod "H". by iFrame.
  Qed.

  (** FIXME: does this hold when we have ∀ K in lwp? Just remove this if this is not used anywhere else. *)
  (* Lemma lwp_bind_inv K `{!LanguageCtx K} s i E e Φ : *)
  (*   lWP K e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, lWP K (of_val v) @ s; i; E {{ Φ }} }}. *)
  (* Proof. *)
  (*   iIntros "H". remember (K e) as e' eqn:He'. *)
  (*   iRevert (e He'). iRevert (i e' E Φ) "H". iApply lwp_ind_strong; first solve_proper. *)
  (*   iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->). *)
  (*   rewrite !lwp_unfold {2}/lwp_pre. *)
  (*   destruct (to_val e) as [v|] eqn:He. *)
  (*   { apply of_to_val in He as <-. iModIntro. rewrite !lwp_unfold. *)
  (*     iApply (lwp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]". } *)
  (*   rewrite /lwp_pre fill_not_val; [|done]. *)
  (*   iIntros (K1 ?????? HK1 LU1) "SI". iMod ("IH" $! (K1 ∘ K) with "[] [//] SI") as "IH". *)
  (*   iModIntro. iPoseProof "IH" as "(%& IH)". iSplitR. *)
  (*   { destruct s; eauto using reducible_fill_inv. } *)
  (*   iIntros (e2 σ2 efs Hstep). iDestruct ("IH" with "[]") as ">IH". *)
  (*   { eauto using fill_step. } *)
  (*   iMod "IH" as ">>IH". iModIntro. iMod "IH" as "(SI& IH& Efs)". *)
  (*   iModIntro. iFrame. iSplitR "Efs". *)
  (*   - iDestruct "IH" as "[IH _]". by iApply "IH". *)
  (*   - iApply (big_sepM_impl with "Efs"). iIntros "!> %%% >[_ H]". done. *)
  (* Qed. *)

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
  Proof. intros <-. by apply lwp_value_sfgupd'. Qed.
  Lemma lwp_value' s i E Φ v : (Φ v) ⊢ lWP (of_val v) @ s; i; E {{ Φ }}.
  Proof.
    rewrite lwp_value_sfgupd'. iIntros "H". done.
  Qed.
  Lemma lwp_value s i E Φ e v : IntoVal e v → (Φ v) ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof. intros <-. apply lwp_value'. Qed.

  Lemma lwp_frame_l s i E e Φ R :
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma lwp_frame_r s i E e Φ R :
    lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }}.
  Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

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

  (** Later credits. *)
  Lemma lwp_lc_later_ord s i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s i E e Φ :
    £n n -∗ (▷^n lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lantanaGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  (** Modality instances for lwp. *)
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

  (* Global Instance elim_modal_lwpupd_lwp p s i E e P Φ : *)
  (*   ElimModal True p false (lwpupd i E e P) P (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Φ }}). *)
  (* Proof. *)
  (*   rewrite /ElimModal intuitionistically_if_elim. *)
  (*   iIntros (_) "[P H]". iApply lwpupd_elim_lwp. iMod "P". *)
  (*   iModIntro. by iApply ("H" with "P"). *)
  (* Qed. *)

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

  Global Instance elim_modal_sfgupd_lwp_atomic p s i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=>g P) P
            (lWP e @ s; i; E1 {{ Φ }}) (lWP e @ s; i; E2 {{ v, |={E2,E1}=>g Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      sfgupd_frame_r wand_elim_r lwp_atomic_sfgupd.
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

  Global Instance add_modal_sfgupd_lwp s i E e P Φ :
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

  Global Instance elim_acc_lwp_atomic_sfgupd {X} i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
      (sfgupd E1 E2) (sfgupd E2 E1)
      α β γ (lWP e @ s; i; E1 {{ Φ }})
      (λ x, lWP e @ s; i; E2 {{ v, |={E2}=>g β x ∗ (γ x -∗? Φ v) }})%I | 100.
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

  Global Instance elim_acc_lwp_nonatomic_sfgupd {X} i E α β γ e s Φ :
    ElimAcc (X:=X) True (sfgupd E E) (sfgupd E E)
      α β γ (lWP e @ s; i; E {{ Φ }})
      (λ x, lWP e @ s; i; E {{ v, |={E}=>g β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_sfgupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
