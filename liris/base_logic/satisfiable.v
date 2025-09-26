(** Anothre version of the one in transfinite.base_logic.lib; with rupd *)

TODO

From transfinite.stepindex Require Export existential_properties.
From iris.algebra Require Import functions gmap gmap_view gset coPset.
From transfinite.base_logic Require Import upred.
From transfinite.bi Require Export satisfiable.
From transfinite.base_logic.lib Require Import iprop own wsat fancy_updates.
From iris.proofmode Require Import proofmode.
Import uPred.


(* we first lift satisfiability from uPred to iProp *)
Definition iProp_sat_def `{SI: indexT} {Σ: gFunctors} := @uPred_primitive.uPred_sat SI (iResUR Σ).
Local Definition iProp_sat_aux : seal (@iProp_sat_def). Proof. by eexists. Qed.
Definition iProp_sat := iProp_sat_aux.(unseal).
Global Arguments iProp_sat {SI Σ} P.
Local Definition iProp_sat_eq : @iProp_sat = @iProp_sat_def := iProp_sat_aux.(seal_eq).
Local Instance: Params (@iProp_sat) 2 := {}.

Section iProp_sat.
  Context `{SI: indexT} {Σ: gFunctors}.

  Global Instance iProp_sat_instance: Satisfiable (@iProp_sat SI Σ).
  Proof. rewrite iProp_sat_eq /iProp_sat_def; apply _. Qed.

  Global Instance iProp_sat_bupd_instance: SatisfiableBUpd (@iProp_sat SI Σ).
  Proof. rewrite iProp_sat_eq /iProp_sat_def; apply _. Qed.

  Global Instance iProp_sat_later_instance: SatisfiableLater (@iProp_sat SI Σ).
  Proof. rewrite iProp_sat_eq /iProp_sat_def; apply _. Qed.

  Global Instance iProp_sat_exists_instance {X} `{!TypeExistentialProperty X SI}: SatisfiableExists X (@iProp_sat SI Σ).
  Proof. rewrite iProp_sat_eq /iProp_sat_def; apply _. Qed.

  (* introduction rule for iProp_sat *)
  Lemma iProp_sat_intro: iProp_sat (True%I: iProp Σ).
  Proof.
    rewrite iProp_sat_eq /iProp_sat_def; apply uPred_primitive.uPred_sat_intro.
  Qed.

End iProp_sat.



(* We develop a validity judgement where we can explicitly control
   the ghost names that are allocated *)
Definition alloc_names_def `{SI: indexT} {Σ: gFunctors} (G: gset gname) (P: iProp Σ): Prop :=
  (∃ m: iResUR Σ, ✓ m ∧ (∀ i, dom (m i) ⊆ G) ∧ (uPred_ownM m ⊢ P)).
Definition alloc_names_aux : seal (@alloc_names_def). by eexists. Qed.
Definition alloc_names := alloc_names_aux.(unseal).
Arguments alloc_names {SI Σ} _ _.
Definition alloc_names_eq : @alloc_names = @alloc_names_def := alloc_names_aux.(seal_eq).
Global Instance: Params (@alloc_names) 4 := {}.

(* we hide the names *)
Definition alloc `{SI: indexT} {Σ: gFunctors} (P: iProp Σ) := ∃ G, alloc_names G P.

Class Alloc `{SI: indexT} {Σ: gFunctors} (X: Type) (Φ: X → iProp Σ) (φ: Type):=
  can_alloc: ∀ P, φ → alloc P → ∃ x: X, alloc (P ∗ Φ x).

Global Hint Mode Alloc - - + ! - : typeclass_instances.
Global Arguments can_alloc {SI Σ X} Φ {φ _ _} _ _.

Section alloc.
  Context `{SI: indexT} {Σ: gFunctors}.

  Lemma alloc_names_empty : alloc_names ∅ (True%I: iProp Σ).
  Proof.
    rewrite alloc_names_eq /alloc_names_def. exists ε; split; first done.
    split; first done.
    apply True_intro.
  Qed.

  Lemma alloc_names_own `{!inG Σ A} (γ : gname) (a : A):
    ✓ a → alloc_names {[ γ ]} (own γ a).
  Proof.
    rewrite alloc_names_eq /alloc_names_def.
    intros Hv. exists (own.iRes_singleton γ a). split; [|split].
    - apply cmra_valid_validN=> n. by apply own.iRes_singleton_validN, cmra_valid_validN.
    - intros i γ'. rewrite /own.iRes_singleton /discrete_fun_singleton /discrete_fun_insert.
      destruct decide.
      + destruct e; simpl. by rewrite dom_singleton.
      + naive_solver.
    - by rewrite own.own_eq /own.own_def.
  Qed.

  Lemma alloc_names_combine G1 G2 (P Q: iProp Σ):
    alloc_names G1 P → alloc_names G2 Q → G1 ## G2 → alloc_names (G1 ∪ G2) (P ∗ Q)%I.
  Proof.
    rewrite alloc_names_eq /alloc_names_def; intros (m1 & V1 & H1 & HP) (m2 & V2 & H2 & HQ) G12.
    exists (λ i, m1 i ⋅ m2 i). split; [|split].
    - intros i γ. rewrite lookup_op.
      specialize (H1 i). specialize (H2 i).
      destruct (m1 i !! γ) as [r|] eqn: EQ1; first destruct (m2 i !! γ) as [r'|] eqn: EQ2.
      + assert (γ ∈ dom (m1 i))
          by by apply (elem_of_dom_2 (m1 i) γ r (D := (gset gname))).
        assert (γ ∈ dom (m2 i))
          by by apply (elem_of_dom_2 (m2 i) γ r' (D := (gset gname))).
        set_solver.
      + rewrite EQ2 right_id. apply V1.
      + rewrite EQ1 left_id. apply V2.
    - intros i. rewrite dom_op. set_solver.
    - by rewrite ownM_op HP HQ.
  Qed.

  Lemma alloc_names_mono G (P Q: iProp Σ):
    (P ⊢ Q) → alloc_names G P → alloc_names G Q.
  Proof.
    rewrite alloc_names_eq /alloc_names_def.
    intros PQ (m & V & H & HP).
    exists m; split; last split; eauto.
    by rewrite HP PQ.
  Qed.

  Lemma alloc_names_weaken G1 G2 (P: iProp Σ):
    alloc_names G1 P → G1 ⊆ G2 → alloc_names G2 P.
  Proof.
    rewrite alloc_names_eq /alloc_names_def.
    intros (m & V & H & HP) Hsub.
    exists m; split; last split; eauto.
    set_solver.
  Qed.


  Lemma alloc_names_iProp_sat G (P: iProp Σ):
    alloc_names G P → iProp_sat P.
  Proof.
    rewrite iProp_sat_eq /iProp_sat_def alloc_names_eq /alloc_names_def.
    intros (m & V & H & HP); simpl.
    intros α. exists m. split.
    - by apply cmra_valid_validN.
    - destruct HP as [HP]. apply HP; first by apply cmra_valid_validN.
      unseal. rewrite /upred.uPred_ownM_def. exists ε.
      by rewrite right_id.
  Qed.

  (* derived *)
  Lemma alloc_names_own_fresh G (P: iProp Σ) {A: cmra} (a: A) `{!inG Σ A}:
    alloc_names G P → ✓ a → ∃ γ, alloc_names (G ∪ {[γ]}) (P ∗ own γ a).
  Proof.
    intros Halloc Hv. exists (fresh G).
    apply alloc_names_combine; first done.
    - by apply alloc_names_own.
    - apply disjoint_singleton_r, is_fresh.
  Qed.

  (* allocation with the name hidden *)
  Lemma alloc_intro: alloc (True%I: iProp Σ).
  Proof.
    exists ∅. apply alloc_names_empty.
  Qed.

  Lemma alloc_fresh_res {A: cmra} `{!inG Σ A} (a: A) P:
    ✓ a → alloc P → ∃ γ, alloc (P ∗ own γ a).
  Proof.
    intros Hv [G Halloc].
    destruct (alloc_names_own_fresh G P a) as [γ Ha]; [done..|].
    by eexists γ, _.
  Qed.

  Lemma alloc_mono (P Q: iProp Σ):
    (P ⊢ Q) → alloc P → alloc Q.
  Proof.
    intros H [G Hx]; exists G; by eapply alloc_names_mono.
  Qed.

  Global Instance alloc_mono_impl: Proper ((⊢) ==> impl) (@alloc SI Σ).
  Proof.
    intros P Q Hent Ha; by eapply alloc_mono.
  Qed.

  Global Instance alloc_mono_iff: Proper ((≡) ==> iff) (@alloc SI Σ).
  Proof.
    intros P Q [? ?] % equiv_entails; split; by eapply alloc_mono.
  Qed.

  Lemma alloc_iProp_sat (P: iProp Σ): alloc P → iProp_sat P.
  Proof. intros [G ?]; by eapply alloc_names_iProp_sat. Qed.

  (* this instance can be used to allocate some ghost state *)
  Global Instance alloc_gname_inst {A: cmra} `{!inG Σ A} (a: A):
    Alloc gname (λ γ, own γ a) (✓ a).
  Proof.
    intros ???; by eapply alloc_fresh_res.
  Qed.

  (* this instance can be used to allocate invariants *)
  Global Instance alloc_wsat_inst `{!wsatGpreS Σ}:
    Alloc (wsatGS Σ) (λ _, wsat ∗ ownE ⊤)%I True.
  Proof.
    intros P _ HP.
    inv wsatGpreS0.
    (* assert (wsatGpreS_inv0 : inG Σ (gmap_viewR positive (agreeR (laterO (iPropO Σ))))). *)
    (* { inv wsatGpreS0. auto. }     *)
    eapply (can_alloc (λ γ, own γ (gmap_view_auth (DfracOwn 1) (∅ : gmap gname (agreeR $ laterO (iPropO Σ)))))) in HP as [γI HP];
      last by apply gmap_view_auth_valid.
    eapply (can_alloc (λ γ, own γ (CoPset ⊤))) in HP as [γE HP];
      last by done.
    eapply (can_alloc (λ γ, own γ (GSet ∅))) in HP as [γD HP];
      last by done.
    eexists (WsatG _ _ _ γI γE γD). Unshelve.
    2:{ split; auto. }
    rewrite /wsat /ownE -lock; eapply alloc_mono, HP.
    simpl. iIntros "[[[$ ?] $] ?]".
    iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
  Qed.

End alloc.


(* we create a notion of satisfiability which includes invariant masks *)
Class SatisfiableAtFupd `{SI: indexT} {Σ: gFunctors} `{!invGS Σ} (sat_at: coPset → iProp Σ → Prop) := {
  sat_fupd E1 E2 P: sat_at E1 (|={E1, E2}=> P)%I → sat_at E2 P
}.

Class SatisfiableAt `{SI: indexT} {Σ: gFunctors} `{!invGS Σ} (sat_at: coPset → iProp Σ → Prop) := {
  #[global] sat_at_satisfiable E :: Satisfiable (sat_at E);
  #[global] sat_at_bupd E :: SatisfiableBUpd (sat_at E);
  #[global] sat_at_later E :: SatisfiableLater (sat_at E);
  #[global] sat_at_fupd :: SatisfiableAtFupd sat_at
}.

Notation SatisfiableAtExists X sat_at := (∀ E, SatisfiableExists X (sat_at E)).

(** TODO: need updates to handle later credits. *)

(* (* there is a canonical satisfiability instance for every notion of satisfiable *) *)
(* Section canonical_sat_at. *)
(*   Context `{SI: indexT} {Σ: gFunctors} `{!invGS Σ} {sat: iProp Σ → Prop} `{!Satisfiable sat} `{!SatisfiableBUpd sat} `{!SatisfiableLater sat}. *)

(*   Definition sat_at E := (sat_frame (sat := sat) (wsat ∗ ownE E)%I). *)

(*   Global Instance sat_at_satisfiable_at_fupd: *)
(*     SatisfiableAtFupd sat_at. *)
(*   Proof using Type*. *)
(*     split; unfold sat_at, sat_frame; intros E1 E2 P Hs; eapply sat_later, sat_bupd, sat_mono, Hs. *)
(*     iIntros "((W & O) & P)". *)
(*     rewrite fancy_updates.uPred_fupd_unseal. *)
(*     iSpecialize ("P" with "[W O]"); first by iFrame. *)
(*     iMod "P". iModIntro. iApply except_0_later. *)
(*     rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def. *)
(*     iMod "P" as "($ & $ & $)". *)
(*   Qed. *)

(*   Global Instance sat_at_satisfiable_at: SatisfiableAt sat_at. *)
(*   Proof using Type*. *)
(*     split; apply _. *)
(*   Qed. *)

(* End canonical_sat_at. *)

(* Notation iProp_sat_at := (sat_at (sat := iProp_sat)). *)


(* (* framing preserves SatisfiableAtFUpd *) *)
(* Section sat_at_frame. *)
(*   Context `{SI: indexT} {Σ: gFunctors} `{!invG Σ} {sat_at: coPset → iProp Σ → Prop}. *)

(*   Definition sat_at_frame F E P := sat_frame (sat := sat_at E) F P. *)

(*   Global Instance sat_at_frame_satisfiable_at_fupd `{!∀ E, Satisfiable (sat_at E)} `{!SatisfiableAtFupd sat_at} F: *)
(*      SatisfiableAtFupd (sat_at_frame F). *)
(*   Proof. *)
(*     split; unfold sat_at_frame, sat_frame. intros E1 E2 P Hs; eapply sat_fupd, sat_mono, Hs. *)
(*     iIntros "[$ $]". *)
(*   Qed. *)

(*   Global Instance sat_at_frame_satisfiable_at `{!SatisfiableAt sat_at} F: SatisfiableAt (sat_at_frame F). *)
(*   Proof. *)
(*     split; apply _. *)
(*   Qed. *)
(* End sat_at_frame. *)
