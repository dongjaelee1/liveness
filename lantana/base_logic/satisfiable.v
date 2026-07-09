(** Another version of the one in transfinite.base_logic.lib; with rupd *)
From transfinite.stepindex Require Export existential_properties.
From iris.algebra Require Import functions gmap gmap_view gset coPset.
From transfinite.base_logic Require Import upred.
From transfinite.bi Require Export satisfiable.
From transfinite.base_logic.lib Require Import iprop own wsat.
From transfinite.base_logic.lib Require Export satisfiable.
From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Import fancy_updates.
Import uPred.

(** For the tlc version of fupd *)

(* we create a notion of satisfiability which includes invariant masks *)
Class SatisfiableAtFupd `{SI : indexT} {Σ : gFunctors} `{!invGS Σ} (sat_at : coPset → iProp Σ → Prop) := {
  sat_fupd E1 E2 P: sat_at E1 (|={E1, E2}=> P)%I → sat_at E2 P
}.

Class SatisfiableAt `{SI : indexT} {Σ : gFunctors} `{!invGS Σ} (sat_at : coPset → iProp Σ → Prop) := {
  #[global] sat_at_satisfiable E :: Satisfiable (sat_at E);
  #[global] sat_at_bupd E :: SatisfiableBUpd (sat_at E);
  #[global] sat_at_later E :: SatisfiableLater (sat_at E);
  #[global] sat_at_fupd :: SatisfiableAtFupd sat_at
}.

(* Notation SatisfiableAtExists X sat_at := (∀ E, SatisfiableExists X (sat_at E)). *)
Notation iProp_sat_lc := (sat_lc iProp_sat).

(* there is a canonical satisfiability instance for every notion of satisfiable *)
Section canonical_sat_at.
  Context `{SI : indexT} {Σ : gFunctors} `{!invGS Σ}.
  Context {sat : iProp Σ → Prop} `{!Satisfiable sat} `{!SatisfiableRUpd sat} `{!SatisfiableLater sat}.

  Definition sat_at E := (sat_frame (sat := sat) (wsat ∗ ownE E)%I).

  Global Instance sat_at_satisfiable_at_fupd :
    SatisfiableAtFupd sat_at.
  Proof using Type*.
    split; unfold sat_at, sat_frame; intros E1 E2 P Hs; eapply sat_later, sat_rupd, sat_mono, Hs.
    iIntros "((W & O) & P)".
    rewrite fancy_updates.uPred_fupd_unseal.
    iSpecialize ("P" with "[W O]"); first by iFrame.
    iMod "P". iModIntro. iApply except_0_later.
    iMod "P" as "($ & $ & $)".
  Qed.

  Global Instance sat_at_satisfiable_at_bupd E :
    SatisfiableBUpd (sat_at E).
  Proof using Type*.
    eapply sat_frame_satisfiable_bupd.
    Unshelve.
    econstructor. intros. apply SatisfiableRUpd0.
    eapply sat_mono; last eapply H.
    apply bupd_rupd.
  Qed.

  Global Instance sat_at_satisfiable_at: SatisfiableAt sat_at.
  Proof using Type*.
    split; apply _.
  Qed.

End canonical_sat_at.

Notation iProp_sat_lc_at := (sat_at (sat := iProp_sat_lc)).

(* framing preserves SatisfiableAtFUpd *)
Section sat_at_frame.
  Context `{SI : indexT} {Σ : gFunctors} `{!invGS Σ} {sat_at : coPset → iProp Σ → Prop}.

  Definition sat_at_frame F E P := sat_frame (sat := sat_at E) F P.

  Global Instance sat_at_frame_satisfiable_at_fupd `{!∀ E, Satisfiable (sat_at E)} `{!SatisfiableAtFupd sat_at} F :
     SatisfiableAtFupd (sat_at_frame F).
  Proof.
    split; unfold sat_at_frame, sat_frame. intros E1 E2 P Hs; eapply sat_fupd, sat_mono, Hs.
    iIntros "[$ $]".
  Qed.

  Global Instance sat_at_frame_satisfiable_at `{!SatisfiableAt sat_at} F :
    SatisfiableAt (sat_at_frame F).
  Proof.
    split; apply _.
  Qed.

End sat_at_frame.

Notation iProp_sat_lc_at_frame := (sat_at_frame (sat_at := iProp_sat_lc_at)).
