From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From liris.algebra Require Import map_of_sets forest.

Section forest.
  Context {V : Type}.
  Context `{!EqDecision V} `{!Countable V}.
  Implicit Type t : tree V.
  Implicit Type f : forest V.
  Implicit Type v u ρ π : V.
  Implicit Type C : gset V.

  (** ** Definitions *)
  Definition forest_subseteq (f1 f2 : forest V) : Prop := f1 ⊆ f2.
  (** Only keeps trees where roots are in the set rs. *)
  Definition forest_filter_roots (f : forest V) (rs : gset V) : forest V :=
    filter (λ '(r, _), r ∈ rs) f.

  (** ** forest_subseteq lemmas *)
  Lemma forest_trees_disjoint_spec_1 f :
    forest_trees_disjoint f → ∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using.
    intros. unfold forest_trees_disjoint in H0. apply elem_of_map_to_list, list_elem_of_lookup in H1, H2.
    destruct H1 as (i1& LU1), H2 as (i2& LU2). assert (Ne : i1 ≠ i2).
    { intros <-. rewrite LU1 in LU2. simplify_eq. }
    specialize (H i1 i2). apply H; auto.
    { unfold forest_to_trees. rewrite list_lookup_fmap LU1. done. }
    { unfold forest_to_trees. rewrite list_lookup_fmap LU2. done. }
  Qed.

  Lemma forest_trees_disjoint_spec_2 f :
    (∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2) → forest_trees_disjoint f.
  Proof using.
    intros. unfold forest_trees_disjoint. intros ???????.
    unfold forest_to_trees in H1, H2. apply list_lookup_fmap_Some_1 in H1, H2.
    destruct H1 as (?&?&?), H2 as (?&?&?). destruct x, x0. simplify_eq. simpl.
    assert (∃ j,  map_to_list f !! j = Some (v, g)) by eauto. apply list_elem_of_lookup in H1.
    assert (∃ j,  map_to_list f !! j = Some (v0, g0)) by eauto. apply list_elem_of_lookup in H2.
    apply elem_of_map_to_list in H1, H2. assert (v ≠ v0).
    { intros <-. rewrite H1 in H2. simplify_eq. pose proof (NoDup_map_to_list f).
      eapply (NoDup_lookup _ j1 j2) in H3; eauto. }
    eapply H; eauto.
  Qed.

  Lemma forest_trees_disjoint_spec f :
    forest_trees_disjoint f ↔ ∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using. split; [apply forest_trees_disjoint_spec_1 | apply forest_trees_disjoint_spec_2]. Qed.

  Lemma forest_subseteq_wf f1 f2 :
    forest_wf f2 →
    forest_subseteq f1 f2 →
    forest_wf f1.
  Proof using.
    intros. rewrite /forest_subseteq map_subseteq_spec in H0. destruct H. split.
    - apply forest_trees_disjoint_spec. intros. rewrite forest_trees_disjoint_spec in H.
      eapply (H r1 r2 t1 t2); auto.
    - intros ???. eapply H1; eauto.
  Qed.

  (** ** forest_filter_roots lemmas *)
  Lemma forest_filter_roots_subseteq f rs :
    forest_subseteq (forest_filter_roots f rs) f.
  Proof using. apply map_filter_subseteq. Qed.

  Lemma forest_filter_roots_disjoint f rs1 rs2 :
    forest_wf f →
    rs1 ## rs2 →
    forest_disjoint (forest_filter_roots f rs1) (forest_filter_roots f rs2).
  Proof using.
    intros. apply map_disjoint_spec. intros.
    apply map_lookup_filter_Some in H1, H2. destruct H1, H2.
    set_solver.
  Qed.

End forest.

Section map_of_forests.
  Context {K V : Type}.
  Context `{!EqDecision K} `{!Countable K} `{!EqDecision V} `{!Countable V}.

  (** ** Definitions *)
  (** F is a forest, Rs is the map of roots.
      forest_to_forests transforms F into a map of forests, where the roots are given as Rs. *)
  Definition forest_to_forests (F : forest V) (Rs : gmap K (gset V)) : gmap K (forest V) :=
    (λ rs, forest_filter_roots F rs) <$> Rs.

  (** Conditions for the forest_to_forests operation to be well-formed. *)
  Definition forest_to_forests_wf (F : forest V) (Rs : gmap K (gset V)) : Prop :=
    disjoint_sets Rs ∧ (dom F = union_sets Rs) ∧ forest_wf F.

  (** ** Lemmas *)
  Lemma forest_to_forests_lookup F Rs k f :
    forest_to_forests F Rs !! k = Some f →
    ∃ rs, Rs !! k = Some rs ∧ f = forest_filter_roots F rs.
  Proof using.
    intros. apply lookup_fmap_Some in H. destruct H as (rs&?&?). eauto.
  Qed.

  Lemma forest_to_forests_disjoint_forest F Rs k1 k2 f1 f2 :
    forest_to_forests_wf F Rs →
    k1 ≠ k2 →
    forest_to_forests F Rs !! k1 = Some f1 →
    forest_to_forests F Rs !! k2 = Some f2 →
    forest_disjoint f1 f2.
  Proof using.
    intros. destruct H as (Disj& Dom& Fwf).
    apply lookup_fmap_Some in H1, H2. destruct H1 as (?&?&?), H2 as (?&?&?). simplify_eq.
    assert (x ## x0) by (eapply Disj; eauto).
    eapply forest_filter_roots_disjoint; eauto.
  Qed.

  Lemma forest_to_forests_lookup_wf F Rs k f :
    forest_to_forests_wf F Rs →
    forest_to_forests F Rs !! k = Some f →
    forest_wf f.
  Proof using.
    intros. apply forest_to_forests_lookup in H0. destruct H0 as (?&?&?).
    destruct H as (Disj& Dom& Fwf). eapply forest_subseteq_wf. 1: eapply Fwf.
    simplify_eq. apply forest_filter_roots_subseteq.
  Qed.

  (** ** Lemmas for forest_to_forests_wf F Rs on operations on the forest F. *)
  (** In this part, we state and prove lemmas where the roots Rs stays the same.
      Forest supports many operations, as defined in forest.v.
      That file contains useful lemmas for forest_wf under forest operations. *)

  (** ** Lemmas for forest_to_forests_wf F Rs on operations on the roots Rs. *)
  (** In this part, we state and prove lemmas where the roots Rs are updated.
    We can insert/delete keys of the map, and update each set in Rs.
    The map_of_sets.v file contains useful lemmas to work with disjoint_sets and union_sets. *)

End map_of_forests.
