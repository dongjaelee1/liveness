(** * Ghost state of obligation forests

    The invariant [oforest Ω Θ] is the fifth conjunct of [model_interp]. Every live obligation
    of [Ω] is a node of the forest and has a parent: a thread or another obligation ([Par]).
    The children of each parent are kept in a ghost map ([Kids]) whose fragments are the
    children predicates of the logic.

    - The owner of an obligation (in [Ω]) is the owner of its parent; children of a thread are
      owned by that thread.
    - An obligation [x] whose parent is an obligation [c] stores a piece of its own fuel that
      is strictly larger than the (model) fuel of [c]. Hence, when [c] makes progress, [x] can
      split one unit off this piece and still be larger than the new fuel of [c]: the children
      of an obligation burn fuel together with it, without any user resource.
    - The fuel of every obligation stays below its initial fuel ([oblG_bound]). *)

From iris.algebra Require Import reservation_map.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.algebra Require Import bank.
From lantana.base_logic Require Export osat othread parent model_rel.
From transfinite.base_logic.lib Require Import ghost_map.

Module oforestGS.

  Class oforestGpreS `{SI : sidx} (Σ : gFunctors) : Set :=
    OforestGpreS {
        #[local] oforestGpreS_kids :: ghost_mapG Σ parent (gset oid);
      }.

  Class oforestGS `{SI : sidx} (Σ : gFunctors) : Set :=
    OforestG {
        oforest_inG : oforestGpreS Σ;
        kids_name : gname;
      }.

  Definition oforestΣ `{SI : sidx} : gFunctors := #[ghost_mapΣ parent (gset oid)].

  Global Instance subG_oforestΣ `{SI : sidx} {Σ} : subG oforestΣ Σ → oforestGpreS Σ.
  Proof. solve_inG. Qed.

End oforestGS.
Import oforestGS.

Local Existing Instances oforest_inG oforestGpreS_kids.

(** ** Children fragments *)
Definition oforestG_kids `{SI : sidx} `{!oforestGS Σ} (p : parent) (K : gset oid) : iProp Σ :=
  ghost_map_elem kids_name p (DfracOwn 1) K.
Global Typeclasses Opaque oforestG_kids.
Global Instance: Params (@oforestG_kids) 3 := {}.

Local Definition oforestG_kids_auth `{SI : sidx} `{!oforestGS Σ}
  (Kids : gmap parent (gset oid)) : iProp Σ :=
  ghost_map_auth kids_name (DfracOwn 1) Kids.

(** ** Reading the model *)
Definition obl_fuel_of (Ω : obls) (x : oid) : obl_fuel :=
  match Ω !! x with
  | Some (obl_assigned a _) => a
  | _ => Ord.O
  end.

Definition obl_owner_of (Ω : obls) (x : oid) : option positive :=
  match Ω !! x with
  | Some (obl_assigned _ t) => Some t
  | _ => None
  end.

(** The obligations of [D] owned by thread [i]. *)
Definition forest_owned (Ω : obls) (D : gset oid) (i : positive) : gset oid :=
  filter (λ x, obl_owner_of Ω x = Some i) D.

(** ** Well-formedness of the forest *)
Record forest_wf (Ω : obls) (Θ : gset positive)
  (Par : gmap oid parent) (Kids : gmap parent (gset oid)) : Prop := {
  (** Every thread of the pool and every node has an entry for its children. *)
  fwf_kids_dom p :
    is_Some (Kids !! p) ↔ (match p with PThread i => i ∈ Θ | PObl x => x ∈ dom Par end);
  (** [Kids] is the inverse of [Par]. *)
  fwf_par_kids x p : Par !! x = Some p ↔ ∃ K, Kids !! p = Some K ∧ x ∈ K;
  (** The nodes are the live obligations. *)
  fwf_par_live x : x ∈ dom Par ↔ ∃ a t, Ω !! x = Some (obl_assigned a t);
  (** Children of a thread are owned by it. *)
  fwf_thread x i : Par !! x = Some (PThread i) → obl_owner_of Ω x = Some i;
  (** Children of an obligation have its owner and more fuel. *)
  fwf_obl x c :
    Par !! x = Some (PObl c) →
    obl_owner_of Ω c = obl_owner_of Ω x ∧ (obl_fuel_of Ω c < obl_fuel_of Ω x)%ord;
  (** Owners are threads of the pool. *)
  fwf_owner x i : x ∈ dom Par → obl_owner_of Ω x = Some i → i ∈ Θ;
}.

(** What the invariant holds for each node [x] with parent [p]. *)
Definition forest_node `{SI : sidx} `{!osatGS.osatGS Σ} `{!othreadGS.othreadGS Σ}
  (Ω : obls) (x : oid) (p : parent) : iProp Σ :=
  oblG_elem x ∗
  (∃ i, ⌜ obl_owner_of Ω x = Some i ⌝ ∗
        oblG_owner x i (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns i x (1/2 + 1/2/2)%Qp) ∗
  (∃ β, oblG_bound x β ∗ ⌜ (obl_fuel_of Ω x <= β)%ord ⌝) ∗
  (match p with
   | PObl c => ∃ π, ⌜ (obl_fuel_of Ω c < π)%ord ⌝ ∗ oblG_fuel x π
   | PThread _ => True
   end).

(** A node of thread [i]'s tree right after it split off the unit for a step of [i]: its
    piece is exactly the fuel its parent had. *)
Definition forest_node_stepped `{SI : sidx} `{!osatGS.osatGS Σ} `{!othreadGS.othreadGS Σ}
  (Ω : obls) (i : positive) (x : oid) (p : parent) : iProp Σ :=
  oblG_elem x ∗
  (∃ t, ⌜ obl_owner_of Ω x = Some t ⌝ ∗
        oblG_owner x t (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns t x (1/2 + 1/2/2)%Qp) ∗
  (∃ β, oblG_bound x β ∗ ⌜ (obl_fuel_of Ω x <= β)%ord ⌝) ∗
  (match p with
   | PObl c => ∃ π, ⌜ if decide (obl_owner_of Ω x = Some i) then π = obl_fuel_of Ω c
                    else (obl_fuel_of Ω c < π)%ord ⌝ ∗ oblG_fuel x π
   | PThread _ => True
   end).

(** The invariant. *)
Definition oforest `{SI : sidx} `{!osatGS.osatGS Σ} `{!othreadGS.othreadGS Σ} `{!oforestGS Σ}
  (Ω : obls) (Θ : gset positive) : iProp Σ :=
  locked
    (∃ (Par : gmap oid parent) (Kids : gmap parent (gset oid)),
        oforestG_kids_auth Kids ∗
        ⌜ forest_wf Ω Θ Par Kids ⌝ ∗
        ([∗ set] i ∈ Θ, othreadG_elem i ∗
           ((othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i (forest_owned Ω (dom Par) i)) ∨
            (othreadG_done i ∗ oforestG_kids (PThread i) ∅ ∗ ⌜ forest_owned Ω (dom Par) i = ∅ ⌝))) ∗
        ([∗ map] x ↦ p ∈ Par, forest_node Ω x p))%I.

(** * Pure facts about forests *)
Section forest_pure.
  Implicit Types (Ω : obls) (Θ : gset positive) (Par : gmap oid parent)
    (Kids : gmap parent (gset oid)).

  Lemma forest_wf_empty : forest_wf ∅ ∅ ∅ ∅.
  Proof.
    split.
    - intros []; rewrite lookup_empty ?dom_empty_L; split; intros H; try (by destruct H); set_solver.
    - intros x p. rewrite !lookup_empty. split; [done|]. intros (?& ?& _); done.
    - intros x. rewrite dom_empty_L lookup_empty. split; [set_solver|]. intros (?&?&?); done.
    - done.
    - done.
    - set_solver.
  Qed.

  (** A thread without children owns no node (every node has a chain of parents ending at
      its owner, by well-founded induction on the fuel). *)
  Lemma forest_wf_owned_empty Ω Θ Par Kids i :
    forest_wf Ω Θ Par Kids →
    Kids !! PThread i = Some ∅ →
    forest_owned Ω (dom Par) i = ∅.
  Proof.
    intros WF Hi. apply set_eq. intros x. rewrite elem_of_filter. split; last set_solver.
    intros [Hx Hdom]. exfalso.
    remember (obl_fuel_of Ω x) as f eqn:Hf. revert x Hf Hx Hdom.
    induction f as [f IH] using (well_founded_induction WFOCM.lt_wf).
    intros x -> Hx Hdom. apply elem_of_dom in Hdom as [p Hp]. destruct p as [j|c].
    - pose proof (fwf_thread _ _ _ _ WF _ _ Hp) as Hj. rewrite Hx in Hj. injection Hj as <-.
      destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hp) as (K& HK& Hin). rewrite Hi in HK.
      injection HK as <-. set_solver.
    - destruct (fwf_obl _ _ _ _ WF _ _ Hp) as [Ho Hlt].
      destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hp) as (K& HK& _).
      assert (Hc : c ∈ dom Par).
      { apply (proj1 (fwf_kids_dom _ _ _ _ WF (PObl c))). eauto. }
      eapply (IH (obl_fuel_of Ω c)); [exact Hlt|reflexivity| |exact Hc]. by rewrite Ho.
  Qed.

  Lemma forest_owned_not_in_pool Ω Θ Par Kids i :
    forest_wf Ω Θ Par Kids → i ∉ Θ → forest_owned Ω (dom Par) i = ∅.
  Proof.
    intros WF Hi. apply set_eq. intros x. rewrite elem_of_filter. split; last set_solver.
    intros [Hx Hdom]. exfalso. apply Hi. by eapply fwf_owner.
  Qed.

  Lemma forest_wf_alloc_thread Ω Θ Par Kids i :
    forest_wf Ω Θ Par Kids → i ∉ Θ →
    forest_wf Ω ({[i]} ∪ Θ) Par (<[PThread i := ∅]> Kids).
  Proof.
    intros WF Hi. split.
    - intros p. destruct (decide (p = PThread i)) as [->|Hne].
      + rewrite lookup_insert_eq. split; [set_solver|eauto].
      + rewrite lookup_insert_ne; last done. rewrite (fwf_kids_dom _ _ _ _ WF p).
        destruct p; [|done]. set_solver.
    - intros x p. destruct (decide (p = PThread i)) as [->|Hne].
      + rewrite lookup_insert_eq. split.
        * intros Hp. exfalso. apply Hi.
          destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hp) as (K& HK& _).
          apply (fwf_kids_dom _ _ _ _ WF (PThread i)). eauto.
        * intros (K& [=<-]& Hx). set_solver.
      + rewrite lookup_insert_ne; last done. apply WF.
    - apply WF.
    - apply WF.
    - apply WF.
    - intros x j Hx Hj. apply elem_of_union_r. by eapply fwf_owner.
  Qed.

  (** ** Reading the model after an update *)
  Lemma obl_fuel_of_insert_ne Ω k g x : x ≠ k → obl_fuel_of (<[k:=g]> Ω) x = obl_fuel_of Ω x.
  Proof. intros. by rewrite /obl_fuel_of lookup_insert_ne. Qed.
  Lemma obl_owner_of_insert_ne Ω k g x : x ≠ k → obl_owner_of (<[k:=g]> Ω) x = obl_owner_of Ω x.
  Proof. intros. by rewrite /obl_owner_of lookup_insert_ne. Qed.
  Lemma obl_fuel_of_insert_eq Ω k a i : obl_fuel_of (<[k:=obl_assigned a i]> Ω) k = a.
  Proof. by rewrite /obl_fuel_of lookup_insert_eq. Qed.
  Lemma obl_owner_of_insert_eq Ω k a i : obl_owner_of (<[k:=obl_assigned a i]> Ω) k = Some i.
  Proof. by rewrite /obl_owner_of lookup_insert_eq. Qed.

  Lemma forest_owned_insert_same Ω D k a i :
    k ∉ D → forest_owned (<[k:=obl_assigned a i]> Ω) ({[k]} ∪ D) i = {[k]} ∪ forest_owned Ω D i.
  Proof.
    intros Hk. apply set_eq. intros x.
    rewrite /forest_owned elem_of_union elem_of_singleton !elem_of_filter elem_of_union elem_of_singleton.
    destruct (decide (x = k)) as [->|Hne].
    - rewrite obl_owner_of_insert_eq. naive_solver.
    - rewrite obl_owner_of_insert_ne //. naive_solver.
  Qed.

  Lemma forest_owned_insert_other Ω D k a i j :
    k ∉ D → j ≠ i →
    forest_owned (<[k:=obl_assigned a i]> Ω) ({[k]} ∪ D) j = forest_owned Ω D j.
  Proof.
    intros Hk Hj. apply set_eq. intros x.
    rewrite /forest_owned !elem_of_filter elem_of_union elem_of_singleton.
    destruct (decide (x = k)) as [->|Hne].
    - rewrite obl_owner_of_insert_eq. split; intros [H1 H2]; [simplify_eq|done].
    - rewrite obl_owner_of_insert_ne //. naive_solver.
  Qed.

  (** ** A new leaf below [p] *)
  Lemma forest_wf_alloc_obl Ω Θ Par Kids p K k a i :
    forest_wf Ω Θ Par Kids →
    Ω !! k = None →
    Kids !! p = Some K →
    (match p with
     | PThread j => j = i
     | PObl q => obl_owner_of Ω q = Some i ∧ (obl_fuel_of Ω q < a)%ord
     end) →
    forest_wf (<[k:=obl_assigned a i]> Ω) Θ (<[k:=p]> Par) (<[PObl k:=∅]> (<[p:={[k]} ∪ K]> Kids)).
  Proof.
    intros WF Hk HK Hp.
    assert (HkPar : Par !! k = None).
    { apply not_elem_of_dom. intros Hd. apply (fwf_par_live _ _ _ _ WF) in Hd as (?&?&Hx).
      by rewrite Hk in Hx. }
    assert (HkKids : Kids !! PObl k = None).
    { destruct (Kids !! PObl k) eqn:E; last done. exfalso. apply not_elem_of_dom in HkPar.
      apply HkPar. apply (fwf_kids_dom _ _ _ _ WF (PObl k)). eauto. }
    assert (Hpk : p ≠ PObl k) by (intros ->; by rewrite HkKids in HK).
    assert (Hi : i ∈ Θ).
    { destruct p as [j|q].
      - subst j. apply (fwf_kids_dom _ _ _ _ WF (PThread i)). eauto.
      - destruct Hp as [Hq _]. eapply (fwf_owner _ _ _ _ WF q); last done.
        apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    assert (Hdomk : ∀ c, c ∈ dom Par → c ≠ k).
    { intros c Hc ->. apply not_elem_of_dom in HkPar. done. }
    split.
    - intros p'. destruct (decide (p' = PObl k)) as [->|H1].
      { rewrite lookup_insert_eq dom_insert_L. split; [set_solver|eauto]. }
      rewrite lookup_insert_ne //.
      assert (is_Some (<[p:={[k]} ∪ K]> Kids !! p') ↔ is_Some (Kids !! p')) as ->.
      { destruct (decide (p' = p)) as [->|H2].
        - rewrite lookup_insert_eq HK. split; eauto.
        - by rewrite lookup_insert_ne. }
      rewrite (fwf_kids_dom _ _ _ _ WF p'). destruct p' as [j|x]; first done.
      rewrite dom_insert_L. assert (x ≠ k) by (intros ->; done). set_solver.
    - intros x p'. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. split.
        * intros [= <-]. exists ({[k]} ∪ K). rewrite lookup_insert_ne // lookup_insert_eq.
          set_solver.
        * intros (K'& HK'& Hin). destruct (decide (p' = PObl k)) as [->|H1].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. set_solver. }
          rewrite lookup_insert_ne // in HK'. destruct (decide (p' = p)) as [->|H2]; first done.
          rewrite lookup_insert_ne // in HK'. exfalso.
          assert (Par !! k = Some p') as Hpar by (apply (fwf_par_kids _ _ _ _ WF); eauto).
          by rewrite HkPar in Hpar.
      + rewrite lookup_insert_ne // (fwf_par_kids _ _ _ _ WF x p'). split.
        * intros (K'& HK'& Hin). destruct (decide (p' = PObl k)) as [->|H1].
          { by rewrite HkKids in HK'. }
          rewrite lookup_insert_ne //. destruct (decide (p' = p)) as [->|H2].
          { rewrite lookup_insert_eq. rewrite HK in HK'. injection HK' as <-.
            exists ({[k]} ∪ K). set_solver. }
          rewrite lookup_insert_ne //. eauto.
        * intros (K'& HK'& Hin). destruct (decide (p' = PObl k)) as [->|H1].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. set_solver. }
          rewrite lookup_insert_ne // in HK'. destruct (decide (p' = p)) as [->|H2].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. exists K. split; first done.
            set_solver. }
          rewrite lookup_insert_ne // in HK'. eauto.
    - intros x. rewrite dom_insert_L elem_of_union elem_of_singleton.
      destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. naive_solver.
      + rewrite lookup_insert_ne // -(fwf_par_live _ _ _ _ WF x). naive_solver.
    - intros x j. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= ->]. subst j. by rewrite obl_owner_of_insert_eq.
      + rewrite lookup_insert_ne // obl_owner_of_insert_ne //. apply WF.
    - intros x c. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= ->]. destruct Hp as [Hq Hlt].
        assert (c ≠ k).
        { apply Hdomk. apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
        rewrite obl_owner_of_insert_ne // obl_fuel_of_insert_ne // obl_owner_of_insert_eq
          obl_fuel_of_insert_eq. done.
      + rewrite lookup_insert_ne //. intros Hxc.
        assert (c ≠ k).
        { apply Hdomk. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hxc) as (K'& HK'& _).
          apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
        rewrite !obl_owner_of_insert_ne // !obl_fuel_of_insert_ne //. by apply WF.
    - intros x j. rewrite dom_insert_L elem_of_union elem_of_singleton.
      destruct (decide (x = k)) as [->|Hx].
      + rewrite obl_owner_of_insert_eq. by intros _ [= <-].
      + rewrite obl_owner_of_insert_ne //. intros [?|Hd] Hj; first done.
        by eapply (fwf_owner _ _ _ _ WF).
  Qed.

  (** ** Physical steps of thread [i] *)
  Lemma prog_owned Ω Ω' i x a :
    (Ω ↪ₚ Ω' | obl_cond_owner i) → Ω !! x = Some (obl_assigned a i) →
    ∃ a' t', Ω' !! x = Some (obl_assigned a' t') ∧ (a' < a)%ord.
  Proof.
    intros [Hs Hk] Hx. pose proof (Hs x) as Hsx. pose proof (Hk x) as Hkx.
    rewrite Hx in Hsx Hkx.
    destruct (Ω' !! x) as [g2|] eqn:E; inversion Hsx as [? ? Hr|]; subst.
    inversion Hkx as [? ? Hkeep|]; subst.
    destruct Hr as [[_ Hst]|[Hn _]]; last (exfalso; by apply Hn).
    inversion Hst as [? ? Hp|? ? Hd]; subst.
    - inversion Hp; subst. eauto.
    - inversion Hd; subst. done.
  Qed.

  Lemma prog_other Ω Ω' i x g :
    (Ω ↪ₚ Ω' | obl_cond_owner i) → Ω !! x = Some g → ¬ obl_cond_owner i x g → Ω' !! x = Some g.
  Proof.
    intros [Hs _] Hx Hn. pose proof (Hs x) as Hsx. rewrite Hx in Hsx.
    destruct (Ω' !! x) as [g2|] eqn:E; inversion Hsx as [? ? Hr|]; subst.
    destruct Hr as [[Hc _]|[_ ->]]; [done|done].
  Qed.

  Lemma prog_live Ω Ω' i x :
    (Ω ↪ₚ Ω' | obl_cond_owner i) →
    (∃ a t, Ω !! x = Some (obl_assigned a t)) ↔ (∃ a t, Ω' !! x = Some (obl_assigned a t)).
  Proof.
    intros Hp. split.
    - intros (a& t& Hx). destruct (decide (t = i)) as [->|Hne].
      + destruct (prog_owned _ _ _ _ _ Hp Hx) as (a'& t'& Hx'& _). eauto.
      + exists a, t. eapply prog_other; [done|done|]. simpl. done.
    - intros (a'& t'& Hx'). destruct Hp as [Hs Hk]. pose proof (Hk x) as Hkx.
      rewrite Hx' in Hkx. destruct (Ω !! x) as [g1|] eqn:E; inversion Hkx as [? ? Hkeep|]; subst.
      destruct g1; [eauto|done].
  Qed.

  Lemma forest_owned_ext Ω Ω' D i :
    (∀ x, x ∈ D → obl_owner_of Ω' x = obl_owner_of Ω x) →
    forest_owned Ω' D i = forest_owned Ω D i.
  Proof.
    intros H. apply set_eq. intros x. rewrite /forest_owned !elem_of_filter.
    split; intros [H1 H2]; split; try done; by rewrite ?H in H1 |- *.
  Qed.

  (** ** Removing a childless leaf (discharge) *)
  Lemma forest_owned_remove Ω D k g j :
    forest_owned (<[k:=g]> Ω) (D ∖ {[k]}) j = forest_owned Ω D j ∖ {[k]}.
  Proof.
    apply set_eq. intros x. rewrite /forest_owned elem_of_difference !elem_of_filter
      elem_of_difference elem_of_singleton.
    destruct (decide (x = k)) as [->|Hne]; first naive_solver.
    rewrite obl_owner_of_insert_ne //. naive_solver.
  Qed.

  Lemma forest_wf_discharge Ω Θ Par Kids p K k :
    forest_wf Ω Θ Par Kids →
    Par !! k = Some p →
    Kids !! p = Some K →
    Kids !! PObl k = Some ∅ →
    forest_wf (<[k:=obl_discharged]> Ω) Θ (delete k Par)
      (<[p:=K ∖ {[k]}]> (delete (PObl k) Kids)).
  Proof.
    intros WF Hk HK HKk.
    assert (HkK : k ∈ K).
    { destruct (proj1 (fwf_par_kids _ _ _ _ WF k p) Hk) as (K'& HK'& Hin).
      rewrite HK in HK'. by injection HK' as <-. }
    assert (Hpk : p ≠ PObl k) by (intros ->; rewrite HKk in HK; injection HK as <-; set_solver).
    assert (Hnochild : ∀ x, Par !! x ≠ Some (PObl k)).
    { intros x Hx. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& Hin).
      rewrite HKk in HK'. injection HK' as <-. set_solver. }
    split.
    - intros p'. destruct (decide (p' = p)) as [->|H1].
      { rewrite lookup_insert_eq. split; intros _; [|eauto].
        assert (Hp : is_Some (Kids !! p)) by eauto.
        apply (fwf_kids_dom _ _ _ _ WF p) in Hp.
        destruct p as [j|q]; first done.
        rewrite dom_delete_L. apply elem_of_difference. split; first done.
        intros ->%elem_of_singleton. done. }
      rewrite lookup_insert_ne //. destruct (decide (p' = PObl k)) as [->|H2].
      { rewrite lookup_delete_eq dom_delete_L. split; [intros []; done|set_solver]. }
      rewrite lookup_delete_ne // (fwf_kids_dom _ _ _ _ WF p'). destruct p' as [j|x]; first done.
      rewrite dom_delete_L. assert (x ≠ k) by (intros ->; done). set_solver.
    - intros x p'. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_delete_eq. split; [done|]. intros (K'& HK'& Hin).
        destruct (decide (p' = p)) as [->|H1].
        { rewrite lookup_insert_eq in HK'. injection HK' as <-. set_solver. }
        rewrite lookup_insert_ne // in HK'. destruct (decide (p' = PObl k)) as [->|H2].
        { by rewrite lookup_delete_eq in HK'. }
        rewrite lookup_delete_ne // in HK'.
        assert (Par !! k = Some p') as Hk' by (apply (fwf_par_kids _ _ _ _ WF); eauto).
        rewrite Hk in Hk'. by injection Hk' as ->.
      + rewrite lookup_delete_ne //. rewrite (fwf_par_kids _ _ _ _ WF x p'). split.
        * intros (K'& HK'& Hin). destruct (decide (p' = p)) as [->|H1].
          { rewrite lookup_insert_eq. rewrite HK in HK'. injection HK' as <-.
            exists (K ∖ {[k]}). set_solver. }
          rewrite lookup_insert_ne //. destruct (decide (p' = PObl k)) as [->|H2].
          { exfalso. apply (Hnochild x). apply (fwf_par_kids _ _ _ _ WF). eauto. }
          rewrite lookup_delete_ne //. eauto.
        * intros (K'& HK'& Hin). destruct (decide (p' = p)) as [->|H1].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. exists K.
            split; first done. set_solver. }
          rewrite lookup_insert_ne // in HK'. destruct (decide (p' = PObl k)) as [->|H2].
          { by rewrite lookup_delete_eq in HK'. }
          rewrite lookup_delete_ne // in HK'. eauto.
    - intros x. rewrite dom_delete_L elem_of_difference elem_of_singleton.
      destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. split; [naive_solver|]. intros (?&?&?); done.
      + rewrite lookup_insert_ne // -(fwf_par_live _ _ _ _ WF x). naive_solver.
    - intros x j Hx. destruct (decide (x = k)) as [->|Hne]; first by rewrite lookup_delete_eq in Hx.
      rewrite lookup_delete_ne // in Hx. rewrite obl_owner_of_insert_ne //. by apply WF.
    - intros x c Hx. destruct (decide (x = k)) as [->|Hne]; first by rewrite lookup_delete_eq in Hx.
      rewrite lookup_delete_ne // in Hx.
      assert (c ≠ k) by (intros ->; by apply (Hnochild x)).
      rewrite !obl_owner_of_insert_ne // !obl_fuel_of_insert_ne //. by apply WF.
    - intros x j Hx Hj. rewrite dom_delete_L elem_of_difference elem_of_singleton in Hx.
      destruct Hx as [Hx Hne]. rewrite obl_owner_of_insert_ne // in Hj.
      by apply (fwf_owner _ _ _ _ WF x).
  Qed.

  (** ** Subtrees *)
  (** [p] is an obligation of [X]. *)
  Definition par_in (X : gset oid) (p : parent) : Prop :=
    match p with PObl c => c ∈ X | PThread _ => False end.
  Global Instance par_in_dec X p : Decision (par_in X p).
  Proof. destruct p; simpl; apply _. Defined.

  (** The obligations whose parent is in [X]. *)
  Definition kids_of Par (X : gset oid) : gset oid :=
    dom (filter (λ xp : oid * parent, par_in X xp.2) Par).

  Definition kids_step Par (Y : gset oid) : gset oid := Y ∪ kids_of Par Y.

  (** [k] and all its descendants. *)
  Definition subtree Par (k : oid) : gset oid :=
    Nat.iter (S (size Par)) (kids_step Par) {[k]}.

  Lemma elem_of_kids_of Par X x :
    x ∈ kids_of Par X ↔ ∃ c, Par !! x = Some (PObl c) ∧ c ∈ X.
  Proof.
    rewrite /kids_of elem_of_dom. split.
    - intros [p Hp]. apply map_lookup_filter_Some in Hp as [Hp Hc].
      destruct p as [|c]; simpl in Hc; [done|]. eauto.
    - intros (c& Hc& HX). exists (PObl c). apply map_lookup_filter_Some. done.
  Qed.

  Lemma kids_of_dom Par X : kids_of Par X ⊆ dom Par.
  Proof. intros x (c& Hc& _)%elem_of_kids_of. by eapply elem_of_dom_2. Qed.

  Lemma iter_kids_step_sub Par n k :
    Nat.iter n (kids_step Par) {[k]} ⊆ {[k]} ∪ dom Par.
  Proof.
    induction n as [|n IH]; simpl; first set_solver.
    rewrite /kids_step. pose proof (kids_of_dom Par (Nat.iter n (kids_step Par) {[k]})).
    set_solver.
  Qed.

  Lemma iter_kids_step_incl Par n k :
    Nat.iter n (kids_step Par) {[k]} ⊆ Nat.iter (S n) (kids_step Par) {[k]}.
  Proof. simpl. rewrite /kids_step. set_solver. Qed.

  (** The iteration stabilises within [size Par] steps. *)
  Lemma iter_kids_step_size Par n k :
    (∃ m, m < n ∧ Nat.iter (S m) (kids_step Par) {[k]} = Nat.iter m (kids_step Par) {[k]}) ∨
    n < size (Nat.iter n (kids_step Par) {[k]}).
  Proof.
    induction n as [|n [(m& Hm& Hfix)|IH]].
    - right. change (Nat.iter 0 (kids_step Par) {[k]}) with ({[k]} : gset oid).
      rewrite size_singleton. lia.
    - left. exists m. split; [lia|done].
    - destruct (decide (Nat.iter (S n) (kids_step Par) {[k]} = Nat.iter n (kids_step Par) {[k]}))
        as [Heq|Hne].
      + left. exists n. split; [lia|done].
      + right. assert (Nat.iter n (kids_step Par) {[k]} ⊂ Nat.iter (S n) (kids_step Par) {[k]}) as Hs.
        { split; first apply iter_kids_step_incl. intros Hsub. apply Hne.
          apply (anti_symm (⊆)); [done|apply iter_kids_step_incl]. }
        apply subset_size in Hs. lia.
  Qed.

  Lemma iter_kids_step_fix_stable Par m n k :
    m ≤ n →
    Nat.iter (S m) (kids_step Par) {[k]} = Nat.iter m (kids_step Par) {[k]} →
    Nat.iter (S n) (kids_step Par) {[k]} = Nat.iter n (kids_step Par) {[k]}.
  Proof.
    intros Hle Hfix. induction Hle as [|n Hle IH]; first done.
    rewrite (Nat.iter_succ (S n)) IH. done.
  Qed.

  Lemma subtree_fix Par k : kids_step Par (subtree Par k) = subtree Par k.
  Proof.
    rewrite /subtree. change (kids_step Par (Nat.iter (S (size Par)) (kids_step Par) {[k]}))
      with (Nat.iter (S (S (size Par))) (kids_step Par) {[k]}).
    destruct (iter_kids_step_size Par (S (size Par)) k) as [(m& Hm& Hfix)|Hsize].
    - eapply iter_kids_step_fix_stable; last done. lia.
    - exfalso. pose proof (iter_kids_step_sub Par (S (size Par)) k) as Hsub.
      apply subseteq_size in Hsub. pose proof (size_union_le {[k]} (dom Par)) as Hu.
      rewrite size_singleton size_dom in Hu. lia.
  Qed.

  Lemma subtree_root Par k : k ∈ subtree Par k.
  Proof.
    rewrite /subtree. generalize (S (size Par)) as n. induction n as [|n IH]; simpl; first set_solver.
    rewrite /kids_step. set_solver.
  Qed.

  Lemma subtree_closed Par k x c :
    Par !! x = Some (PObl c) → c ∈ subtree Par k → x ∈ subtree Par k.
  Proof.
    intros Hx Hc. rewrite -subtree_fix /kids_step elem_of_union elem_of_kids_of. eauto.
  Qed.

  Lemma subtree_inv Par k x :
    x ∈ subtree Par k → x = k ∨ ∃ c, Par !! x = Some (PObl c) ∧ c ∈ subtree Par k.
  Proof.
    rewrite /subtree. intros Hx.
    assert (∀ n, x ∈ Nat.iter n (kids_step Par) {[k]} →
                 x = k ∨ ∃ c, Par !! x = Some (PObl c) ∧ c ∈ Nat.iter n (kids_step Par) {[k]})
      as Hgen.
    { intros n. induction n as [|n IH]; simpl.
      - intros ->%elem_of_singleton. by left.
      - rewrite /kids_step elem_of_union elem_of_kids_of. intros [Hx'|(c& Hc& Hin)].
        + destruct (IH Hx') as [->|(c& Hc& Hin)]; [by left|right]. exists c. split; first done.
          set_solver.
        + right. exists c. split; first done. set_solver. }
    destruct (Hgen _ Hx) as [->|(c& Hc& Hin)]; [by left|right]. eauto.
  Qed.

  (** All nodes of the subtree of a node [k] are nodes with the owner of [k]. *)
  Lemma subtree_owner Ω Θ Par Kids k x :
    forest_wf Ω Θ Par Kids → k ∈ dom Par → x ∈ subtree Par k →
    x ∈ dom Par ∧ obl_owner_of Ω x = obl_owner_of Ω k.
  Proof.
    intros WF Hk. rewrite /subtree. generalize (S (size Par)) as n. intros n. revert x.
    induction n as [|n IH]; intros x; simpl.
    - intros ->%elem_of_singleton. done.
    - rewrite /kids_step elem_of_union elem_of_kids_of. intros [Hx|(c& Hc& Hin)]; first by apply IH.
      destruct (IH c Hin) as [_ Hoc]. split; first by eapply elem_of_dom_2.
      destruct (fwf_obl _ _ _ _ WF _ _ Hc) as [Hcx _]. by rewrite -Hcx.
  Qed.

  (** ** Moving a node [k] from parent [p1] to parent [p2] *)
  Lemma forest_wf_reparent Ω Ω' Θ Par Kids p1 p2 K1 K2 k :
    forest_wf Ω Θ Par Kids →
    Par !! k = Some p1 → Kids !! p1 = Some K1 → Kids !! p2 = Some K2 → p1 ≠ p2 →
    (∀ x, (∃ a t, Ω !! x = Some (obl_assigned a t)) ↔ (∃ a t, Ω' !! x = Some (obl_assigned a t))) →
    (∀ x i, <[k:=p2]> Par !! x = Some (PThread i) → obl_owner_of Ω' x = Some i) →
    (∀ x c, <[k:=p2]> Par !! x = Some (PObl c) →
            obl_owner_of Ω' c = obl_owner_of Ω' x ∧ (obl_fuel_of Ω' c < obl_fuel_of Ω' x)%ord) →
    (∀ x i, x ∈ dom Par → obl_owner_of Ω' x = Some i → i ∈ Θ) →
    forest_wf Ω' Θ (<[k:=p2]> Par) (<[p2:={[k]} ∪ K2]> (<[p1:=K1 ∖ {[k]}]> Kids)).
  Proof.
    intros WF Hk HK1 HK2 Hne Hlive Hthr Hobl Hown.
    assert (Hdom : dom (<[k:=p2]> Par) = dom Par).
    { rewrite dom_insert_L. apply elem_of_dom_2 in Hk. set_solver. }
    assert (HkK1 : k ∈ K1).
    { destruct (proj1 (fwf_par_kids _ _ _ _ WF k p1) Hk) as (K'& HK'& Hin).
      rewrite HK1 in HK'. by injection HK' as <-. }
    split.
    - intros p. rewrite Hdom -(fwf_kids_dom _ _ _ _ WF p).
      destruct (decide (p = p2)) as [->|H2].
      { rewrite lookup_insert_eq HK2. split; eauto. }
      rewrite lookup_insert_ne //. destruct (decide (p = p1)) as [->|H1].
      { rewrite lookup_insert_eq HK1. split; eauto. }
      by rewrite lookup_insert_ne.
    - intros x p. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. split.
        * intros [= <-]. rewrite lookup_insert_eq. eexists; split; first done. set_solver.
        * intros (K'& HK'& Hin). destruct (decide (p = p2)) as [->|H2]; first done.
          rewrite lookup_insert_ne // in HK'. destruct (decide (p = p1)) as [->|H1].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. set_solver. }
          rewrite lookup_insert_ne // in HK'.
          assert (Par !! k = Some p) as Hk' by (apply (fwf_par_kids _ _ _ _ WF); eauto).
          rewrite Hk in Hk'. by injection Hk' as ->.
      + rewrite lookup_insert_ne // (fwf_par_kids _ _ _ _ WF x p). split.
        * intros (K'& HK'& Hin). destruct (decide (p = p2)) as [->|H2].
          { rewrite lookup_insert_eq. rewrite HK2 in HK'. injection HK' as <-.
            eexists; split; first done. set_solver. }
          rewrite lookup_insert_ne //. destruct (decide (p = p1)) as [->|H1].
          { rewrite lookup_insert_eq. rewrite HK1 in HK'. injection HK' as <-.
            eexists; split; first done. set_solver. }
          rewrite lookup_insert_ne //. eauto.
        * intros (K'& HK'& Hin). destruct (decide (p = p2)) as [->|H2].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. exists K2.
            split; first done. set_solver. }
          rewrite lookup_insert_ne // in HK'. destruct (decide (p = p1)) as [->|H1].
          { rewrite lookup_insert_eq in HK'. injection HK' as <-. exists K1.
            split; first done. set_solver. }
          rewrite lookup_insert_ne // in HK'. eauto.
    - intros x. rewrite Hdom -Hlive. apply WF.
    - done.
    - done.
    - intros x i. rewrite Hdom. apply Hown.
  Qed.

  (** Without owner change, [k] can move below any parent with its owner and less fuel. *)
  Lemma forest_wf_move_same Ω Θ Par Kids p1 p2 K1 K2 k :
    forest_wf Ω Θ Par Kids →
    Par !! k = Some p1 → Kids !! p1 = Some K1 → Kids !! p2 = Some K2 → p1 ≠ p2 →
    (match p2 with
     | PThread j => obl_owner_of Ω k = Some j
     | PObl q => obl_owner_of Ω q = obl_owner_of Ω k ∧ (obl_fuel_of Ω q < obl_fuel_of Ω k)%ord
     end) →
    forest_wf Ω Θ (<[k:=p2]> Par) (<[p2:={[k]} ∪ K2]> (<[p1:=K1 ∖ {[k]}]> Kids)).
  Proof.
    intros WF Hk HK1 HK2 Hne Hp2. eapply forest_wf_reparent; [done..| | | |].
    - done.
    - intros x i. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= Heq]. by subst p2.
      + rewrite lookup_insert_ne //. apply WF.
    - intros x c. destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= Heq]. by subst p2.
      + rewrite lookup_insert_ne //. apply WF.
    - apply WF.
  Qed.

  (** [Ω'] is [Ω] where all obligations of [S], owned by [t], have a new owner [j] and less
      fuel. *)
  Definition chown_rel (S : gset oid) (t j : positive) (Ω Ω' : obls) : Prop :=
    (∀ x, x ∉ S → Ω' !! x = Ω !! x) ∧
    (∀ x, x ∈ S → ∃ a a', Ω !! x = Some (obl_assigned a t) ∧
                          Ω' !! x = Some (obl_assigned a' j) ∧ (a' < a)%ord).

  Lemma chown_rel_empty t j Ω : chown_rel ∅ t j Ω Ω.
  Proof. split; [done|set_solver]. Qed.

  Lemma chown_rel_insert S t j Ω Ω' x a a' :
    x ∉ S → chown_rel S t j Ω Ω' →
    Ω' !! x = Some (obl_assigned a t) → (a' < a)%ord →
    chown_rel ({[x]} ∪ S) t j Ω (<[x:=obl_assigned a' j]> Ω').
  Proof.
    intros Hx [H1 H2] Hxa Hlt. split.
    - intros y Hy. rewrite lookup_insert_ne; last set_solver. apply H1. set_solver.
    - intros y. rewrite elem_of_union elem_of_singleton. intros [->|Hy].
      + exists a, a'. rewrite lookup_insert_eq -(H1 x) //.
      + destruct (H2 y Hy) as (b& b'& Hb& Hb'& Hlt'). exists b, b'.
        rewrite lookup_insert_ne; last set_solver. done.
  Qed.

  Lemma chown_rel_ndf S t j Ω Ω' : chown_rel S t j Ω Ω' → obls_ndf Ω Ω'.
  Proof.
    intros [H1 H2] x g Hx. destruct (decide (x ∈ S)) as [Hin|Hnin].
    - destruct (H2 x Hin) as (a& a'& Ha& Ha'& Hlt). rewrite Ha in Hx. injection Hx as <-.
      exists (obl_assigned a' j). split; first done. right. by constructor.
    - exists g. rewrite H1 //. split; [done|by left].
  Qed.

  Lemma chown_rel_live S t j Ω Ω' x :
    chown_rel S t j Ω Ω' →
    (∃ a t, Ω !! x = Some (obl_assigned a t)) ↔ (∃ a t, Ω' !! x = Some (obl_assigned a t)).
  Proof.
    intros [H1 H2]. destruct (decide (x ∈ S)) as [Hin|Hnin].
    - destruct (H2 x Hin) as (a& a'& Ha& Ha'& _). rewrite Ha Ha'. naive_solver.
    - by rewrite H1.
  Qed.

  Lemma chown_rel_owner S t j Ω Ω' x :
    chown_rel S t j Ω Ω' →
    obl_owner_of Ω' x = if decide (x ∈ S) then Some j else obl_owner_of Ω x.
  Proof.
    intros [H1 H2]. destruct (decide (x ∈ S)) as [Hin|Hnin].
    - destruct (H2 x Hin) as (a& a'& Ha& Ha'& _). by rewrite /obl_owner_of Ha'.
    - by rewrite /obl_owner_of H1.
  Qed.

  Lemma chown_rel_fuel_out S t j Ω Ω' x :
    chown_rel S t j Ω Ω' → x ∉ S → obl_fuel_of Ω' x = obl_fuel_of Ω x.
  Proof. intros [H1 _] Hx. by rewrite /obl_fuel_of H1. Qed.

  Lemma chown_rel_fuel_in S t j Ω Ω' x :
    chown_rel S t j Ω Ω' → x ∈ S →
    obl_owner_of Ω x = Some t ∧ (obl_fuel_of Ω' x < obl_fuel_of Ω x)%ord.
  Proof.
    intros [_ H2] Hx. destruct (H2 x Hx) as (a& a'& Ha& Ha'& Hlt).
    by rewrite /obl_owner_of /obl_fuel_of Ha Ha'.
  Qed.

  Lemma forest_owned_chown Ω Ω' D S t j i :
    chown_rel S t j Ω Ω' → S ⊆ D →
    forest_owned Ω' D i =
      (if decide (i = j) then S ∪ forest_owned Ω D i
       else if decide (i = t) then forest_owned Ω D i ∖ S
       else forest_owned Ω D i).
  Proof.
    intros Hrel HSD. apply set_eq. intros x. rewrite /forest_owned.
    destruct (decide (x ∈ S)) as [Hin|Hnin].
    - destruct (chown_rel_fuel_in _ _ _ _ _ _ Hrel Hin) as [Hot _].
      pose proof (chown_rel_owner _ _ _ _ _ x Hrel) as Ho. rewrite decide_True // in Ho.
      rewrite elem_of_filter Ho.
      destruct (decide (i = j)) as [->|Hij]; first set_solver.
      destruct (decide (i = t)) as [->|Hit]; first set_solver.
      rewrite elem_of_filter Hot. split; [intros [[= ->] _]; done|intros [[= ->] _]; done].
    - pose proof (chown_rel_owner _ _ _ _ _ x Hrel) as Ho. rewrite decide_False // in Ho.
      rewrite elem_of_filter Ho.
      destruct (decide (i = j)) as [->|Hij]; first (rewrite elem_of_union elem_of_filter; set_solver).
      destruct (decide (i = t)) as [->|Hit]; first (rewrite elem_of_difference elem_of_filter; set_solver).
      by rewrite elem_of_filter.
  Qed.

  (** With owner change, the whole subtree [S] of [k] gets the new owner. *)
  Lemma forest_wf_move_cross Ω Ω' Θ Par Kids p1 p2 K1 K2 k t j :
    forest_wf Ω Θ Par Kids →
    Par !! k = Some p1 → Kids !! p1 = Some K1 → Kids !! p2 = Some K2 → p1 ≠ p2 →
    obl_owner_of Ω k = Some t → t ≠ j →
    (match p2 with PThread j' => j' = j | PObl q => obl_owner_of Ω q = Some j end) →
    chown_rel (subtree Par k) t j Ω Ω' →
    (∀ q, p2 = PObl q → (obl_fuel_of Ω q < obl_fuel_of Ω' k)%ord) →
    (∀ x c, x ∈ subtree Par k → x ≠ k → Par !! x = Some (PObl c) →
            (obl_fuel_of Ω c <= obl_fuel_of Ω' x)%ord) →
    forest_wf Ω' Θ (<[k:=p2]> Par) (<[p2:={[k]} ∪ K2]> (<[p1:=K1 ∖ {[k]}]> Kids)).
  Proof.
    intros WF Hk HK1 HK2 Hne Ht Htj Hp2 Hrel Hpk Hpx.
    set (S := subtree Par k) in *.
    assert (HkD : k ∈ dom Par) by (by eapply elem_of_dom_2).
    assert (HSown : ∀ x, x ∈ S → x ∈ dom Par ∧ obl_owner_of Ω x = Some t).
    { intros x Hx. rewrite -Ht. by eapply subtree_owner. }
    assert (Hj : j ∈ Θ).
    { destruct p2 as [j'|q].
      - subst j'. apply (fwf_kids_dom _ _ _ _ WF (PThread j)). eauto.
      - eapply (fwf_owner _ _ _ _ WF q); last done.
        apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    assert (Hq : ∀ q, p2 = PObl q → q ∉ S).
    { intros q -> HqS. destruct (HSown q HqS) as [_ Hoq]. rewrite Hoq in Hp2.
      injection Hp2 as ->. done. }
    eapply forest_wf_reparent; [done..| | | |].
    - intros x. by eapply chown_rel_live.
    - intros x i. rewrite !(chown_rel_owner _ _ _ _ _ x Hrel). destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= Heq]. subst p2. rewrite decide_True; [by subst|].
        apply subtree_root.
      + rewrite lookup_insert_ne //. intros Hxi. rewrite decide_False; first by apply WF.
        intros HxS. destruct (subtree_inv _ _ _ HxS) as [?|(c& Hc& _)]; first done.
        by rewrite Hxi in Hc.
    - intros x c. rewrite !(chown_rel_owner _ _ _ _ _ _ Hrel). destruct (decide (x = k)) as [->|Hx].
      + rewrite lookup_insert_eq. intros [= Heq]. subst p2.
        rewrite decide_False; last by apply Hq. rewrite decide_True; last apply subtree_root.
        split; first done. rewrite (chown_rel_fuel_out _ _ _ _ _ _ Hrel); last by apply Hq.
        by apply Hpk.
      + rewrite lookup_insert_ne //. intros Hxc. destruct (decide (x ∈ S)) as [HxS|HxS].
        * destruct (subtree_inv _ _ _ HxS) as [?|(c'& Hc'& HcS)]; first done.
          rewrite Hxc in Hc'. injection Hc' as <-. rewrite decide_True //. split; first done.
          eapply Ord.lt_le_lt; last by apply Hpx.
          by apply (chown_rel_fuel_in _ _ _ _ _ _ Hrel).
        * assert (HcS : c ∉ S) by (intros HcS; by apply HxS, (subtree_closed _ _ _ c)).
          rewrite decide_False //.
          rewrite !(chown_rel_fuel_out _ _ _ _ _ _ Hrel) //. by apply WF.
    - intros x i Hx. rewrite (chown_rel_owner _ _ _ _ _ x Hrel). destruct (decide (x ∈ S)).
      + by intros [= <-].
      + by apply WF.
  Qed.

End forest_pure.

(** * Rules of the invariant *)
Section oforest.
  Context `{SI : sidx} `{OSAT : !osatGS.osatGS Σ} `{OTH : !othreadGS.othreadGS Σ}
    `{!oforestGS Σ} `{OMF : !ord_mono_fun_class}.

  Global Instance oforestG_kids_timeless p K : Timeless (oforestG_kids p K).
  Proof. rewrite /oforestG_kids. apply _. Qed.

  Lemma oforestG_kids_excl p K1 K2 : oforestG_kids p K1 -∗ oforestG_kids p K2 -∗ False.
  Proof.
    rewrite /oforestG_kids. iIntros "H1 H2". iCombine "H1 H2" gives %[Hv _].
    rewrite dfrac_op_own dfrac_valid_own in Hv. by apply Qp.not_add_le_l in Hv.
  Qed.

  Lemma oforestG_kids_lookup Kids p K :
    oforestG_kids_auth Kids -∗ oforestG_kids p K -∗ ⌜ Kids !! p = Some K ⌝.
  Proof.
    rewrite /oforestG_kids /oforestG_kids_auth. iIntros "A F".
    iApply (ghost_map_lookup with "A F").
  Qed.

  (** ** Threads: allocation and termination *)
  Lemma oforest_alloc_thread Ω Θ i :
    i ∉ Θ →
    oforest Ω Θ ∗ othreadG_elem i ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅
    ⊢ |==> oforest Ω ({[i]} ∪ Θ) ∗ oforestG_kids (PThread i) ∅.
  Proof.
    iIntros (Hi) "(F& #Ei& Tx& TG)".
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    assert (HK : Kids !! PThread i = None).
    { destruct (Kids !! PThread i) eqn:E; last done. exfalso. apply Hi.
      apply (fwf_kids_dom _ _ _ _ WF (PThread i)). eauto. }
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_insert (PThread i) ∅ with "A") as "[A $]"; first done.
    iModIntro. iExists Par, _. iFrame "A Ns". iSplit.
    { iPureIntro. by apply forest_wf_alloc_thread. }
    iApply big_sepS_union; first set_solver. iFrame "Ts". iApply big_sepS_singleton.
    iFrame "Ei". iLeft. iFrame. by rewrite (forest_owned_not_in_pool _ _ _ _ _ WF Hi).
  Qed.

  Lemma oforest_alloc_threads Ω π Θ :
    π ## Θ →
    oforest Ω Θ ∗ ([∗ set] i ∈ π, othreadG_elem i ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅)
    ⊢ |==> oforest Ω (Θ ∪ π) ∗ ([∗ set] i ∈ π, oforestG_kids (PThread i) ∅).
  Proof.
    revert Θ. induction π as [|i π Hi IH] using set_ind_L; iIntros (Θ Disj) "[F M]".
    { rewrite union_empty_r_L !big_sepS_empty. by iFrame. }
    rewrite !big_sepS_union; [|set_solver..]. rewrite !big_sepS_singleton.
    iDestruct "M" as "(Mi& M)".
    iMod (IH with "[$F $M]") as "(F& $)"; first set_solver.
    iMod (oforest_alloc_thread _ _ i with "[$F $Mi]") as "(F& $)"; first set_solver.
    iModIntro. by replace ({[i]} ∪ (Θ ∪ π)) with (Θ ∪ ({[i]} ∪ π)) by set_solver.
  Qed.

  Lemma oforest_exec_to_done Ω Θ i :
    i ∈ Θ →
    othread Θ ∗ oforest Ω Θ ∗ othreadG_exec i (1/2)%Qp ∗ oforestG_kids (PThread i) ∅
    ⊢ |==> othread Θ ∗ oforest Ω Θ ∗ othreadG_done i.
  Proof.
    iIntros (Hi) "(T& F& Tx& Ki)".
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A Ki") as "%HK".
    iPoseProof (big_sepS_delete _ _ _ Hi with "Ts") as "[(#Ei& [(Tx2& TG) | (_& Ki2& _)]) Ts]"; cycle 1.
    { iExFalso. iApply (oforestG_kids_excl with "Ki Ki2"). }
    pose proof (forest_wf_owned_empty _ _ _ _ _ WF HK) as Hown. rewrite Hown.
    iCombine "Tx Tx2" as "Tx".
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[$ #Td]".
    iModIntro. iFrame "Td". iExists Par, Kids. iFrame "A Ns". iSplit; first done.
    iApply (big_sepS_delete _ _ _ Hi). iFrame "Ts Ei". iRight. by iFrame "Td Ki".
  Qed.

  (** ** Obligations: allocation, steps of a thread and discharge *)
  (** A new obligation [k] (already allocated in the model) becomes a leaf below [p]. *)
  Lemma oforest_alloc_obl Ω Θ p K k a i β :
    Ω !! k = None →
    (match p with
     | PThread j => j = i
     | PObl q => obl_owner_of Ω q = Some i ∧ (obl_fuel_of Ω q < a)%ord
     end) →
    (a <= β)%ord →
    osat (<[k:=obl_assigned a i]> Ω) ∗ othread Θ ∗ oforest Ω Θ ∗ oforestG_kids p K ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_bound k β ∗
    (match p with
     | PObl q => ∃ π, ⌜ (obl_fuel_of Ω q < π)%ord ⌝ ∗ oblG_fuel k π
     | PThread _ => True
     end)
    ⊢ |==> osat (<[k:=obl_assigned a i]> Ω) ∗ othread Θ ∗ oforest (<[k:=obl_assigned a i]> Ω) Θ ∗
        ⌜ k ∉ K ⌝ ∗ oforestG_kids p ({[k]} ∪ K) ∗ oforestG_kids (PObl k) ∅ ∗
        othreadG_elem i ∗ othreadG_owns i k (1/2/2)%Qp ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Hk Hp Hab) "(S& T& F& Kp& #Ek& Ok& #Bk& Pk)".
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A Kp") as "%HK".
    assert (HkPar : Par !! k = None).
    { apply not_elem_of_dom. intros Hd. apply (fwf_par_live _ _ _ _ WF) in Hd as (?&?&Hx).
      by rewrite Hk in Hx. }
    assert (HkKids : Kids !! PObl k = None).
    { destruct (Kids !! PObl k) eqn:E; last done. exfalso. apply not_elem_of_dom in HkPar.
      apply HkPar. apply (fwf_kids_dom _ _ _ _ WF (PObl k)). eauto. }
    assert (Hdomk : ∀ c, c ∈ dom Par → c ≠ k).
    { intros c Hc ->. apply not_elem_of_dom in HkPar. done. }
    assert (Hi : i ∈ Θ).
    { destruct p as [j|q].
      - subst j. apply (fwf_kids_dom _ _ _ _ WF (PThread i)). eauto.
      - destruct Hp as [Hq _]. eapply (fwf_owner _ _ _ _ WF q); last done.
        apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    iPoseProof (big_sepS_delete _ _ _ Hi with "Ts") as "[(#Ei& Hi) Ts]".
    iDestruct "Hi" as "[(Tx& TG) | (_& Kd& %Hown)]"; cycle 1.
    { iExFalso. destruct p as [j|q].
      - subst j. iApply (oforestG_kids_excl with "Kp Kd").
      - destruct Hp as [Hq _]. iPureIntro.
        assert (q ∈ forest_owned Ω (dom Par) i); last set_solver.
        apply elem_of_filter. split; first done. apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    iMod (othread_alloc_obl with "[$S $T $TG $Ek $Ok]") as "(S& T& %NinkG& TG& Oo& Ok)".
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_update ({[k]} ∪ K) with "A Kp") as "[A Kp]".
    iMod (ghost_map_insert (PObl k) ∅ with "A") as "[A Kk]".
    { rewrite lookup_insert_ne; first done. intros ->. by rewrite HkKids in HK. }
    iDestruct "Ok" as "[Ok Ok']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
    iModIntro. iFrame "S T Kp Kk Ei Oo' Ok'".
    iSplitL; last first.
    { iPureIntro. intros HkK. apply not_elem_of_dom in HkPar. apply HkPar.
      eapply elem_of_dom_2. apply (fwf_par_kids _ _ _ _ WF k p). eauto. }
    iExists (<[k:=p]> Par), _. iFrame "A". iSplit.
    { iPureIntro. by eapply forest_wf_alloc_obl. }
    rewrite dom_insert_L. iSplitL "Ts Tx TG".
    { iApply (big_sepS_delete _ _ _ Hi). iSplitL "Tx TG".
      - iFrame "Ei". iLeft. iFrame "Tx".
        rewrite forest_owned_insert_same; last by apply not_elem_of_dom. done.
      - iApply (big_sepS_impl with "Ts"). iIntros "!> %j %Hj (#Ej& H)". iFrame "Ej".
        rewrite forest_owned_insert_other; [done|by apply not_elem_of_dom|set_solver]. }
    iApply big_sepM_insert; first done. iSplitL "Oo Oo1 Ok Pk".
    { rewrite /forest_node. iFrame "Ek". iSplitL "Oo Oo1 Ok".
      { iExists i. rewrite obl_owner_of_insert_eq. iSplit; first done. iFrame "Ok".
        iCombine "Oo Oo1" as "$". }
      iSplitR.
      { iExists β. iFrame "Bk". by rewrite obl_fuel_of_insert_eq. }
      destruct p as [j|q]; first done. iDestruct "Pk" as "(%π& %Hπ& Pk)". iExists π.
      iFrame "Pk". iPureIntro. rewrite obl_fuel_of_insert_ne //. apply Hdomk.
      apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    iApply (big_sepM_impl with "Ns"). iIntros "!> %x %p' %Hx (#Ex& Own& Bnd& Pp)".
    assert (x ≠ k) as Hxk by (apply Hdomk; by eapply elem_of_dom_2).
    rewrite /forest_node obl_owner_of_insert_ne // obl_fuel_of_insert_ne //. iFrame "Ex Own Bnd".
    destruct p' as [j|c]; first done.
    assert (c ≠ k).
    { apply Hdomk. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& _).
      apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
    by rewrite obl_fuel_of_insert_ne.
  Qed.

  (** A fuel piece of a live obligation is below its model fuel. *)
  Lemma osat_fuel_le Ω x a :
    osat Ω -∗ oblG_fuel x a -∗ ⌜ ∀ f t, Ω !! x = Some (obl_assigned f t) → (a <= f)%ord ⌝.
  Proof.
    iIntros "S F" (f t Hx). rewrite /osat -!lock. iDestruct "S" as "(_& _& _& _& HM)".
    iPoseProof (big_sepM_lookup with "HM") as "(%β& _& %α& Gs& %Hαβ& Mk)"; first done.
    iDestruct "Mk" as "(%& _& %Hαf& _)".
    rewrite /oblG_fuel_supply /oblG_fuel. iCombine "Gs F" gives %Hv.
    rewrite -reservation_map_data_op reservation_map_data_valid in Hv.
    apply bank_valid_debt_cash in Hv as [Hle _]. iPureIntro.
    etrans; first exact Hle. done.
  Qed.

  (** Children and obligation parents are live. *)
  Lemma oforest_kids_live Ω Θ p K :
    oforest Ω Θ -∗ oforestG_kids p K -∗
    ⌜ (∀ x, x ∈ K → ∃ a t, Ω !! x = Some (obl_assigned a t)) ∧
      (∀ q, p = PObl q → ∃ a t, Ω !! q = Some (obl_assigned a t)) ⌝.
  Proof.
    rewrite /oforest -!lock. iIntros "(%Par& %Kids& A& %WF& _& _) Kp".
    iPoseProof (oforestG_kids_lookup with "A Kp") as "%HK". iPureIntro. split.
    - intros x Hx. apply (fwf_par_live _ _ _ _ WF). apply (elem_of_dom_2 _ _ p).
      apply (fwf_par_kids _ _ _ _ WF). eauto.
    - intros q ->. apply (fwf_par_live _ _ _ _ WF). apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto.
  Qed.

  (** The fuel of an obligation parent is below any fuel bound of it. *)
  Lemma oforest_obl_fuel_bound Ω Θ q K β :
    oforest Ω Θ -∗ oforestG_kids (PObl q) K -∗ oblG_bound q β -∗
    ⌜ (obl_fuel_of Ω q <= β)%ord ∧ ∃ a t, Ω !! q = Some (obl_assigned a t) ⌝.
  Proof.
    rewrite /oforest -!lock. iIntros "(%Par& %Kids& A& %WF& _& Ns) Kp #B".
    iPoseProof (oforestG_kids_lookup with "A Kp") as "%HK".
    assert (Hq : q ∈ dom Par) by (apply (fwf_kids_dom _ _ _ _ WF (PObl q)); eauto).
    apply elem_of_dom in Hq as [pq Hq].
    iPoseProof (big_sepM_lookup with "Ns") as "(_& _& (%β'& #B'& %Hle)& _)"; first done.
    iPoseProof (oblG_bound_agree q β β' with "[$B $B']") as "%Heq". iPureIntro. split.
    - etrans; first done. apply Heq.
    - apply (fwf_par_live _ _ _ _ WF). by eapply elem_of_dom_2.
  Qed.

  (** A discharged obligation outside the forest. *)
  Lemma oforest_alloc_discharged Ω Θ k :
    Ω !! k = None → oforest Ω Θ ⊢ oforest (<[k:=obl_discharged]> Ω) Θ.
  Proof.
    iIntros (Hk). rewrite /oforest -!lock. iIntros "(%Par& %Kids& A& %WF& Ts& Ns)".
    assert (HkPar : k ∉ dom Par).
    { intros Hd. apply (fwf_par_live _ _ _ _ WF) in Hd as (?&?&Hx). by rewrite Hk in Hx. }
    assert (Hdomk : ∀ c, c ∈ dom Par → c ≠ k) by (intros c Hc ->; done).
    assert (Hown : ∀ j, forest_owned (<[k:=obl_discharged]> Ω) (dom Par) j = forest_owned Ω (dom Par) j).
    { intros j. apply set_eq. intros x. rewrite /forest_owned !elem_of_filter.
      split; intros [H1 H2]; split; try done;
        (rewrite obl_owner_of_insert_ne in H1 |- *; [done|by apply Hdomk..]). }
    iExists Par, Kids. iFrame "A". iSplit.
    { iPureIntro. split.
      - apply WF.
      - apply WF.
      - intros x. rewrite (fwf_par_live _ _ _ _ WF x). destruct (decide (x = k)) as [->|Hx].
        + rewrite lookup_insert_eq Hk. split; intros (?&?&?); done.
        + by rewrite lookup_insert_ne.
      - intros x i Hx. rewrite obl_owner_of_insert_ne; first by apply WF.
        apply Hdomk. by eapply elem_of_dom_2.
      - intros x c Hx. assert (x ≠ k) by (apply Hdomk; by eapply elem_of_dom_2).
        assert (c ≠ k).
        { apply Hdomk. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& _).
          apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
        rewrite !obl_owner_of_insert_ne // !obl_fuel_of_insert_ne //. by apply WF.
      - intros x i Hx. rewrite obl_owner_of_insert_ne; last by apply Hdomk.
        by apply (fwf_owner _ _ _ _ WF). }
    iSplitL "Ts".
    { iApply (big_sepS_impl with "Ts"). iIntros "!> %j %Hj H". by rewrite Hown. }
    iApply (big_sepM_impl with "Ns"). iIntros "!> %x %p' %Hx (#Ex& Own& Bnd& Pp)".
    assert (x ≠ k) as Hxk by (apply Hdomk; by eapply elem_of_dom_2).
    rewrite /forest_node obl_owner_of_insert_ne // obl_fuel_of_insert_ne //. iFrame "Ex Own Bnd".
    destruct p' as [j|c]; first done.
    assert (c ≠ k).
    { apply Hdomk. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& _).
      apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
    by rewrite obl_fuel_of_insert_ne.
  Qed.

  (** A step of thread [i]: the children of [i] spend the units given by the user; every
      other node owned by [i] splits one unit off its stored piece, keeping exactly the fuel
      its parent had. After the step of the model, which lowers the fuel of every obligation
      owned by [i], the invariant holds again. *)
  Lemma oforest_step Ω Θ i K :
    i ∈ Θ →
    oforest Ω Θ ∗ oforestG_kids (PThread i) K ∗
    ([∗ set] k ∈ K, ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel k c)
    ⊢ |==> ∃ G, oforestG_kids (PThread i) K ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i G ∗
            ([∗ set] k ∈ G, oblG_elem k ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel k c) ∗
            (∀ Ω', ⌜ Ω ↪ₚ Ω' | obl_cond_owner i ⌝ -∗ osat Ω' -∗ othreadG_exec i (1/2/2) -∗
                   othreadG_obls i G -∗ osat Ω' ∗ oforest Ω' Θ).
  Proof.
    iIntros (Hi) "(F& Kt& Us)".
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A Kt") as "%HK".
    iPoseProof (big_sepS_delete _ _ _ Hi with "Ts") as "[(#Ei& Hi) Ts]".
    iDestruct "Hi" as "[(Tx& TG) | (_& Kd& _)]"; cycle 1.
    { iExFalso. iApply (oforestG_kids_excl with "Kt Kd"). }
    assert (HKdom : K = dom (filter (λ xp : oid * parent, xp.2 = PThread i) Par)).
    { apply set_eq. intros x. rewrite elem_of_dom. split.
      - intros Hx. exists (PThread i). apply map_lookup_filter_Some. split; last done.
        apply (fwf_par_kids _ _ _ _ WF). eauto.
      - intros [p Hp]. apply map_lookup_filter_Some in Hp as [Hp Hp2]. simpl in Hp2. subst p.
        destruct (proj1 (fwf_par_kids _ _ _ _ WF _ _) Hp) as (K'& HK'& Hin).
        rewrite HK in HK'. by injection HK' as <-. }
    iAssert ([∗ map] x ↦ p ∈ Par, if decide (p = PThread i)
               then (∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel x c) else emp)%I with "[Us]" as "Us".
    { rewrite HKdom -big_sepM_dom. by rewrite big_sepM_filter'. }
    iAssert (|==> ([∗ map] x ↦ p ∈ Par, forest_node_stepped Ω i x p) ∗
               ([∗ map] x ↦ p ∈ Par, if decide (obl_owner_of Ω x = Some i)
                  then (oblG_elem x ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel x c) else emp))%I
      with "[Ns Us]" as ">[Ns Ps]".
    { rewrite -big_sepM_sep -big_sepM_bupd. iCombine "Ns Us" as "NU". rewrite -big_sepM_sep.
      iApply (big_sepM_impl with "NU"). iIntros "!> %x %p %Hx [(#Ex& Own& Bnd& Pp) U]".
      rewrite /forest_node_stepped. iFrame "Ex Own Bnd". destruct p as [j|c].
      - pose proof (fwf_thread _ _ _ _ WF _ _ Hx) as Hj.
        destruct (decide (j = i)) as [->|Hne].
        + rewrite !decide_True //. iModIntro. iSplit; first done. iFrame "Ex U".
        + rewrite decide_False; last (intros [= ->]; done).
          rewrite decide_False; last (rewrite Hj; intros [= ->]; done).
          iModIntro. done.
      - rewrite decide_False; last done. iDestruct "Pp" as "(%π& %Hπ& Fx)".
        destruct (decide (obl_owner_of Ω x = Some i)) as [Ho|Ho].
        + iMod (oblG_fuel_lt _ (obl_fuel_of Ω c) with "Fx") as "(Fc& %c'& %Hc'& Fu)"; first done.
          iModIntro. iSplitL "Fc".
          { iExists _. iFrame "Fc". done. }
          iFrame "Ex". iExists c'. by iFrame.
        + iModIntro. iSplitL; last done. iExists π. iFrame "Fx". done. }
    iAssert ([∗ set] k ∈ forest_owned Ω (dom Par) i,
               oblG_elem k ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel k c)%I with "[Ps]" as "Ps".
    { rewrite /forest_owned filter_dom_L -big_sepM_dom. by rewrite big_sepM_filter'. }
    iModIntro. iExists (forest_owned Ω (dom Par) i). iFrame "Kt Tx TG Ps".
    iIntros (Ω' Hprog) "S' Tx TG".
    (* Owners do not change: they are read off the owner tokens of the nodes. *)
    iAssert (⌜ ∀ x p, Par !! x = Some p → obl_owner_of Ω' x = obl_owner_of Ω x ⌝)%I as %Hown.
    { iIntros (x p Hx).
      iPoseProof (big_sepM_lookup with "Ns") as "(#Ex& (%t& %Ht& Ot& _)& _)"; first done.
      iPoseProof (osat_lookup_owner with "[$S' $Ex $Ot]") as "%Hx'". destruct Hx' as (a'& Ha').
      iPureIntro. by rewrite Ht /obl_owner_of Ha'. }
    assert (Hlive : ∀ x, x ∈ dom Par → ∃ a t, Ω !! x = Some (obl_assigned a t)).
    { intros x Hx. by apply (fwf_par_live _ _ _ _ WF). }
    assert (Hlt : ∀ x, x ∈ dom Par → obl_owner_of Ω x = Some i →
                       (obl_fuel_of Ω' x < obl_fuel_of Ω x)%ord).
    { intros x Hx Ho. destruct (Hlive x Hx) as (a& t& Hxa). rewrite /obl_owner_of Hxa in Ho.
      injection Ho as ->. destruct (prog_owned _ _ _ _ _ Hprog Hxa) as (a'& t'& Hxa'& Hlt).
      by rewrite /obl_fuel_of Hxa Hxa'. }
    assert (Heq : ∀ x, x ∈ dom Par → obl_owner_of Ω x ≠ Some i →
                       obl_fuel_of Ω' x = obl_fuel_of Ω x).
    { intros x Hx Ho. destruct (Hlive x Hx) as (a& t& Hxa). rewrite /obl_owner_of Hxa in Ho.
      rewrite /obl_fuel_of (prog_other _ _ _ _ _ Hprog Hxa) ?Hxa //. simpl. intros ->. done. }
    assert (Hle : ∀ x, x ∈ dom Par → (obl_fuel_of Ω' x <= obl_fuel_of Ω x)%ord).
    { intros x Hx. destruct (decide (obl_owner_of Ω x = Some i)) as [Ho|Ho].
      - apply Ord.lt_le. by apply Hlt.
      - rewrite Heq //. }
    assert (Hpar : ∀ x c, Par !! x = Some (PObl c) → c ∈ dom Par).
    { intros x c Hx. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& _).
      apply (fwf_kids_dom _ _ _ _ WF (PObl c)). eauto. }
    (* The new pieces are below the new fuels. *)
    iAssert (⌜ ∀ x c, Par !! x = Some (PObl c) → obl_owner_of Ω x = Some i →
               (obl_fuel_of Ω c <= obl_fuel_of Ω' x)%ord ⌝)%I as %Hpiece.
    { iIntros (x c Hx Ho).
      iPoseProof (big_sepM_lookup _ _ x (PObl c) with "Ns") as "(_& _& _& (%π& %Hπ& Fx))";
        first done.
      rewrite decide_True in Hπ; last done. subst π.
      iDestruct (osat_fuel_le with "S' Fx") as %Hle'.
      destruct (proj1 (prog_live _ _ _ x Hprog) (Hlive x (elem_of_dom_2 _ _ _ Hx)))
        as (a'& t'& Hxa').
      iPureIntro. rewrite {2}/obl_fuel_of Hxa'. by eapply Hle'. }
    iFrame "S'". rewrite -lock. iExists Par, Kids. iFrame "A". iSplit.
    { iPureIntro. split.
      - apply WF.
      - apply WF.
      - intros x. rewrite (fwf_par_live _ _ _ _ WF x). apply (prog_live _ _ _ x Hprog).
      - intros x j Hx. rewrite (Hown x _ Hx). by apply WF.
      - intros x c Hx. destruct (fwf_obl _ _ _ _ WF _ _ Hx) as [Hoc Hlt0].
        assert (Hc : c ∈ dom Par) by (by eapply Hpar).
        apply elem_of_dom in Hc as [pc Hc].
        rewrite (Hown x _ Hx) (Hown c _ Hc). split; first done.
        destruct (decide (obl_owner_of Ω x = Some i)) as [Ho|Ho].
        + eapply Ord.lt_le_lt; last by apply Hpiece.
          apply Hlt; [by eapply elem_of_dom_2|by rewrite Hoc].
        + rewrite (Heq x); [|by eapply elem_of_dom_2|done].
          rewrite (Heq c); [done|by eapply elem_of_dom_2|by rewrite Hoc].
      - intros x j Hx Hj. apply elem_of_dom in Hx as [px Hx'].
        rewrite (Hown x _ Hx') in Hj. eapply (fwf_owner _ _ _ _ WF); [by eapply elem_of_dom_2|done]. }
    assert (Hown' : ∀ j, forest_owned Ω' (dom Par) j = forest_owned Ω (dom Par) j).
    { intros j. apply forest_owned_ext. intros x Hx. apply elem_of_dom in Hx as [p Hp].
      by eapply Hown. }
    iSplitL "Ts Tx TG".
    { iApply (big_sepS_delete _ _ _ Hi). rewrite Hown'. iSplitL "Tx TG".
      - iFrame "Ei". iLeft. iFrame.
      - iApply (big_sepS_impl with "Ts"). iIntros "!> %j %Hj H". by rewrite Hown'. }
    iApply (big_sepM_impl with "Ns").
    iIntros "!> %x %p %Hx (#Ex& (%t& %Ht& Ot)& (%β& #Bx& %Hb)& Pp)".
    rewrite /forest_node. iFrame "Ex". iSplitL "Ot".
    { iExists t. rewrite (Hown x p Hx). by iFrame. }
    iSplitR.
    { iExists β. iFrame "Bx". iPureIntro. etrans; last done. apply Hle. by eapply elem_of_dom_2. }
    destruct p as [j|c]; first done. iDestruct "Pp" as "(%π& %Hπ& Fx)". iExists π.
    iFrame "Fx". iPureIntro. destruct (fwf_obl _ _ _ _ WF _ _ Hx) as [Hoc _].
    assert (Hc : c ∈ dom Par) by (by eapply Hpar).
    destruct (decide (obl_owner_of Ω x = Some i)) as [Ho|Ho].
    - simpl in Hπ. subst π. apply Hlt; [done|by rewrite Hoc].
    - simpl in Hπ. rewrite Heq //. by rewrite Hoc.
  Qed.

  (** A childless obligation [k] leaves the forest (it is about to be discharged). *)
  Lemma oforest_discharge_obl Ω Θ p K k t :
    k ∈ K → obl_owner_of Ω k = Some t →
    othread Θ ∗ oforest Ω Θ ∗ oforestG_kids p K ∗ oforestG_kids (PObl k) ∅ ∗
    othreadG_owns t k (1/2/2)%Qp
    ⊢ |==> othread Θ ∗ oforest (<[k:=obl_discharged]> Ω) Θ ∗ oforestG_kids p (K ∖ {[k]}) ∗
           oblG_owner k t (1/2 + 1/2/2/2)%Qp ∗ oblG_owner k t (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Hk Ht) "(T& F& Kp& Kk& Oo')".
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A Kp") as "%HK".
    iPoseProof (oforestG_kids_lookup with "A Kk") as "%HKk".
    assert (Hpk : Par !! k = Some p) by (apply (fwf_par_kids _ _ _ _ WF); eauto).
    iPoseProof (big_sepM_delete _ _ _ _ Hpk with "Ns") as "[(#Ek& (%t'& %Ht'& Ok& Oo)& _& _) Ns]".
    rewrite Ht in Ht'. injection Ht' as <-.
    assert (Hti : t ∈ Θ) by (eapply (fwf_owner _ _ _ _ WF); [by eapply elem_of_dom_2|done]).
    iPoseProof (big_sepS_delete _ _ _ Hti with "Ts") as "[(#Et& Hi) Ts]".
    iDestruct "Hi" as "[(Tx& TG) | (_& _& %Hown)]"; cycle 1.
    { iExFalso. iPureIntro. assert (k ∈ forest_owned Ω (dom Par) t); last set_solver.
      apply elem_of_filter. split; first done. by eapply elem_of_dom_2. }
    iDestruct "Oo" as "[Oo Oo1]". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iMod (othread_delete_obl with "[$T $TG $Oo]") as "(T& TG& Go2)".
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_delete with "A Kk") as "A".
    iMod (ghost_map_update (K ∖ {[k]}) with "A Kp") as "[A Kp]".
    iModIntro. iFrame "T Kp Ok Go2".
    iExists (delete k Par), _. iFrame "A". iSplit.
    { iPureIntro. by eapply forest_wf_discharge. }
    rewrite dom_delete_L. iSplitL "Ts Tx TG".
    { iApply (big_sepS_delete _ _ _ Hti). iSplitL "Tx TG".
      - iFrame "Et". iLeft. iFrame "Tx". by rewrite forest_owned_remove.
      - iApply (big_sepS_impl with "Ts"). iIntros "!> %j %Hj (#Ej& H)". iFrame "Ej".
        rewrite forest_owned_remove.
        assert (forest_owned Ω (dom Par) j ∖ {[k]} = forest_owned Ω (dom Par) j) as ->; last done.
        apply set_eq. intros x. rewrite elem_of_difference elem_of_singleton /forest_owned
          elem_of_filter. split; [naive_solver|]. intros [Hx Hd]. split; first done.
        intros ->. rewrite Ht in Hx. injection Hx as <-. set_solver. }
    assert (Hnochild : ∀ x, Par !! x ≠ Some (PObl k)).
    { intros x Hx. destruct (proj1 (fwf_par_kids _ _ _ _ WF x _) Hx) as (K'& HK'& Hin).
      rewrite HKk in HK'. injection HK' as <-. set_solver. }
    iApply (big_sepM_impl with "Ns"). iIntros "!> %x %p' %Hx (#Ex& Own& Bnd& Pp)".
    apply lookup_delete_Some in Hx as [Hxk Hx].
    rewrite /forest_node obl_owner_of_insert_ne // obl_fuel_of_insert_ne //. iFrame "Ex Own Bnd".
    destruct p' as [j|c]; first done.
    assert (c ≠ k) by (intros ->; by apply (Hnochild x)).
    by rewrite obl_fuel_of_insert_ne.
  Qed.

  (** ** Owner change of obligations *)
  (** Obligation [x], owned by [t], gets the new owner [j] and burns [c]. *)
  Lemma osat_chown Ω TP t j Gt Gj x c :
    (Ord.O < c)%ord →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_obls t Gt ∗ othreadG_obls j Gj ∗
    othreadG_elem j ∗ oblG_elem x ∗ oblG_owner x t (1/2 + 1/2/2/2)%Qp ∗
    othreadG_owns t x (1/2 + 1/2/2)%Qp ∗ oblG_fuel x c
    ⊢ |==> ∃ a a', ⌜ Ω !! x = Some (obl_assigned a t) ∧ (a' < a)%ord ∧ x ∈ Gt ∧ x ∉ Gj ⌝ ∗
        osat (<[x:=obl_assigned a' j]> Ω) ∗ othread TP ∗
        oassigned (dom (<[x:=obl_assigned a' j]> Ω)) ∗
        othreadG_obls t (Gt ∖ {[x]}) ∗ othreadG_obls j ({[x]} ∪ Gj) ∗
        oblG_owner x j (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns j x (1/2 + 1/2/2)%Qp.
  Proof.
    iIntros (Hc) "(S& T& A& TGt& TGj& #Ej& #Ex& Go& Oo& Fx)".
    iPoseProof (osat_lookup_owner with "[$S $Ex $Go]") as "%Hx". destruct Hx as (a& Hx).
    iPoseProof (othread_obls_owns_elem with "[$T $TGt $Oo]") as "%HxGt".
    iPoseProof (oassigned_delete_obl _ x with "A") as "(A& _& [(%t'& Go1& Oo1& _) | #Gu])".
    { by eapply elem_of_dom_2. }
    2:{ iExFalso. iPoseProof (osat_lookup_discharged with "[$S $Ex $Gu]") as "%H".
        by rewrite H in Hx. }
    iPoseProof (oblG_owner_agree _ t t' with "[$Go $Go1]") as "%Heq". destruct Heq as [<- _].
    iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iMod (othread_delete_obl with "[$T $TGt $Oo]") as "(T& TGt& Go2)".
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
    iCombine "Go Go'" as "Go".
    iMod (osat_progress_one_owner _ _ _ _ j with "[$S $Go $Fx]") as "(%a'& S& Go& %Gstep)";
      [done|done|].
    iMod (othread_alloc_obl with "[$S $T $TGj $Ex $Go]") as "(S& T& %HxGj& TGj& Oo& Go)".
    iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
    iPoseProof (oassigned_add_obl with "[$A $Ex Go' Oo']") as "A".
    { iLeft. iExists j. iFrame "Go' Oo' Ej". }
    iModIntro. iExists a, a'. iSplitR.
    { iPureIntro. split_and!; [done| |done|done]. inversion Gstep; subst. done. }
    rewrite dom_insert_L.
    replace ({[x]} ∪ dom Ω) with ({[x]} ∪ dom Ω ∖ {[x]}); last first.
    { apply elem_of_dom_2 in Hx. apply set_eq. intros y. rewrite !elem_of_union elem_of_difference.
      destruct (decide (y = x)) as [->|Hy]; set_solver. }
    iCombine "Oo Oo1" as "Oo". iFrame.
  Qed.

  (** All obligations of [S], owned by [t], get the new owner [j]. *)
  Lemma osat_chown_set Ω TP t j Gt Gj S :
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_obls t Gt ∗ othreadG_obls j Gj ∗
    othreadG_elem j ∗
    ([∗ set] x ∈ S, oblG_elem x ∗ oblG_owner x t (1/2 + 1/2/2/2)%Qp ∗
                    othreadG_owns t x (1/2 + 1/2/2)%Qp ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel x c)
    ⊢ |==> ∃ Ω', ⌜ chown_rel S t j Ω Ω' ∧ dom Ω' = dom Ω ∧ S ⊆ Gt ∧ S ## Gj ⌝ ∗
        osat Ω' ∗ othread TP ∗ oassigned (dom Ω') ∗
        othreadG_obls t (Gt ∖ S) ∗ othreadG_obls j (S ∪ Gj) ∗
        ([∗ set] x ∈ S, oblG_owner x j (1/2 + 1/2/2/2)%Qp ∗ othreadG_owns j x (1/2 + 1/2/2)%Qp).
  Proof.
    revert Ω Gt Gj. induction S as [|x S Hx IH] using set_ind_L; intros Ω Gt Gj.
    - iIntros "(S& T& A& TGt& TGj& _& _)". iModIntro. iExists Ω.
      rewrite difference_empty_L left_id_L big_sepS_empty. iFrame. iPureIntro.
      split_and!; [apply chown_rel_empty|done|set_solver|set_solver].
    - iIntros "(S& T& A& TGt& TGj& #Ej& Xs)".
      rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
      iDestruct "Xs" as "[(#Ex& Go& Oo& %c& %Hc& Fx) Xs]".
      iMod (IH with "[$S $T $A $TGt $TGj $Ej $Xs]") as "(%Ω1& %Hrel& S& T& A& TGt& TGj& Ys)".
      destruct Hrel as (Hrel& Hdom& HSGt& HSGj).
      iMod (osat_chown with "[$S $T $A $TGt $TGj $Ej $Ex $Go $Oo $Fx]")
        as "(%a& %a'& %Hx1& S& T& A& TGt& TGj& Go& Oo)"; first done.
      destruct Hx1 as (Hx1& Hlt& HxGt& HxGj).
      iModIntro. iExists (<[x:=obl_assigned (OC:=ord_obl_class) a' j]> Ω1). iFrame "S T A".
      rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton. iFrame "Go Oo Ys".
      replace (Gt ∖ ({[x]} ∪ S)) with (Gt ∖ S ∖ {[x]}) by set_solver.
      replace (({[x]} ∪ S) ∪ Gj) with ({[x]} ∪ (S ∪ Gj)) by set_solver.
      iFrame "TGt TGj". iPureIntro. split_and!.
      + by eapply chown_rel_insert.
      + rewrite dom_insert_L -Hdom. apply elem_of_dom_2 in Hx1. set_solver.
      + set_solver.
      + set_solver.
  Qed.

  Lemma big_sepS_filter_dom (Φ : oid → iProp Σ) (m : gmap oid parent) (S : gset oid) :
    ([∗ set] x ∈ filter (λ x, x ∈ S) (dom m), Φ x) ⊣⊢
    ([∗ map] x ↦ _ ∈ m, if decide (x ∈ S) then Φ x else emp).
  Proof. rewrite filter_dom_L -big_sepM_dom big_sepM_filter'. done. Qed.

  (** ** Moving [k] below a parent of the same owner: no model change *)
  Lemma oforest_move_same Ω Θ p1 p2 K1 K2 k π :
    k ∈ K1 →
    (match p2 with
     | PThread j => obl_owner_of Ω k = Some j
     | PObl q => obl_owner_of Ω q = obl_owner_of Ω k ∧ (obl_fuel_of Ω q < π)%ord ∧
                 (π <= obl_fuel_of Ω k)%ord
     end) →
    oforest Ω Θ ∗ oforestG_kids p1 K1 ∗ oforestG_kids p2 K2 ∗
    (match p2 with PObl _ => oblG_fuel k π | PThread _ => True end)
    ⊢ |==> ⌜ k ∉ K2 ⌝ ∗ oforest Ω Θ ∗ oforestG_kids p1 (K1 ∖ {[k]}) ∗
           oforestG_kids p2 ({[k]} ∪ K2).
  Proof.
    iIntros (Hk Hp2) "(F& K1& K2& Fπ)".
    destruct (decide (p1 = p2)) as [<-|Hne].
    { iDestruct (oforestG_kids_excl with "K1 K2") as %[]. }
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A K1") as "%HK1".
    iPoseProof (oforestG_kids_lookup with "A K2") as "%HK2".
    assert (Hpk : Par !! k = Some p1) by (apply (fwf_par_kids _ _ _ _ WF); eauto).
    assert (HkK2 : k ∉ K2).
    { intros Hin. assert (Par !! k = Some p2) as Hk2 by (apply (fwf_par_kids _ _ _ _ WF); eauto).
      rewrite Hpk in Hk2. by injection Hk2 as ->. }
    assert (Hdom : dom (<[k:=p2]> Par) = dom Par).
    { rewrite dom_insert_L. apply elem_of_dom_2 in Hpk. set_solver. }
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_update (K1 ∖ {[k]}) with "A K1") as "[A K1]".
    iMod (ghost_map_update ({[k]} ∪ K2) with "A K2") as "[A K2]".
    iModIntro. iFrame "K1 K2". iSplit; first done.
    iExists (<[k:=p2]> Par), _. iFrame "A". iSplit.
    { iPureIntro. eapply forest_wf_move_same; [done..|]. destruct p2 as [j|q]; first done.
      destruct Hp2 as (Hq& Hlt& Hle). split; first done. by eapply Ord.lt_le_lt. }
    rewrite Hdom. iFrame "Ts".
    iPoseProof (big_sepM_delete _ _ _ _ Hpk with "Ns") as "[(#Ek& Own& Bnd& _) Ns]".
    iApply big_sepM_insert_delete. iFrame "Ns". rewrite /forest_node. iFrame "Ek Own Bnd".
    destruct p2 as [j|q]; first done. destruct Hp2 as (_& Hlt& _). iExists π. by iFrame "Fπ".
  Qed.

  (** ** Moving [k], owned by [t], below a parent of another owner [j]

      The whole subtree of [k] gets the new owner, and each of its nodes burns a unit: [k]
      burns [u], the other nodes split a unit off their stored piece. Below an obligation,
      [π] is the new piece of [k]. *)
  Lemma oforest_move_cross Ω Θ p1 p2 K1 K2 k t j u π :
    k ∈ K1 → obl_owner_of Ω k = Some t → t ≠ j → (Ord.O < u)%ord →
    (match p2 with
     | PThread j' => j' = j
     | PObl q => obl_owner_of Ω q = Some j ∧ (obl_fuel_of Ω q < π)%ord
     end) →
    osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ oforest Ω Θ ∗
    oforestG_kids p1 K1 ∗ oforestG_kids p2 K2 ∗ oblG_fuel k u ∗
    (match p2 with PObl _ => oblG_fuel k π | PThread _ => True end)
    ⊢ |==> ∃ Ω', ⌜ obls_ndf Ω Ω' ∧ dom Ω' = dom Ω ∧ k ∉ K2 ⌝ ∗
        osat Ω' ∗ othread Θ ∗ oassigned (dom Ω') ∗ oforest Ω' Θ ∗
        oforestG_kids p1 (K1 ∖ {[k]}) ∗ oforestG_kids p2 ({[k]} ∪ K2).
  Proof.
    iIntros (Hk Ht Htj Hu Hp2) "(S& T& A& F& K1& K2& Fu& Fπ)".
    destruct (decide (p1 = p2)) as [<-|Hne].
    { iDestruct (oforestG_kids_excl with "K1 K2") as %[]. }
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& Au& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "Au K1") as "%HK1".
    iPoseProof (oforestG_kids_lookup with "Au K2") as "%HK2".
    assert (Hpk : Par !! k = Some p1) by (apply (fwf_par_kids _ _ _ _ WF); eauto).
    assert (HkK2 : k ∉ K2).
    { intros Hin. assert (Par !! k = Some p2) as Hk2 by (apply (fwf_par_kids _ _ _ _ WF); eauto).
      rewrite Hpk in Hk2. by injection Hk2 as ->. }
    assert (HkD : k ∈ dom Par) by (by eapply elem_of_dom_2).
    set (S := subtree Par k).
    assert (HkS : k ∈ S) by apply subtree_root.
    assert (HSown : ∀ x, x ∈ S → x ∈ dom Par ∧ obl_owner_of Ω x = Some t).
    { intros x Hx. rewrite -Ht. by eapply subtree_owner. }
    assert (HSD : S ⊆ dom Par) by (intros x Hx; by apply HSown).
    assert (Hti : t ∈ Θ) by (by eapply (fwf_owner _ _ _ _ WF)).
    assert (Hj : j ∈ Θ).
    { destruct p2 as [j'|q].
      - subst j'. apply (fwf_kids_dom _ _ _ _ WF (PThread j)). eauto.
      - eapply (fwf_owner _ _ _ _ WF q); last apply Hp2.
        apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    assert (Hq : ∀ q, p2 = PObl q → q ∉ S).
    { intros q -> HqS. destruct (HSown q HqS) as [_ Hoq]. destruct Hp2 as [Hp2 _].
      rewrite Hoq in Hp2. injection Hp2 as ->. done. }
    (* The entries of the threads [t] and [j]: both are running. *)
    iPoseProof (big_sepS_delete _ _ _ Hti with "Ts") as "[(#Et& Ht) Ts]".
    iPoseProof (big_sepS_delete _ _ j with "Ts") as "[(#Ej& Hj) Ts]"; first set_solver.
    iDestruct "Ht" as "[(Txt& TGt) | (_& _& %Hnone)]"; cycle 1.
    { iExFalso. iPureIntro. assert (k ∈ forest_owned Ω (dom Par) t); last set_solver.
      by apply elem_of_filter. }
    iDestruct "Hj" as "[(Txj& TGj) | (_& Kd& %Hnone)]"; cycle 1.
    { iExFalso. destruct p2 as [j'|q].
      - subst j'. iApply (oforestG_kids_excl with "K2 Kd").
      - iPureIntro. assert (q ∈ forest_owned Ω (dom Par) j); last set_solver.
        apply elem_of_filter. split; first apply Hp2.
        apply (fwf_kids_dom _ _ _ _ WF (PObl q)). eauto. }
    (* The node [k]: its old piece is dropped. *)
    iPoseProof (big_sepM_delete _ _ _ _ Hpk with "Ns")
      as "[(#Ek& (%t'& %Ht'& Gok& Ook)& (%βk& #Bk& %Hbk)& _) Ns]".
    rewrite Ht in Ht'. injection Ht' as <-.
    (* The other nodes of the subtree split a unit off their piece. *)
    iAssert (|==> ([∗ map] x ↦ p ∈ delete k Par, if decide (x ∈ S) then
                     (oblG_elem x ∗ oblG_owner x t (1/2 + 1/2/2/2)%Qp ∗
                      othreadG_owns t x (1/2 + 1/2/2)%Qp ∗
                      ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel x c) else emp) ∗
                  ([∗ map] x ↦ p ∈ delete k Par, if decide (x ∈ S) then
                     (oblG_elem x ∗ (∃ β, oblG_bound x β ∗ ⌜ (obl_fuel_of Ω x <= β)%ord ⌝) ∗
                      ∃ c, ⌜ p = PObl c ⌝ ∗ oblG_fuel x (obl_fuel_of Ω c))
                   else forest_node Ω x p))%I with "[Ns]" as ">[Us Ns]".
    { rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Ns").
      iIntros "!> %x %p %Hx (#Ex& Own& Bnd& Pp)". apply lookup_delete_Some in Hx as [Hxk Hx].
      destruct (decide (x ∈ S)) as [HxS|HxS]; last by iFrame.
      destruct (subtree_inv _ _ _ HxS) as [?|(c& Hc& HcS)]; first done.
      rewrite Hx in Hc. injection Hc as ->.
      iDestruct "Own" as "(%tx& %Htx& Gox& Oox)". destruct (HSown x HxS) as [_ Htx'].
      rewrite Htx in Htx'. injection Htx' as ->.
      iDestruct "Pp" as "(%π'& %Hπ'& Fx)".
      iMod (oblG_fuel_lt _ (obl_fuel_of Ω c) with "Fx") as "(Fc& %c'& %Hc'& Fx)"; first done.
      iModIntro. iFrame "Ex Gox Oox Bnd". iSplitL "Fx"; first (iExists c'; by iFrame).
      iExists c. by iFrame. }
    assert (HSk : S ∖ {[k]} = filter (λ x, x ∈ S) (dom (delete k Par))).
    { rewrite dom_delete_L. apply set_eq. intros x. rewrite elem_of_filter elem_of_difference.
      set_solver. }
    iMod (osat_chown_set _ _ t j _ _ S with "[$S $T $A $TGt $TGj $Ej Us Gok Ook Fu]")
      as "(%Ω'& %Hc& S& T& A& TGt& TGj& Os)".
    { rewrite (big_sepS_delete _ S k) // HSk big_sepS_filter_dom. iFrame "Us Ek Gok Ook".
      iExists u. by iFrame. }
    destruct Hc as (Hrel& Hdom& HSGt& HSGj).
    (* The new pieces are below the new fuels. *)
    iAssert (⌜ ∀ q, p2 = PObl q → (obl_fuel_of Ω q < obl_fuel_of Ω' k)%ord ⌝)%I as %Hpk'.
    { iIntros (q ->). destruct Hp2 as [_ Hlt]. iDestruct (osat_fuel_le with "S Fπ") as %Hle.
      destruct Hrel as [_ Hin]. destruct (Hin k HkS) as (a& a'& Ha& Ha'& _).
      iPureIntro. eapply Ord.lt_le_lt; first done. rewrite /obl_fuel_of Ha'. by eapply Hle. }
    iAssert (⌜ ∀ x c, x ∈ S → x ≠ k → Par !! x = Some (PObl c) →
               (obl_fuel_of Ω c <= obl_fuel_of Ω' x)%ord ⌝)%I as %Hpx.
    { iIntros (x c HxS Hxk Hx).
      iPoseProof (big_sepM_lookup _ _ x (PObl c) with "Ns") as "H".
      { by rewrite lookup_delete_ne. }
      rewrite decide_True //. iDestruct "H" as "(_& _& %c'& %Hc'& Fx)". injection Hc' as <-.
      iDestruct (osat_fuel_le with "S Fx") as %Hle.
      destruct Hrel as [_ Hin]. destruct (Hin x HxS) as (a& a'& Ha& Ha'& _).
      iPureIntro. rewrite /obl_fuel_of Ha'. by eapply Hle. }
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_update (K1 ∖ {[k]}) with "Au K1") as "[Au K1]".
    iMod (ghost_map_update ({[k]} ∪ K2) with "Au K2") as "[Au K2]".
    iModIntro. iExists Ω'. iFrame "S T A K1 K2". iSplit.
    { iPureIntro. split_and!; [by eapply chown_rel_ndf|done|done]. }
    rewrite -lock. iExists (<[k:=p2]> Par), _. iFrame "Au". iSplit.
    { iPureIntro.
      assert (Hp2' : match p2 with
                     | PThread j' => j' = j | PObl q => obl_owner_of Ω q = Some j
                     end) by (destruct p2; [done|apply Hp2]).
      by eapply forest_wf_move_cross. }
    assert (Hdom' : dom (<[k:=p2]> Par) = dom Par) by (rewrite dom_insert_L; set_solver).
    rewrite Hdom'.
    pose proof (λ i, forest_owned_chown _ _ (dom Par) _ _ _ i Hrel HSD) as Hown.
    iSplitL "Ts Txt TGt Txj TGj".
    { iApply (big_sepS_delete _ _ _ Hti). iSplitL "Txt TGt".
      { iFrame "Et". iLeft. iFrame "Txt". rewrite Hown decide_False // decide_True //. }
      iApply (big_sepS_delete _ _ j); first set_solver. iSplitL "Txj TGj".
      { iFrame "Ej". iLeft. iFrame "Txj". rewrite Hown decide_True //. }
      iApply (big_sepS_impl with "Ts"). iIntros "!> %i %Hi (#Ei& H)". iFrame "Ei".
      rewrite Hown decide_False; last set_solver. rewrite decide_False; last set_solver. done. }
    iApply big_sepM_insert_delete.
    iPoseProof (big_sepS_delete _ S k with "Os") as "[(Gok& Ook) Os]"; first done.
    iSplitL "Gok Ook Fπ".
    { rewrite /forest_node. iFrame "Ek". iSplitL "Gok Ook".
      { iExists j. iFrame. iPureIntro. rewrite (chown_rel_owner _ _ _ _ _ _ Hrel) decide_True //. }
      iSplitR.
      { iExists βk. iFrame "Bk". iPureIntro. etrans; last exact Hbk. apply Ord.lt_le.
        by apply (chown_rel_fuel_in _ _ _ _ _ _ Hrel). }
      destruct p2 as [j'|q]; first done. iExists π. iFrame "Fπ". iPureIntro.
      rewrite (chown_rel_fuel_out _ _ _ _ _ _ Hrel); last by apply Hq. apply Hp2. }
    rewrite HSk big_sepS_filter_dom.
    iDestruct (big_sepM_sep_2 with "Os Ns") as "ON".
    iApply (big_sepM_impl with "ON"). iIntros "!> %x %p %Hx [O N]".
    apply lookup_delete_Some in Hx as [Hxk Hx].
    destruct (decide (x ∈ S)) as [HxS|HxS].
    - iDestruct "O" as "(Gox& Oox)". iDestruct "N" as "(#Ex& Bnd& %c& -> & Fc)".
      rewrite /forest_node. iFrame "Ex". iSplitL "Gox Oox".
      { iExists j. iFrame. iPureIntro.
        rewrite (chown_rel_owner _ _ _ _ _ _ Hrel) decide_True //. }
      iSplitL "Bnd".
      { iDestruct "Bnd" as (β) "[Bx %Hb]". iExists β. iFrame "Bx". iPureIntro.
        etrans; last exact Hb. apply Ord.lt_le. by apply (chown_rel_fuel_in _ _ _ _ _ _ Hrel). }
      iExists (obl_fuel_of Ω c). iFrame "Fc". iPureIntro.
      destruct (subtree_inv _ _ _ HxS) as [?|(c'& Hc'& HcS)]; first done.
      rewrite Hx in Hc'. injection Hc' as <-. by apply (chown_rel_fuel_in _ _ _ _ _ _ Hrel).
    - iClear "O". iDestruct "N" as "(#Ex& (%tx& %Htx& Own)& (%β& #Bx& %Hb)& Pp)".
      rewrite /forest_node. iFrame "Ex". iSplitL "Own".
      { iExists tx. iFrame "Own". iPureIntro.
        rewrite (chown_rel_owner _ _ _ _ _ _ Hrel) decide_False //. }
      iSplitR.
      { iExists β. iFrame "Bx". iPureIntro. rewrite (chown_rel_fuel_out _ _ _ _ _ _ Hrel) //. }
      destruct p as [i|c]; first done. iDestruct "Pp" as "(%π'& %Hπ'& Fx)". iExists π'.
      iFrame "Fx". iPureIntro.
      assert (HcS : c ∉ S) by (intros HcS; by apply HxS, (subtree_closed _ _ _ c)).
      rewrite (chown_rel_fuel_out _ _ _ _ _ _ Hrel) //.
  Qed.

  (** ** Moving a grandchild up: [x], a child of [k], moves to the parent [p] of [k]

      No model change and no new fuel: [x] already has the owner of [p], and the piece that
      [x] stores is above the fuel of [k], hence above the fuel of [p]. *)
  Lemma oforest_move_up Ω Θ p K k Kk x :
    k ∈ K → x ∈ Kk →
    oforest Ω Θ ∗ oforestG_kids p K ∗ oforestG_kids (PObl k) Kk
    ⊢ |==> ⌜ x ∉ K ⌝ ∗ oforest Ω Θ ∗ oforestG_kids p ({[x]} ∪ K) ∗
           oforestG_kids (PObl k) (Kk ∖ {[x]}).
  Proof.
    iIntros (Hk Hx) "(F& Kp& Kk)".
    destruct (decide (p = PObl k)) as [->|Hne].
    { iDestruct (oforestG_kids_excl with "Kk Kp") as %[]. }
    rewrite /oforest -!lock. iDestruct "F" as "(%Par& %Kids& A& %WF& Ts& Ns)".
    iPoseProof (oforestG_kids_lookup with "A Kp") as "%HK".
    iPoseProof (oforestG_kids_lookup with "A Kk") as "%HKk".
    assert (Hkp : Par !! k = Some p) by (apply (fwf_par_kids _ _ _ _ WF); eauto).
    assert (Hxk : Par !! x = Some (PObl k)) by (apply (fwf_par_kids _ _ _ _ WF); eauto).
    assert (HxK : x ∉ K).
    { intros Hin. assert (Par !! x = Some p) as Hx' by (apply (fwf_par_kids _ _ _ _ WF); eauto).
      rewrite Hxk in Hx'. injection Hx' as Heq. apply Hne. by rewrite Heq. }
    destruct (fwf_obl _ _ _ _ WF _ _ Hxk) as [Hokx Hlt].
    assert (Hdom : dom (<[x:=p]> Par) = dom Par).
    { rewrite dom_insert_L. apply elem_of_dom_2 in Hxk. set_solver. }
    rewrite /oforestG_kids_auth /oforestG_kids.
    iMod (ghost_map_update (Kk ∖ {[x]}) with "A Kk") as "[A Kk]".
    iMod (ghost_map_update ({[x]} ∪ K) with "A Kp") as "[A Kp]".
    iModIntro. iFrame "Kp Kk". iSplit; first done.
    iExists (<[x:=p]> Par), _. iFrame "A". iSplit.
    { iPureIntro. eapply forest_wf_move_same; [done..|]. destruct p as [j|q].
      - rewrite -Hokx. by apply (fwf_thread _ _ _ _ WF).
      - destruct (fwf_obl _ _ _ _ WF _ _ Hkp) as [Hoqk Hltq]. split; first by rewrite Hoqk.
        by etrans. }
    rewrite Hdom. iFrame "Ts".
    iPoseProof (big_sepM_delete _ _ _ _ Hxk with "Ns") as "[(#Ex& Own& Bnd& Pp) Ns]".
    iApply big_sepM_insert_delete. iFrame "Ns". rewrite /forest_node. iFrame "Ex Own Bnd".
    destruct p as [j|q]; first done. iDestruct "Pp" as "(%π& %Hπ& Fx)". iExists π.
    iFrame "Fx". iPureIntro. destruct (fwf_obl _ _ _ _ WF _ _ Hkp) as [_ Hltq]. by etrans.
  Qed.

End oforest.

(** Allocation of an empty forest. *)
Lemma oforest_alloc `{SI : sidx} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!othreadGS.othreadGS Σ} `{!oforestGpreS Σ} :
  ⊢ |==> ∃ _ : oforestGS Σ, oforest ∅ ∅.
Proof.
  iMod (ghost_map_alloc_empty) as (γ) "HA".
  iModIntro. iExists (OforestG SI _ _ γ). rewrite /oforest -!lock.
  iExists ∅, ∅. rewrite /oforestG_kids_auth. iFrame "HA".
  iSplit; [iPureIntro; apply forest_wf_empty|]. by rewrite big_sepS_empty big_sepM_empty.
Qed.
