From stdpp Require Import base.
From liris.prelude Require Import axioms wf_structs ordinal_facts.

Section measure.
  Context {L : Type} {ltL : L → L → Prop} {WF_ltL : well_founded ltL}.
  Context {η : Ord.t → Ord.t} {η_proper_le : Proper (Ord.le ==> Ord.le) η}.

  Inductive measurable_syntax : Type :=
  | ms_unit (n : nat)
  | ms_add (s1 s2 : measurable_syntax)
  | ms_extend (s : measurable_syntax).

  Definition L_sub (u : L) : Type := sig (λ v, ltL v u).
  Remark measure_oblig : ∀ (l : L) (m : L_sub l), ltL (proj1_sig m) l.
  Proof using. intros. destruct m. auto. Qed.

  Fixpoint measure_rec (α : Ord.t) (l : L) (ACC : Acc ltL l) {struct ACC} :
    ∀ (s : measurable_syntax), Ord.t :=
  (fix go s {struct s} :=
     match s with
     | ms_unit n =>
         n
     | ms_add s1 s2 =>
         (go s1 ⊕ go s2)%ord
     | ms_extend s1 =>
         ((go s1 × α) ⊕
            (go s1 ×
               (η (Ord.join (λ (m : L_sub l),
                               Ord.join (λ (t : measurable_syntax),
                                           measure_rec α
                                             (proj1_sig m) (Acc_inv ACC (measure_oblig l m))
                                             t))))))%ord
     end).

  (* Assumes Jacobsthal.expn ω ω is large enough for self-terminating codes. *)
  Definition measure (l : L) (s : measurable_syntax) : Ord.t :=
    measure_rec (ω ↑ ω)%ord l (WF_ltL l) s.

  Lemma measure_rec_proof_irrelevance α l ACC1 ACC2 s :
    measure_rec α l ACC1 s = measure_rec α l ACC2 s.
  Proof using Type*.
    revert ACC1 ACC2 s. induction l as [l IH] using (well_founded_ind WF_ltL).
    intros. induction s.
    { destruct ACC1, ACC2. simpl. auto. }
    { destruct ACC1, ACC2. simpl. simpl in IHs1, IHs2. rewrite IHs1, IHs2. auto. }
    { destruct ACC1, ACC2. simpl. simpl in IHs. rewrite !IHs. f_equal.
      do 3 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
      apply IH. destruct x. auto. }
  Qed.

  Lemma measure_unfold l s :
    measure l s =
    match s with
    | ms_unit n =>
        n
    | ms_add s1 s2 =>
        (measure l s1 ⊕ measure l s2)%ord
    | ms_extend s1 =>
        ((measure l s1 × (ω ↑ ω)) ⊕
           (measure l s1 ×
              η (Ord.join (λ (m : L_sub l),
                             Ord.join (λ (t : measurable_syntax),
                                         measure (proj1_sig m) t)))))%ord
    end.
  Proof using Type*.
    unfold measure. destruct (WF_ltL l). destruct s; simpl; auto.
    f_equal. do 3 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
    apply measure_rec_proof_irrelevance.
  Qed.

  Global Opaque measure_rec measure.

  (** Reduction rules *)
  Lemma measure_unit (l : L) n :
    measure l (ms_unit n) = (n)%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_unit _)).
    auto.
  Qed.

  Lemma measure_add (l : L) s1 s2 :
    measure l (ms_add s1 s2) = (measure l s1 ⊕ measure l s2)%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_add _ _)).
    auto.
  Qed.

  Lemma measure_extend_le (l1 l2 : L) (s : measurable_syntax) :
    ltL l1 l2 →
    ∀ (t : measurable_syntax),
    (((measure l2 s × (ω ↑ ω)) ⊕ (measure l2 s × η (measure l1 t)))
     <= measure l2 (ms_extend s))%ord.
  Proof using Type*.
    intros Hlt d. rewrite (measure_unfold _ (ms_extend _)).
    apply Hessenberg.le_add_r. apply Jacobsthal.le_mult_r.
    apply η_proper_le.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. apply Ord.join_upperbound.
  Qed.

  Lemma measure_extend_le_const (l : L) (s : measurable_syntax) :
    ((measure l s × (ω ↑ ω)) <= measure l (ms_extend s))%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_extend _)).
    etransitivity; last eapply Hessenberg.add_base_l.
    reflexivity.
  Qed.

  Lemma measure_extend_le_layer (l1 l2 : L) (s : measurable_syntax) :
    ltL l1 l2 →
    ∀ (t : measurable_syntax),
    ((measure l2 s × η (measure l1 t)) <= measure l2 (ms_extend s))%ord.
  Proof using Type*.
    intros Hlt d. etransitivity; last eapply (measure_extend_le l1 l2); eauto.
    eapply Hessenberg.add_base_r.
  Qed.
  Lemma measure_extend_le_layer_alt (l1 l2 : L) (o : Ord.t) (s : measurable_syntax) :
    ltL l1 l2 →
    (∃ (t : measurable_syntax), (o <= η (measure l1 t))%ord) →
    ((measure l2 s × o) <= measure l2 (ms_extend s))%ord.
  Proof using Type*.
    intros Hlt (t& ?).
    etransitivity; last eapply (measure_extend_le_layer l1 l2); eauto.
    eapply Jacobsthal.le_mult_r. eauto.
  Qed.

End measure.

Section aux.

  Definition ord_tree_lt_tc {A : Type} : ord_tree A -> ord_tree A -> Prop :=
    clos_trans_n1 _ (ord_tree_lt (A:=A)).

  Lemma ord_tree_lt_tc_well_founded A :
    well_founded (@ord_tree_lt_tc A).
  Proof. apply clos_trans_well_founded, ord_tree_lt_well_founded. Qed.

  Lemma ord_tree_join_tc A (P : A -> Prop) (R : A -> ord_tree A -> Prop)
    (ORD : forall a (SAT : P a), exists o, R a o)
    :
    exists o1, forall (a : A) (SAT : P a),
    exists o0, R a o0 /\ ord_tree_lt_tc o0 o1.
  Proof.
    pose proof (ord_tree_join _ _ _ ORD) as (?& Hj).
    exists x. intros. specialize (Hj _ SAT). destruct Hj as (?&?&?).
    exists x0. split; first auto. econstructor. auto.
  Qed.

  Global Instance ord_tree_lt_tc_transitive A : Transitive (@ord_tree_lt_tc A).
  Proof. apply _. Qed.

End aux.

Section layer.

  Definition layerT : Type := ord_tree nat.
  Definition layer_lt : layerT → layerT → Prop := ord_tree_lt_tc.

  Lemma layer_lt_well_founded : well_founded layer_lt.
  Proof. apply ord_tree_lt_tc_well_founded. Qed.
  Global Instance layer_lt_transitive : Transitive layer_lt.
  Proof. apply _. Qed.

  Definition layer_zero : layerT := ord_tree_base.
  Definition layer_join (ls : nat → layerT) : layerT :=
    ord_tree_cons ls.

  Lemma layer_join_upperbound ls :
    ∀ l n, l = ls n →
           layer_lt l (layer_join ls).
  Proof. intros. subst. econstructor 1. econstructor. Qed.

  (** A layer has a base and has a nat-like ordering that starts from the base. *)
  Fixpoint layer (b : layerT) (n : nat) : layerT :=
    match n with
    | O => b
    | S m => layer_join (λ _, layer b m)
    end.

  Global Instance layer_proper_lt_nat b :
    Proper (lt ==> layer_lt) (layer b).
  Proof.
    repeat intro. induction H.
    - simpl. eapply layer_join_upperbound; auto.
    - etransitivity; first eauto. simpl. eapply layer_join_upperbound; auto.
  Qed.

  Lemma layer_lt_base_S :
    ∀ b n, layer_lt b (layer b (S n)).
  Proof.
    intros. induction n; simpl.
    { apply layer_join_upperbound; auto. exact 0. }
    etransitivity; first eauto. simpl.
    eapply layer_join_upperbound; auto.
  Qed.

  Lemma layer_nat_cases :
    ∀ b n, (n = 0 ∧ b = layer b n) ∨ (0 < n ∧ layer_lt b (layer b n)).
  Proof.
    intros. destruct n.
    - left. split; auto.
    - right. split; first apply PeanoNat.Nat.lt_0_succ. apply layer_lt_base_S.
  Qed.

  Lemma layer_lt_base_upperbound b1 b2 :
    (∀ n, layer_lt (layer b1 n) b2) →
    ∀ n m, layer_lt (layer b1 n) (layer b2 m).
  Proof.
    intros. destruct (layer_nat_cases b2 m).
    - destruct H0; subst. rewrite <- H1. eauto.
    - destruct H0. etransitivity; eauto.
  Qed.

  (** An upperbound of any layer with base b. *)
  Definition layer_next (b : layerT) : layerT := layer_join (layer b).

  Lemma layer_next_upperbound b :
    ∀ l n, l = layer b n →
           layer_lt l (layer_next b).
  Proof. intros. eapply layer_join_upperbound; eauto. Qed.

  Fixpoint layer_next_iter (l : nat) : layerT :=
    match l with
    | O => layer_zero
    | S l' => layer_next (layer_next_iter l')
    end.

  Lemma layer_next_iter_proper_lt :
    Proper (lt ==> layer_lt) (layer_next_iter).
  Proof.
    repeat intro. induction H.
    - simpl. eapply (layer_next_upperbound _ _ 0). auto.
    - etransitivity; first eauto. simpl. eapply (layer_next_upperbound _ _ 0). auto.
  Qed.

  Lemma layer_next_iter_upperbound l1 l2 :
    l1 < l2 →
    ∀ n, layer_lt (layer (layer_next_iter l1) n) (layer_next_iter l2).
  Proof.
    intros LT. induction LT; intros.
    - simpl. eapply layer_next_upperbound; eauto.
    - etransitivity; first eauto. eapply layer_next_iter_proper_lt. eauto.
  Qed.

  (** Some useful instances *)
  (* A pair of nats with the lexicographical order *)
  Definition layer_pair (l n : nat) : layerT :=
    layer (layer_next_iter l) n.

  Lemma layer_pair_lt_fst l1 l2 :
    l1 < l2 →
    ∀ n m, layer_lt (layer_pair l1 n) (layer_pair l2 m).
  Proof.
    intros. unfold layer_pair. eapply layer_lt_base_upperbound.
    intros. eapply layer_next_iter_upperbound; auto.
  Qed.
  Lemma layer_pair_lt_snd l :
    Proper (lt ==> layer_lt) (layer_pair l).
  Proof.
    repeat intro. unfold layer_pair. apply layer_proper_lt_nat. auto.
  Qed.

  Definition layer_pair_omega (n : nat) : layerT :=
    layer (layer_join (λ l, layer_pair l 0)) n.

  Lemma layer_pair_omega_upperbound l :
    ∀ n m, layer_lt (layer_pair l n) (layer_pair_omega m).
  Proof.
    intros. unfold layer_pair_omega.
    destruct (layer_nat_cases (layer_join (λ l0 : nat, layer_pair l0 0)) m).
    - destruct H; subst. rewrite <-H0. etransitivity.
      + eapply (layer_pair_lt_fst l (S l)). auto.
      + eapply layer_join_upperbound; eauto.
    - destruct H. etransitivity; last eauto.
      etransitivity.
      + eapply (layer_pair_lt_fst l (S l)). auto.
      + eapply layer_join_upperbound; eauto.
  Qed.
  Lemma layer_pair_omega_proper_lt_nat :
    Proper (lt ==> layer_lt) (layer_pair_omega).
  Proof.
    repeat intro. apply layer_proper_lt_nat. auto.
  Qed.

  (* A nat *)
  Definition layer_nat (n : nat) : layerT := layer_pair 0 n.
  Definition layer_nat_omega : layerT := layer_pair 1 0.

  Lemma layer_omega_upperbound :
    ∀ n, layer_lt (layer_nat n) layer_nat_omega.
  Proof. intros. eapply layer_pair_lt_fst. auto. Qed.

End layer.
