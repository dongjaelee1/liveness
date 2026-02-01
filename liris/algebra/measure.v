From stdpp Require Import base.
From liris.prelude Require Import axioms ordinal_facts.
From liris.prelude Require Export wf_structs.

Section measure.
  Context `{!well_founded_class L} `{!ord_mono_fun_class}.

  Inductive measurable_syntax  : Type :=
  (* Any well-founded ordering of type A can be embedded as long as the universe is consistent. *)
  | ms_embed {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (a : A)
  | ms_embed_set {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  | ms_large
  | ms_add (s1 s2 : measurable_syntax)
  | ms_mult (s1 s2 : measurable_syntax)
  | ms_expn (s1 s2 : measurable_syntax)
  | ms_extend.
  (* | ms_extend (s : measurable_syntax). *)

  (* Useful instances. *)
  Definition ms_nat (n : nat) : measurable_syntax :=
    ms_embed PeanoNat.Nat.lt_wf_0 n.
  Definition ms_omega : measurable_syntax :=
    ms_embed_set PeanoNat.Nat.lt_wf_0.

  Definition L_sub (u : L) : Type := sig (λ v, ltL v u).
  Remark measure_oblig : ∀ (l : L) (m : L_sub l), ltL (proj1_sig m) l.
  Proof using. intros. destruct m. auto. Qed.

  Fixpoint measure_rec (l : L) (ACC : Acc ltL l) {struct ACC} :
    ∀ (s : measurable_syntax), Ord.t :=
  (fix go s {struct s} :=
     match s with
     | ms_embed wf_ltA a =>
         Ord.from_wf wf_ltA a
     | ms_embed_set wf_ltA =>
         Ord.from_wf_set wf_ltA
     | ms_large =>
         Ord.large
     | ms_add s1 s2 =>
         (go s1 ⊕ go s2)%ord
     | ms_mult s1 s2 =>
         (go s1 × go s2)%ord
     | ms_expn s1 s2 =>
         (go s1 ↑ go s2)%ord
     | ms_extend =>
         (η (Ord.join (λ (m : L_sub l),
                         Ord.join (λ (t : measurable_syntax),
                                     measure_rec
                                       (proj1_sig m) (Acc_inv ACC (measure_oblig l m))
                                       t))))
     end).

  (* We assume that Jacobsthal.expn ω ω is large enough. *)
  Definition measure (l : L) (s : measurable_syntax) : Ord.t :=
    measure_rec l (wf_ltL l) s.

  Lemma measure_rec_proof_irrelevance l ACC1 ACC2 s :
    measure_rec l ACC1 s = measure_rec l ACC2 s.
  Proof using Type*.
    revert ACC1 ACC2 s. induction l as [l IH] using (well_founded_ind wf_ltL).
    intros. induction s.
    { destruct ACC1, ACC2. simpl. auto. }
    { destruct ACC1, ACC2. simpl. auto. }
    { destruct ACC1, ACC2. simpl. auto. }
    { destruct ACC1, ACC2. simpl. simpl in IHs1, IHs2. rewrite IHs1, IHs2. auto. }
    { destruct ACC1, ACC2. simpl. simpl in IHs1, IHs2. rewrite IHs1, IHs2. auto. }
    { destruct ACC1, ACC2. simpl. simpl in IHs1, IHs2. rewrite IHs1, IHs2. auto. }
    { destruct ACC1, ACC2. simpl. do 2 f_equal.
      apply func_ext. intros. f_equal. apply func_ext. intros.
      apply IH. destruct x. auto. }
  Qed.

  Lemma measure_unfold l s :
    measure l s =
    match s with
    | ms_embed wf_ltA a =>
        Ord.from_wf wf_ltA a
    | ms_embed_set wf_ltA =>
        Ord.from_wf_set wf_ltA
    | ms_large =>
        Ord.large
    | ms_add s1 s2 =>
        (measure l s1 ⊕ measure l s2)%ord
    | ms_mult s1 s2 =>
        (measure l s1 × measure l s2)%ord
    | ms_expn s1 s2 =>
        (measure l s1 ↑ measure l s2)%ord
    | ms_extend =>
        (η (Ord.join (λ (m : L_sub l),
                        Ord.join (λ (t : measurable_syntax),
                                    measure (proj1_sig m) t))))
    end.
  Proof using Type*.
    unfold measure. destruct (wf_ltL l). destruct s; simpl; auto.
    do 2 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
    apply measure_rec_proof_irrelevance.
  Qed.

  (** Reduction rules *)
  Lemma measure_embed {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (l : L) (a : A) :
    measure l (ms_embed wf_ltA a) = Ord.from_wf wf_ltA a.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_embed _ _)). auto.
  Qed.

  Lemma measure_embed_set {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (l : L) :
    measure l (ms_embed_set wf_ltA) = Ord.from_wf_set wf_ltA.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_embed_set _)). auto.
  Qed.

  Lemma measure_large (l : L) :
    measure l (ms_large) = Ord.large.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_large)). auto.
  Qed.

  Lemma measure_add (l : L) s1 s2 :
    measure l (ms_add s1 s2) = (measure l s1 ⊕ measure l s2)%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_add _ _)). auto.
  Qed.

  Lemma measure_mult (l : L) s1 s2 :
    measure l (ms_mult s1 s2) = (measure l s1 × measure l s2)%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_mult _ _)). auto.
  Qed.

  Lemma measure_expn (l : L) s1 s2 :
    measure l (ms_expn s1 s2) = (measure l s1 ↑ measure l s2)%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_expn _ _)). auto.
  Qed.

  Lemma measure_extend_le (l1 l2 : L) :
    ltL l1 l2 →
    ∀ (t : measurable_syntax), (η (measure l1 t) <= measure l2 (ms_extend))%ord.
  Proof using Type*.
    intros Hlt d. rewrite (measure_unfold _ (ms_extend)).
    apply η_proper_le.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. apply Ord.join_upperbound.
  Qed.

  (* Useful instances. *)
  Lemma measure_nat (l : L) n :
    (measure l (ms_nat n) == n)%ord.
  Proof using Type*.
    unfold ms_nat. rewrite (measure_unfold _ (ms_embed _ _)).
    symmetry. apply Ord.from_nat_from_peano_lt.
  Qed.

  Lemma measure_omega (l : L) :
    (measure l (ms_omega) == ω)%ord.
  Proof using Type*.
    unfold ms_omega. rewrite (measure_unfold _ (ms_embed_set _)).
    symmetry. apply Ord.omega_from_peano_lt_set.
  Qed.

  (** Properties *)
  Lemma measure_embed_lt {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) l (a1 a2 : A) :
    ltA a1 a2 →
    (measure l (ms_embed wf_ltA a1) < measure l (ms_embed wf_ltA a2))%ord.
  Proof using.
    intros. rewrite !measure_embed. apply Ord.lt_from_wf. auto.
  Qed.

  Lemma measure_extend_le_const (l : L) (s : measurable_syntax) :
    ((measure l s × (ω ↑ ω)) <= measure l (ms_extend s))%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_extend _)).
    etransitivity; last eapply Hessenberg.add_base_l.
    reflexivity.
  Qed.

  Lemma measure_extend_le_large (l : L) (s : measurable_syntax) :
    ((measure l s × Ord.large) <= measure l (ms_extend s))%ord.
  Proof using Type*.
    rewrite (measure_unfold _ (ms_extend _)).
    etransitivity; last eapply Hessenberg.add_base_r.
    etransitivity; last eapply Hessenberg.add_base_l.
    reflexivity.
  Qed.
  Lemma measure_extend_le_wf_set {A : Type} {ltA : A → A → Prop}
    (wf_ltA : well_founded ltA) (l : L) (s : measurable_syntax) :
    ((measure l s × (Ord.from_wf_set wf_ltA)) <= measure l (ms_extend s))%ord.
  Proof using Type*.
    etransitivity; last eapply measure_extend_le_large.
    eapply Jacobsthal.le_mult_r. apply Ord.lt_le. apply Ord.large_lt_from_wf_set.
  Qed.
  Lemma measure_extend_le_wf {A : Type} {ltA : A → A → Prop}
    (wf_ltA : well_founded ltA) (a : A) (l : L) (s : measurable_syntax) :
    ((measure l s × (Ord.from_wf wf_ltA a)) <= measure l (ms_extend s))%ord.
  Proof using Type*.
    etransitivity; last eapply measure_extend_le_wf_set.
    eapply Jacobsthal.le_mult_r. apply Ord.lt_le. apply Ord.from_wf_set_upperbound.
  Qed.

  Lemma measure_extend_le_layer (l1 l2 : L) (s : measurable_syntax) :
    ltL l1 l2 →
    ∀ (t : measurable_syntax),
    ((measure l2 s × η (measure l1 t)) <= measure l2 (ms_extend s))%ord.
  Proof using Type*.
    intros Hlt d. etransitivity; last eapply (measure_extend_le l1 l2); eauto.
    etransitivity; last eapply Hessenberg.add_base_r.
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

  Lemma measure_finite_add l n1 n2 :
    (measure l (ms_finite (n1 + n2)) == (measure l (ms_finite n1) ⊕ measure l (ms_finite n2)))%ord.
  Proof using.
    revert n2. induction n1; intros; simpl.
    { rewrite measure_zero, Hessenberg.add_O_l. reflexivity. }
    rewrite !measure_add, !measure_one, (IHn1 n2).
    rewrite !Hessenberg.add_assoc. reflexivity.
  Qed.

  Lemma measure_finite_S (l : L) (n : nat) :
    (measure l (ms_finite (S n)) == (measure l (ms_finite 1) ⊕ measure l (ms_finite n)))%ord.
  Proof using.
    rewrite <-measure_finite_add. reflexivity.
  Qed.

End measure.
Global Opaque measure_rec measure ms_finite.

Declare Scope msyn_scope.
Delimit Scope msyn_scope with M.

Coercion ms_finite : nat >-> measurable_syntax.
Infix "+" := ms_add : msyn_scope.
Notation "'⟪' s '⟫'" := (ms_extend s%M) (at level 50, format "⟪ s ⟫") : msyn_scope.

Global Instance nat_inhabited : Inhabited nat := populate 0.

Section layer.

  Definition layer : Type := ord_tree nat.
  Definition layer_lt : layer → layer → Prop := ord_tree_lt_tc.

  Lemma layer_lt_well_founded : well_founded layer_lt.
  Proof. apply ord_tree_lt_tc_well_founded. Qed.
  Global Instance layer_lt_transitive : Transitive layer_lt.
  Proof. apply _. Qed.

  Definition layer_zero : layer := ord_tree_base.
  Definition layer_join (ls : nat → layer) : layer :=
    ord_tree_cons ls.

  Lemma layer_zero_bot : ∀ (l : layer), (l = layer_zero) ∨ (layer_lt layer_zero l).
  Proof. eapply ord_tree_base_bot. econstructor. exact 0. Qed.

  Lemma layer_join_upperbound ls :
    ∀ l n, l = ls n →
           layer_lt l (layer_join ls).
  Proof. intros. subst. econstructor 1. econstructor. Qed.

  (** A layer has a base and has a nat-like ordering that starts from the base. *)
  Fixpoint layer_def (b : layer) (n : nat) : layer :=
    match n with
    | O => b
    | S m => layer_join (λ _, layer_def b m)
    end.

  Lemma layer_unfold b n :
    layer_def b n =
    match n with
    | O => b
    | S m => layer_join (λ _, layer_def b m)
    end.
  Proof. destruct n; auto. Qed.

  Global Instance layer_proper_lt_nat b :
    Proper (lt ==> layer_lt) (layer_def b).
  Proof.
    repeat intro. induction H.
    - simpl. eapply layer_join_upperbound; auto.
    - etransitivity; first eauto. simpl. eapply layer_join_upperbound; auto.
  Qed.

  Lemma layer_lt_base_S :
    ∀ b n, layer_lt b (layer_def b (S n)).
  Proof.
    intros. induction n; simpl.
    { apply layer_join_upperbound; auto. exact 0. }
    etransitivity; first eauto. simpl.
    eapply layer_join_upperbound; auto.
  Qed.

  Lemma layer_nat_cases :
    ∀ b n, (n = 0 ∧ b = layer_def b n) ∨ (0 < n ∧ layer_lt b (layer_def b n)).
  Proof.
    intros. destruct n.
    - left. split; auto.
    - right. split; first apply PeanoNat.Nat.lt_0_succ. apply layer_lt_base_S.
  Qed.

  Lemma layer_lt_base_upperbound b1 b2 :
    (∀ n, layer_lt (layer_def b1 n) b2) →
    ∀ n m, layer_lt (layer_def b1 n) (layer_def b2 m).
  Proof.
    intros. destruct (layer_nat_cases b2 m).
    - destruct H0; subst. rewrite <- H1. eauto.
    - destruct H0. etransitivity; eauto.
  Qed.

  (** An upperbound of any layer with base b. *)
  Definition layer_next (b : layer) : layer := layer_join (layer_def b).

  Lemma layer_next_upperbound b :
    ∀ l n, l = layer_def b n →
           layer_lt l (layer_next b).
  Proof. intros. eapply layer_join_upperbound; eauto. Qed.

  Fixpoint layer_next_iter (b : layer) (l : nat) : layer :=
    match l with
    | O => b
    | S l' => layer_next (layer_next_iter b l')
    end.

  Lemma layer_next_iter_unfold b l :
    layer_next_iter b l =
    match l with
    | O => b
    | S l' => layer_next (layer_next_iter b l')
    end.
  Proof. destruct l; auto. Qed.

  Lemma layer_next_iter_proper_lt b :
    Proper (lt ==> layer_lt) (layer_next_iter b).
  Proof.
    repeat intro. induction H.
    - simpl. eapply (layer_next_upperbound _ _ 0). auto.
    - etransitivity; first eauto. simpl. eapply (layer_next_upperbound _ _ 0). auto.
  Qed.

  Lemma layer_next_iter_upperbound b l1 l2 :
    l1 < l2 →
    ∀ n, layer_lt (layer_def (layer_next_iter b l1) n) (layer_next_iter b l2).
  Proof.
    intros LT. induction LT; intros.
    - simpl. eapply layer_next_upperbound; eauto.
    - etransitivity; first eauto. eapply layer_next_iter_proper_lt. eauto.
  Qed.

  (** Some useful instances *)
  (* A pair of nats with the lexicographical order *)
  Definition layer_pair (l n : nat) : layer :=
    layer_def (layer_next_iter layer_zero l) n.

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

  Definition layer_pair_omega (n : nat) : layer :=
    layer_def (layer_join (λ l, layer_pair l 0)) n.

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
  Definition layer_nat (n : nat) : layer := layer_pair 0 n.
  Definition layer_nat_omega : layer := layer_pair 1 0.

  Lemma layer_omega_upperbound :
    ∀ n, layer_lt (layer_nat n) layer_nat_omega.
  Proof. intros. eapply layer_pair_lt_fst. auto. Qed.

End layer.
Global Opaque layer layer_def layer_next layer_next_iter.

Global Instance layer_well_founded_class : well_founded_class layer :=
  Build_well_founded_class _ _ layer_lt_well_founded.

Declare Scope layer_scope.
Delimit Scope layer_scope with L.

Notation "'0ₗ'" := layer_zero : layer_scope.
Infix "<" := layer_lt : layer_scope.
Notation "b '⨣' n" := (layer_def b%L n) (at level 50, format "b  ⨣  n") : layer_scope.
Notation "'⌈' l '⌉'" := (layer_next l%L) (at level 50, format "⌈ l ⌉") : layer_scope.
