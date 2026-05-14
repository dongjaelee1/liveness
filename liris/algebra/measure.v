From stdpp Require Import base.
From liris.prelude Require Import axioms.
From liris.prelude Require Export wf_structs ordinal_facts.

(** This is only meant to be instantiated only in this file. *)
Class layer_class (L : Type) := {
    ltL : L -> L -> Prop;
    wf_ltL : well_founded ltL;
    #[global] ltL_transitive :: Transitive ltL;
  }.

Section measure.
  Context `{!layer_class L} `{!ord_mono_fun_class}.

  (** Syntax that captures a useful subset of Ordinal. *)
  Inductive measurable_syntax  : Type :=
  (* Any well-founded ordering of type A can be embedded as long as the universe is consistent. *)
  | ms_embed {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (a : A)
  | ms_large
  | ms_add (s1 s2 : measurable_syntax)
  | ms_mult (s1 s2 : measurable_syntax)
  | ms_expn (s1 s2 : measurable_syntax)
  | ms_extend.

  (** Interpretaion into Ordinal. *)
  Definition L_sub (u : L) : Type := sig (λ v, ltL v u).
  Remark measure_rec_oblig : ∀ (l : L) (m : L_sub l), ltL (proj1_sig m) l.
  Proof using. intros. destruct m. auto. Qed.

  Fixpoint measure_rec (l : L) (ACC : Acc ltL l) {struct ACC} :
    ∀ (s : measurable_syntax), Ord.t :=
  (fix go s {struct s} :=
     match s with
     | ms_embed wf_ltA a =>
         Ord.from_wf wf_ltA a
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
                                       (proj1_sig m) (Acc_inv ACC (measure_rec_oblig l m))
                                       t))))
     end).

  Definition measure (l : L) (s : measurable_syntax) : Ord.t :=
    measure_rec l (wf_ltL l) s.

  Lemma measure_rec_proof_irrelevance l ACC1 ACC2 s :
    measure_rec l ACC1 s = measure_rec l ACC2 s.
  Proof using Type*.
    revert ACC1 ACC2 s. induction l as [l IH] using (well_founded_ind wf_ltL).
    intros. induction s.
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

  Lemma measure_extend (l1 l2 : L) :
    ltL l1 l2 →
    ∀ (t : measurable_syntax), (η (measure l1 t) <= measure l2 (ms_extend))%ord.
  Proof using Type*.
    intros Hlt d. rewrite (measure_unfold _ (ms_extend)).
    apply η_le_proper.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. apply Ord.join_upperbound.
  Qed.

  (** Properties *)
  Lemma measure_embed_lt {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) l (a1 a2 : A) :
    ltA a1 a2 →
    (measure l (ms_embed wf_ltA a1) < measure l (ms_embed wf_ltA a2))%ord.
  Proof using.
    intros. rewrite !measure_embed. apply Ord.lt_from_wf. auto.
  Qed.

  Lemma measure_large_lt {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) l a :
    (measure l (ms_embed wf_ltA a) < measure l ms_large)%ord.
  Proof using.
    rewrite measure_embed, measure_large. apply Ord.large_lt_from_wf.
  Qed.

  Lemma measure_extend_alt (l1 l2 : L) (o : Ord.t) :
    ltL l1 l2 →
    (∃ (t : measurable_syntax), (o <= η (measure l1 t))%ord) →
    (o <= measure l2 (ms_extend))%ord.
  Proof using Type*.
    intros Hlt (t& ?). etransitivity; last eapply (measure_extend l1 l2); eauto.
  Qed.

  (** Useful instances. *)
  Definition ms_nat (n : nat) : measurable_syntax :=
    ms_embed PeanoNat.Nat.lt_wf_0 n.

  Lemma measure_nat (l : L) n :
    (measure l (ms_nat n) == n)%ord.
  Proof using Type*.
    unfold ms_nat. rewrite (measure_unfold _ (ms_embed _ _)).
    symmetry. apply Ord.from_nat_from_peano_lt.
  Qed.

  Lemma measure_nat_add l n1 n2 :
    (measure l (ms_nat (n1 + n2)) == (measure l (ms_nat n1) ⊕ measure l (ms_nat n2)))%ord.
  Proof using.
    rewrite !measure_nat. apply Hessenberg.add_from_nat.
  Qed.

  Lemma measure_nat_S (l : L) (n : nat) :
    (measure l (ms_nat (S n)) == (measure l (ms_nat 1) ⊕ measure l (ms_nat n)))%ord.
  Proof using.
    rewrite <-measure_nat_add. reflexivity.
  Qed.

  (** Top element *)
  Definition measure_top (l : L) : Ord.t :=
    Ord.join (λ (μ : measurable_syntax), measure l μ).

  Lemma measure_top_upperbound l μ :
    (measure l μ <= measure_top l)%ord.
  Proof using. apply Ord.join_upperbound. Qed.

  Lemma measure_top_lt_extend l1 l2 :
    ltL l1 l2 →
    (η (measure_top l1) <= measure l2 (ms_extend))%ord.
  Proof using.
    intros Hlt. rewrite (measure_unfold _ (ms_extend)).
    apply η_le_proper.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. reflexivity.
  Qed.

  Lemma measure_top_lt l1 l2 :
    ltL l1 l2 →
    (η (measure_top l1) <= measure_top l2)%ord.
  Proof using.
    intros Hlt. etransitivity; first eapply measure_top_lt_extend; eauto.
    apply measure_top_upperbound.
  Qed.

End measure.
Global Opaque measure_rec measure ms_nat.

Declare Scope msyn_scope.
Delimit Scope msyn_scope with M.

Coercion ms_nat : nat >-> measurable_syntax.
Notation "'⟪' R , a '⟫'" := (ms_embed R a) (at level 50, format "⟪ R ,  a ⟫") : msyn_scope.
Notation "⫚" := (ms_large) : msyn_scope.
Infix "⊕" := ms_add : msyn_scope.
Infix "×" := ms_mult : msyn_scope.
Infix "↑" := ms_expn : msyn_scope.
Notation "▽" := (ms_extend) : msyn_scope.

(** Additional definitions and properties. *)
Section layer.
  Context `{!layer_class L} `{!ord_mono_fun_class}.

  Definition layer_leibniz_le : L → L → Prop :=
    λ l1 l2, l1 = l2 ∨ (ltL l1 l2).

  Global Instance layer_leibniz_le_reflexive : Reflexive layer_leibniz_le.
  Proof using. repeat intro. left. auto. Qed.
  Global Instance layer_leibniz_le_transitive : Transitive layer_leibniz_le.
  Proof using.
    repeat intro. destruct H0, H1; subst.
    - reflexivity.
    - right; auto.
    - right; auto.
    - right. etransitivity; eauto.
  Qed.
  Global Instance layer_leibniz_le_preorder : PreOrder layer_leibniz_le.
  Proof using. econstructor; apply _. Qed.

  Global Instance measure_layer_leibniz_le_proper μ : Proper (layer_leibniz_le ==> Ord.le) (λ ℓ, measure ℓ μ).
  Proof using.
    induction μ; repeat intro.
    - rewrite !measure_embed. reflexivity.
    - rewrite !measure_large. reflexivity.
    - rewrite !measure_add. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_mult. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_expn. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - destruct H0.
      + subst. reflexivity.
      + etransitivity; last (eapply measure_extend; eauto).
        eapply η_mono.
  Qed.

End layer.
