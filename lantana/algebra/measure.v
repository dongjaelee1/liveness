From stdpp Require Import base.
From lantana.prelude Require Import axioms.
From lantana.prelude Require Export wf_structs ordinal_facts.

Class layer_class (L : Type) := {
    ltL : L -> L -> Prop;
    wf_ltL : well_founded ltL;
    #[global] ltL_transitive :: Transitive ltL;
    eqL : L → L → Prop;
    #[global] eqL_equivalence :: Equivalence eqL;
    #[global] lt_eq_proper_L :: Proper (eqL ==> eqL ==> iff) ltL;
  }.

Section measure_rep.
  Context `{!layer_class L} `{!ord_mono_fun_class}.

  (** Syntax that captures a useful subset of Ordinal. *)
  Inductive measure  : Type :=
  (* Any well-founded ordering of type A can be embedded as long as the universe is consistent. *)
  | ms_embed {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (a : A)
  | ms_large
  | ms_add (s1 s2 : measure)
  | ms_mult (s1 s2 : measure)
  | ms_expn (s1 s2 : measure)
  | ms_extend.

  (** Interpretation into [Ord.t]. *)
  Definition L_sub (u : L) : Type := sig (λ v, ltL v u).
  Remark measure_rep_rec_oblig : ∀ (l : L) (m : L_sub l), ltL (proj1_sig m) l.
  Proof using. intros. destruct m. auto. Qed.

  Fixpoint measure_rep_rec (l : L) (ACC : Acc ltL l) {struct ACC} :
    ∀ (s : measure), Ord.t :=
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
                         Ord.join (λ (t : measure),
                                     measure_rep_rec
                                       (proj1_sig m) (Acc_inv ACC (measure_rep_rec_oblig l m))
                                       t))))
     end).

  Definition measure_rep (l : L) (s : measure) : Ord.t :=
    measure_rep_rec l (wf_ltL l) s.

  Lemma measure_rep_rec_proof_irrelevance l ACC1 ACC2 s :
    measure_rep_rec l ACC1 s = measure_rep_rec l ACC2 s.
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

  Lemma measure_rep_unfold l s :
    measure_rep l s =
    match s with
    | ms_embed wf_ltA a =>
        Ord.from_wf wf_ltA a
    | ms_large =>
        Ord.large
    | ms_add s1 s2 =>
        (measure_rep l s1 ⊕ measure_rep l s2)%ord
    | ms_mult s1 s2 =>
        (measure_rep l s1 × measure_rep l s2)%ord
    | ms_expn s1 s2 =>
        (measure_rep l s1 ↑ measure_rep l s2)%ord
    | ms_extend =>
        (η (Ord.join (λ (m : L_sub l),
                        Ord.join (λ (t : measure),
                                    measure_rep (proj1_sig m) t))))
    end.
  Proof using Type*.
    unfold measure_rep. destruct (wf_ltL l). destruct s; simpl; auto.
    do 2 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
    apply measure_rep_rec_proof_irrelevance.
  Qed.

  (** Reduction rules *)
  Lemma measure_rep_embed {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (l : L) (a : A) :
    measure_rep l (ms_embed wf_ltA a) = Ord.from_wf wf_ltA a.
  Proof using Type*.
    rewrite (measure_rep_unfold _ (ms_embed _ _)). auto.
  Qed.

  Lemma measure_rep_large (l : L) :
    measure_rep l (ms_large) = Ord.large.
  Proof using Type*.
    rewrite (measure_rep_unfold _ (ms_large)). auto.
  Qed.

  Lemma measure_rep_add (l : L) s1 s2 :
    measure_rep l (ms_add s1 s2) = (measure_rep l s1 ⊕ measure_rep l s2)%ord.
  Proof using Type*.
    rewrite (measure_rep_unfold _ (ms_add _ _)). auto.
  Qed.

  Lemma measure_rep_mult (l : L) s1 s2 :
    measure_rep l (ms_mult s1 s2) = (measure_rep l s1 × measure_rep l s2)%ord.
  Proof using Type*.
    rewrite (measure_rep_unfold _ (ms_mult _ _)). auto.
  Qed.

  Lemma measure_rep_expn (l : L) s1 s2 :
    measure_rep l (ms_expn s1 s2) = (measure_rep l s1 ↑ measure_rep l s2)%ord.
  Proof using Type*.
    rewrite (measure_rep_unfold _ (ms_expn _ _)). auto.
  Qed.

  Lemma measure_rep_extend (l1 l2 : L) :
    ltL l1 l2 →
    ∀ (t : measure), (η (measure_rep l1 t) <= measure_rep l2 (ms_extend))%ord.
  Proof using Type*.
    intros Hlt d. rewrite (measure_rep_unfold _ (ms_extend)).
    apply η_le_proper.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. apply Ord.join_upperbound.
  Qed.

  (** Properties *)
  Lemma measure_rep_embed_lt {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) l (a1 a2 : A) :
    ltA a1 a2 →
    (measure_rep l (ms_embed wf_ltA a1) < measure_rep l (ms_embed wf_ltA a2))%ord.
  Proof using.
    intros. rewrite !measure_rep_embed. apply Ord.lt_from_wf. auto.
  Qed.

  Lemma measure_rep_large_lt {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) l a :
    (measure_rep l (ms_embed wf_ltA a) < measure_rep l ms_large)%ord.
  Proof using.
    rewrite measure_rep_embed, measure_rep_large. apply Ord.large_lt_from_wf.
  Qed.

  Lemma measure_rep_extend_alt (l1 l2 : L) (o : Ord.t) :
    ltL l1 l2 →
    (∃ (t : measure), (o <= η (measure_rep l1 t))%ord) →
    (o <= measure_rep l2 (ms_extend))%ord.
  Proof using Type*.
    intros Hlt (t& ?). etransitivity; last eapply (measure_rep_extend l1 l2); eauto.
  Qed.

  Lemma measure_rep_layer_eq (l1 l2 : L) m :
    eqL l1 l2 →
    (measure_rep l1 m == measure_rep l2 m)%ord.
  Proof using Type*.
    induction m; intros Heq.
    - rewrite !measure_rep_embed. reflexivity.
    - rewrite !measure_rep_large. reflexivity.
    - rewrite !measure_rep_add. rewrite IHm1; auto. rewrite IHm2; auto. reflexivity.
    - rewrite !measure_rep_mult. rewrite IHm1; auto. rewrite IHm2; auto. reflexivity.
    - rewrite !measure_rep_expn. rewrite IHm1; auto. rewrite IHm2; auto. reflexivity.
    - rewrite !measure_rep_unfold. split.
      + apply η_le_proper. apply Ord.le_join.
        intros (a& HLa1). assert (HLa2 : ltL a l2).
        { eapply lt_eq_proper_L. 3: eapply HLa1. 1: reflexivity. symmetry. auto. }
        exists (exist _ a HLa2). simpl. reflexivity.
      + apply η_le_proper. apply Ord.le_join.
        intros (a& HLa2). assert (HLa1 : ltL a l1).
        { eapply lt_eq_proper_L. 3: eapply HLa2. 1: reflexivity. auto. }
        exists (exist _ a HLa1). simpl. reflexivity.
  Qed.

  Global Instance measure_rep_layer_le_proper μ : Proper ((λ ℓ1 ℓ2, eqL ℓ1 ℓ2 ∨ ltL ℓ1 ℓ2) ==> Ord.le) (λ ℓ, measure_rep ℓ μ).
  Proof using.
    induction μ; repeat intro.
    - rewrite !measure_rep_embed. reflexivity.
    - rewrite !measure_rep_large. reflexivity.
    - rewrite !measure_rep_add. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_rep_mult. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_rep_expn. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - destruct H0.
      + rewrite measure_rep_layer_eq; first reflexivity. auto.
      + etransitivity; last (eapply measure_rep_extend; eauto).
        eapply η_mono.
  Qed.

  (** Useful instances. *)
  Definition ms_nat (n : nat) : measure :=
    ms_embed PeanoNat.Nat.lt_wf_0 n.

  Lemma measure_rep_nat (l : L) n :
    (measure_rep l (ms_nat n) == n)%ord.
  Proof using Type*.
    unfold ms_nat. rewrite (measure_rep_unfold _ (ms_embed _ _)).
    symmetry. apply Ord.from_nat_from_peano_lt.
  Qed.

  Lemma measure_rep_nat_add l n1 n2 :
    (measure_rep l (ms_nat (n1 + n2)) == (measure_rep l (ms_nat n1) ⊕ measure_rep l (ms_nat n2)))%ord.
  Proof using.
    rewrite !measure_rep_nat. apply Hessenberg.add_from_nat.
  Qed.

  Lemma measure_rep_nat_S (l : L) (n : nat) :
    (measure_rep l (ms_nat (S n)) == (measure_rep l (ms_nat 1) ⊕ measure_rep l (ms_nat n)))%ord.
  Proof using.
    rewrite <-measure_rep_nat_add. reflexivity.
  Qed.

  (** Top element *)
  Definition measure_rep_top (l : L) : Ord.t :=
    Ord.join (λ (μ : measure), measure_rep l μ).

  Lemma measure_rep_top_upperbound l μ :
    (measure_rep l μ <= measure_rep_top l)%ord.
  Proof using. apply Ord.join_upperbound. Qed.

  Lemma measure_rep_top_lt_extend l1 l2 :
    ltL l1 l2 →
    (η (measure_rep_top l1) <= measure_rep l2 (ms_extend))%ord.
  Proof using.
    intros Hlt. rewrite (measure_rep_unfold _ (ms_extend)).
    apply η_le_proper.
    etransitivity; cycle 1.
    { eapply (Ord.join_upperbound _ (exist _ l1 Hlt)). }
    simpl. reflexivity.
  Qed.

  Lemma measure_rep_top_lt l1 l2 :
    ltL l1 l2 →
    (η (measure_rep_top l1) <= measure_rep_top l2)%ord.
  Proof using.
    intros Hlt. etransitivity; first eapply measure_rep_top_lt_extend; eauto.
    apply measure_rep_top_upperbound.
  Qed.

End measure_rep.
Global Opaque measure_rep_rec measure_rep ms_nat.

Declare Scope msyn_scope.
Delimit Scope msyn_scope with M.

Coercion ms_nat : nat >-> measure.
Notation "'⟪' R , a '⟫'" := (ms_embed R a) (at level 50, format "⟪ R ,  a ⟫") : msyn_scope.
Notation "'ℵ'" := (ms_large) : msyn_scope.
Infix "⊕" := ms_add : msyn_scope.
Infix "×" := ms_mult : msyn_scope.
Infix "↑" := ms_expn : msyn_scope.
Notation "▽" := (ms_extend) : msyn_scope.

(** Additional definitions and properties. *)

Class Layerless `{!layer_class L} `{!ord_mono_fun_class} (μ : measure) : Prop :=
  layerless: ∀ (ℓ1 ℓ2 : L), (measure_rep ℓ1 μ == measure_rep ℓ2 μ)%ord.

Section layerless.
  Context `{!layer_class L} `{!ord_mono_fun_class}.

  Global Instance ms_embed_layerless {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) (a : A) :
    Layerless (ms_embed wf_ltA a).
  Proof using. intros ℓ1 ℓ2. rewrite !measure_rep_embed. reflexivity. Qed.

  Global Instance ms_large_layerless : Layerless (ms_large).
  Proof using. intros ℓ1 ℓ2. rewrite !measure_rep_large. reflexivity. Qed.

  Global Instance ma_add_layerless s1 s2 :
    Layerless s1 → Layerless s2 → Layerless (ms_add s1 s2).
  Proof using.
    intros HL1 HL2 ℓ1 ℓ2. rewrite !measure_rep_add. rewrite (HL1 ℓ1 ℓ2), (HL2 ℓ1 ℓ2). reflexivity.
  Qed.

  Global Instance ma_mult_layerless s1 s2 :
    Layerless s1 → Layerless s2 → Layerless (ms_mult s1 s2).
  Proof using.
    intros HL1 HL2 ℓ1 ℓ2. rewrite !measure_rep_mult. rewrite (HL1 ℓ1 ℓ2), (HL2 ℓ1 ℓ2). reflexivity.
  Qed.

  Global Instance ma_expn_layerless s1 s2 :
    Layerless s1 → Layerless s2 → Layerless (ms_expn s1 s2).
  Proof using.
    intros HL1 HL2 ℓ1 ℓ2. rewrite !measure_rep_expn. rewrite (HL1 ℓ1 ℓ2), (HL2 ℓ1 ℓ2). reflexivity.
  Qed.

End layerless.

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

  Global Instance measure_rep_layer_leibniz_le_proper μ : Proper (layer_leibniz_le ==> Ord.le) (λ ℓ, measure_rep ℓ μ).
  Proof using.
    induction μ; repeat intro.
    - rewrite !measure_rep_embed. reflexivity.
    - rewrite !measure_rep_large. reflexivity.
    - rewrite !measure_rep_add. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_rep_mult. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - rewrite !measure_rep_expn. rewrite IHμ1, IHμ2; eauto. reflexivity.
    - destruct H0.
      + subst. reflexivity.
      + etransitivity; last (eapply measure_rep_extend; eauto).
        eapply η_mono.
  Qed.

End layer.
