From stdpp Require Import base.
From liris Require Export wfocm.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.
From liris.prelude Require Import axioms.

Section limit.

  Local Open Scope ord.

  Definition limit_fun {A : Type} (f : Ord.t -> A -> Ord.t) : Ord.t -> Ord.t :=
    fun o => Ord.join (f o).

  Lemma limit_fun_upperbound {A : Type} (f : Ord.t -> A -> Ord.t) : forall o a, (f o a) <= (limit_fun f o).
  Proof. intros. apply Ord.join_upperbound. Qed.

  Lemma limit_fun_supremum {A : Type} (f : Ord.t -> A -> Ord.t) : forall o u, (∀ a, f o a <= u) -> (limit_fun f o <= u).
  Proof. intros. eapply Ord.join_supremum. eauto. Qed.

End limit.

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

Global Program Instance ord_OCM : OCM.t Ord.le Hessenberg.add :=
  OCM.Build_t _ _ _ Ord.O _ _ _ _ _ _ _.
Next Obligation.
  repeat intro. eapply ClassicOrd.total_le.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_assoc.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_comm.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_O_l.
Qed.
Next Obligation.
  eapply Hessenberg.add_base_l.
Qed.

Lemma ord_OCM_eq (a0 a1 : Ord.t) : OCM.eq a0 a1 <-> Ord.eq a0 a1.
Proof. auto. Qed.

Global Program Instance ord_wfocm : WFOCM.t Ord.le Hessenberg.add Ord.lt :=
  WFOCM.Build_t _ _ _ _ _ _ _ _.
Next Obligation.
  apply Ord.lt_well_founded.
Qed.
Next Obligation.
  intros a c. split; simpl; intros.
  { destruct H as (b&LT&LE). eapply Ord.lt_le_lt; [|eauto]. apply Hessenberg.add_lt_l. auto. }
  { exists Ord.one. split; [apply Ord.S_lt |].
    unfold Ord.one. rewrite Hessenberg.add_S_r. apply Ord.S_supremum.
    rewrite Hessenberg.add_O_r. auto.
  }
Qed.
Next Obligation.
  exists (Ord.S Ord.O). apply Ord.S_pos.
Qed.

Global Program Instance ord_wfocm_pack : WFOCM.pack Ord.t :=
  WFOCM.Build_pack _ _ _ _ ord_wfocm.


Section ord_facts.

  Import Hessenberg Jacobsthal.

  Lemma omega_lt_one : (Ord.S Ord.O < ω)%ord.
  Proof.
    rewrite <- Ord.from_nat_O. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
  Qed.

  Lemma ord_lt_one (o0 o1 : Ord.t) :
    (o0 < o1)%ord -> ((o0 ⊕ (Ord.S Ord.O)) <= o1)%ord.
  Proof.
    intros H. apply WFOCM.lt_exists_left in H. destruct H as (b&H0&H1).
    etransitivity; [|eauto]. apply Hessenberg.le_add_r.
    apply Ord.S_supremum. auto.
  Qed.

  Lemma Jacobsthal_expn_omega (o : Ord.t) :
    (Ord.S Ord.O < o)%ord -> forall (n : nat), ((o ↑ n) < (o ↑ Ord.omega))%ord.
  Proof.
    intros. apply Jacobsthal.lt_expn_r; [auto|apply Ord.omega_upperbound].
  Qed.

  Lemma Jacobsthal_expn_square (o : Ord.t) :
    (ω <= o)%ord -> forall (n : nat), ((o × n) < (o ↑ 2))%ord.
  Proof.
    intros. assert (Z : (Ord.O < o)%ord).
    { eapply Ord.lt_le_lt; [|eauto]. rewrite <- Ord.from_nat_O. apply Ord.omega_upperbound. }
    rewrite !Ord.from_nat_S, Ord.from_nat_O. rewrite Jacobsthal.expn_S; [|auto].
    rewrite Jacobsthal.expn_1_r; [|auto]. apply Jacobsthal.lt_mult_r; [|auto].
    eapply Ord.lt_le_lt; [|eauto]. apply Ord.omega_upperbound.
  Qed.

  Lemma unit_mult_omega_lt_one (u : Ord.t) :
    (Ord.S Ord.O < ((Ord.S u) × ω))%ord.
  Proof.
    eapply Ord.lt_le_lt; [apply omega_lt_one|].
    etransitivity; [rewrite <-mult_1_l; reflexivity|].
    apply le_mult_l, Ord.le_S, Ord.O_bot.
  Qed.

  Lemma unit_mult_omega_lt_zero (u : Ord.t) :
    (Ord.O < ((Ord.S u) × ω))%ord.
  Proof.
    etransitivity; [|eapply unit_mult_omega_lt_one]. apply Ord.S_lt.
  Qed.

  Lemma unit_mult_omega_le_omega (u : Ord.t) :
    (ω <= ((Ord.S u) × ω))%ord.
  Proof.
    etransitivity. instantiate (1:=((Ord.S Ord.O) × ω)%ord).
    - rewrite mult_1_l. reflexivity.
    - apply le_mult_l. apply Ord.le_S, Ord.O_bot.
  Qed.

  Lemma ord_S_add :
    forall o, (Ord.S o == ((Ord.S Ord.O) ⊕ o))%ord.
  Proof.
    intros. rewrite add_S_l, add_O_l. reflexivity.
  Qed.

  Lemma mult_base_l (o0 o1 : Ord.t) : (Ord.O < o1)%ord -> (o0 <= (o0 × o1))%ord.
  Proof.
    intros. etransitivity.
    2:{ eapply le_mult_r. eapply Ord.S_supremum. eauto. }
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma omega_lt_zero : (Ord.O < ω)%ord.
  Proof. etransitivity; [|eapply omega_lt_one]. apply Ord.S_lt. Qed.

End ord_facts.

Section ord_from_wf_facts.

  Context {A : Type} {R : A -> A -> Prop}.
  Variable WF : well_founded R.

  Lemma ord_from_wf_lt_one (a0 a1 : A) :
    R a0 a1 -> ((Ord.from_wf WF a0 ⊕ (Ord.S Ord.O)) <= Ord.from_wf WF a1)%ord.
  Proof using.
    intros HR. apply ord_lt_one. apply Ord.lt_from_wf. auto.
  Qed.

  Lemma ord_from_wf_set_one (a : A) :
    ((Ord.from_wf WF a ⊕ (Ord.S Ord.O)) <= Ord.from_wf_set WF)%ord.
  Proof using.
    apply ord_lt_one. apply Ord.from_wf_set_upperbound.
  Qed.

End ord_from_wf_facts.

(** Limiting Jacobsthal expn to nat gives useful properties. *)
Fixpoint Jacobsthal_expn_nat (o : Ord.t) (n : nat) : Ord.t :=
  match n with
  | O => Ord.S Ord.O
  | S m => (Jacobsthal_expn_nat o m × o)%ord
  end.

Section Jacobsthal_expn_nat_facts.

  Lemma Jacobsthal_expn_nat_spec o :
    (Ord.O < o)%ord -> forall n, (Jacobsthal_expn_nat o n == (o ↑ n))%ord.
  Proof.
    intros. induction n; intros.
    - simpl. rewrite Ord.from_nat_O, Jacobsthal.expn_O. reflexivity.
    - simpl. rewrite Ord.from_nat_S, Jacobsthal.expn_S; [rewrite IHn; reflexivity | auto].
  Qed.

End Jacobsthal_expn_nat_facts.

(** WFOCM respects some ordinal operations when embedded. *)
Class OrdFromWFOCM `(wfocm : WFOCM.t A leR addO ltR) := {
    ord_from_wfocm_hess_add :
    forall (a1 a2 : A), (Ord.from_wf WFOCM.lt_wf (addO a1 a2) == ((Ord.from_wf WFOCM.lt_wf a1) ⊕ (Ord.from_wf WFOCM.lt_wf a2)))%ord;
    ord_from_wfocm_le :
    forall (a1 a2 : A), leR a1 a2 -> (Ord.from_wf WFOCM.lt_wf a1 <= Ord.from_wf WFOCM.lt_wf a2)%ord;
  }.

Section ord_from_wfocm.
  Context `{wfocm : WFOCM.t A leR addO ltR} {OFW : OrdFromWFOCM wfocm}.

  Lemma ord_from_wfocm_unit_lt (a : A) :
    (ltR OCM.unit a) -> (Ord.O < Ord.from_wf WFOCM.lt_wf a)%ord.
  Proof using.
    intros. apply (Ord.lt_from_wf WFOCM.lt_wf) in H. apply ord_lt_one in H.
    eapply Ord.lt_le_lt; [| eauto]. rewrite Hessenberg.add_comm, <- ord_S_add.
    apply Ord.S_pos.
  Qed.

End ord_from_wfocm.

(* (** Layer structure. (Ord.S u) is the "unit" of the construction. *) *)
(* (* u is instantiated to the upperbound ordinal of the set of scheduler fairness fuel. *) *)
(* (* A inperative-like pseudocode has the following "size": *)
(* one 'line' (Ord.S u), one 'block' = line × ω, one 'loop' = block × ω <= (line × ω) ↑ 2, *)
(* and this is recursively nested: size(pseudocode) <= (line × ω) ↑ ω. *)
(* We also multiply (ω ↑ ω) to get code-size nondeterministic number of  (line × ω) ↑ ω tokens, *)
(* which allow us to write an "obligation structure code". *)
(* Finally, (⊕ u) is to initialize the layer-scheduler fairness connection. *)
(*  *) *)
(* Fixpoint layer (u : Ord.t) (i : nat) : Ord.t := *)
(*   match i with *)
(*   | O => (((((Ord.S u) × ω) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord *)
(*   | S j => ((((layer u j) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord *)
(*   end. *)

(* Notation "'ℓ[' u '](' i ')'" := (layer u i) (format "ℓ[ u ]( i )"). *)

(* Section layer_facts. *)

(*   Import Hessenberg Jacobsthal. *)

(*   Lemma layer_unfold_zero u : ℓ[u](0) = (((((Ord.S u) × ω) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord. *)
(*   Proof using. reflexivity. Qed. *)

(*   Lemma layer_unfold_S u : *)
(*     forall i, ℓ[u](S i) = (((ℓ[u](i) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord. *)
(*   Proof using. auto. Qed. *)

(*   Ltac lt_remove_add_r := eapply Ord.lt_le_lt; [|apply add_base_l]. *)
(*   Ltac lt_remove_mult_r := eapply Ord.lt_le_lt; [|apply mult_base_l; apply expn_pos]. *)
(*   Ltac lt_remove_r := lt_remove_add_r; lt_remove_mult_r. *)

(*   Lemma layer_lt_zero u : *)
(*     forall i, (Ord.O < ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     destruct i. *)
(*     - unfold layer. lt_remove_r. apply Jacobsthal.expn_pos. *)
(*     - rewrite layer_unfold_S. lt_remove_r. apply Jacobsthal.expn_pos. *)
(*   Qed. *)

(*   Lemma layer_lt_one u : *)
(*     forall i, (Ord.S Ord.O < ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     assert (Ord.S Ord.O < ((Ord.S u) × ω))%ord by apply unit_mult_omega_lt_one. *)
(*     assert (OM : (Ord.S Ord.O < ω)%ord) by apply omega_lt_one. *)
(*     induction i. *)
(*     - unfold layer. pose proof H. *)
(*       rewrite <- (@expn_1_r (Ord.S u × ω)%ord) in H. *)
(*       2:{ etransitivity; [|eapply H]. apply Ord.S_lt. } *)
(*       lt_remove_r. etransitivity; [eapply H|]. eapply lt_expn_r; auto. *)
(*     - etransitivity; [eauto|]. rewrite <- (@expn_1_r ℓ[u](i)); [| apply layer_lt_zero]. *)
(*       rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; auto. *)
(*   Qed. *)

(*   Lemma layer_lt_S_nats u : *)
(*     forall (n i : nat), (((ℓ[u](i) ↑ ω) × n) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. rewrite layer_unfold_S. lt_remove_add_r. apply lt_mult_r; [| apply expn_pos]. *)
(*     etransitivity; [|eapply lt_expn_r]. 2,3: apply omega_lt_one. *)
(*     rewrite expn_1_r; [apply Ord.omega_upperbound | apply omega_lt_zero]. *)
(*   Qed. *)

(*   Lemma layer_lt_S_nat u : *)
(*     forall (n i : nat), ((ℓ[u](i) ↑ n) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; [apply layer_lt_one | apply Ord.omega_upperbound]. *)
(*   Qed. *)

(*   Lemma layer_lt_S u : *)
(*     forall i, (ℓ[u](i) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. eapply Ord.le_lt_lt; [|apply (layer_lt_S_nat _ 1)]. *)
(*     rewrite Ord.from_nat_1. unfold Ord.one. rewrite expn_1_r; [reflexivity|]. *)
(*     apply layer_lt_zero. *)
(*   Qed. *)

(*   Lemma layer_le_layer_zero u : *)
(*     forall i, (ℓ[u](0) <= ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     induction i; [reflexivity|]. *)
(*     etransitivity; [eauto|]. apply Ord.lt_le, layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_le_proper u : *)
(*     Proper (le ==> Ord.le) (layer u). *)
(*   Proof using. *)
(*     intros i j LE. induction LE. *)
(*     - reflexivity. *)
(*     - etransitivity; [eauto|]. apply Ord.lt_le. apply layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_lt_proper u : *)
(*     Proper (lt ==> Ord.lt) (layer u). *)
(*   Proof using. *)
(*     intros i j LT. unfold lt in LT. eapply (Ord.lt_le_lt (o1 := ℓ[u](S i))). *)
(*     - apply layer_lt_S. *)
(*     - apply layer_le_proper. auto. *)
(*   Qed. *)

(*   Lemma layer_upperbound u : *)
(*     forall (n i : nat), ((((Ord.S u) × ω) ↑ n) < ℓ[u](i))%ord. *)
(*   Proof. *)
(*     intros n. induction i. *)
(*     - rewrite layer_unfold_zero. lt_remove_r. apply lt_expn_r. *)
(*       + apply unit_mult_omega_lt_one. *)
(*       + apply Ord.omega_upperbound. *)
(*     - etransitivity; [eauto|]. apply layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_upperbound_nat u : *)
(*     forall (n i : nat), (n < ℓ[u](i))%ord. *)
(*   Proof. *)
(*     intros. eapply Ord.le_lt_lt; [|eapply (layer_upperbound _ 1)]. *)
(*     rewrite expn_1_r; [|apply unit_mult_omega_lt_zero]. *)
(*     etransitivity; [eapply Ord.lt_le, Ord.omega_upperbound|]. *)
(*     apply unit_mult_omega_le_omega. *)
(*   Qed. *)

(*   Lemma layer_expn_lt_S_gen u : *)
(*     forall (n m i : nat), (((ℓ[u](i) ↑ n) × m) < (ℓ[u](i) ↑ (S n)))%ord. *)
(*   Proof. *)
(*     intros. rewrite Ord.from_nat_S, expn_S; [| apply layer_lt_zero]. *)
(*     apply lt_mult_r; [| apply expn_pos]. apply layer_upperbound_nat. *)
(*   Qed. *)

(*   Lemma layer_lt_S_gen u : *)
(*     forall (n m i : nat), (((ℓ[u](i) ↑ n) × m) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. etransitivity. instantiate (1:=(ℓ[u](i) ↑ (S n))%ord). *)
(*     - apply layer_expn_lt_S_gen. *)
(*     - rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; [apply layer_lt_one | apply Ord.omega_upperbound]. *)
(*   Qed. *)

(* End layer_facts. *)

(* (* Rank structure. *) *)
(* Definition rank (o : Ord.t) (i : nat) : Ord.t := (o ↑ i)%ord. *)

(* (* TODO: prove facts about rank. *) *)

(* (** Embedding enumeration into ordinal. Deprecated for now. *) *)
(* Class enum_from_nat (A : Type) := enum_f : nat -> A. *)
(* Notation "'en[' n ']'" := (enum_f n) (format "en[ n ]"). *)

(* Class Enum {A : Type} (R : A -> A -> Prop) (f : enum_from_nat A) := { *)
(*     enum_wf : well_founded R; *)
(*     enum_f_proper : Proper (lt ==> R) enum_f; *)
(*   }. *)

(* Definition ord_from_enum `{E : Enum A R} (a : A) : Ord.t := Ord.from_wf enum_wf a. *)
(* Definition ord_from_enum_set `{E : Enum A R} : Ord.t := Ord.from_wf_set enum_wf. *)

(* Notation "'oe[' a ']'" := (ord_from_enum a) (format "oe[ a ]"). *)
(* Notation "'oen[' n ']'" := (ord_from_enum en[n]) (format "oen[ n ]"). *)
(* Notation "'oE'" := ord_from_enum_set. *)

(* Section ord_from_enum_facts. *)

(*   Context `{@Enum A R f}. *)

(*   Lemma ord_from_enum_lt (a0 a1 : A) : *)
(*     R a0 a1 -> (oe[a0] < oe[a1])%ord. *)
(*   Proof using. apply Ord.lt_from_wf. Qed. *)

(*   Lemma ord_from_enum_lt_nat (n0 n1 : nat) : *)
(*     n0 < n1 -> (oen[n0] < oen[n1])%ord. *)
(*   Proof using. *)
(*     intros. apply Ord.lt_from_wf. apply enum_f_proper. auto. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_omega : *)
(*     (ω <= oE)%ord. *)
(*   Proof using. *)
(*     rewrite Ord.omega_from_peano_lt_set. eapply WfRel.from_wf_set_inj. apply enum_f_proper. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_nat : *)
(*     forall (n : nat), (n < oE)%ord. *)
(*   Proof using. *)
(*     intros. eapply Ord.lt_le_lt; [apply Ord.omega_upperbound | apply ord_from_enum_set_omega]. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_zero : *)
(*     (Ord.O < oE)%ord. *)
(*   Proof using. *)
(*     rewrite <- Ord.from_nat_O. apply ord_from_enum_set_nat. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_one : *)
(*     (Ord.S Ord.O < oE)%ord. *)
(*   Proof using. *)
(*     rewrite <- Ord.from_nat_O, <- Ord.from_nat_S. apply ord_from_enum_set_nat. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_square : *)
(*     forall (n : nat), ((oE × n) < (oE ↑ 2))%ord. *)
(*   Proof using. *)
(*     intros. apply Jacobsthal_expn_square. apply ord_from_enum_set_omega. *)
(*   Qed. *)

(* End ord_from_enum_facts. *)
