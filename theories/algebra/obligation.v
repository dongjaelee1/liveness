From iris.proofmode Require Import proofmode.

Definition prop_of (T : Type) := (T → Prop).

Global Instance prop_of_iff (T : Type) : Equiv (prop_of T) :=
  λ P1 P2, ∀ (s : T), (P1 s) ↔ (P2 s).

Global Instance prop_of_iff_equivalence T : Equivalence (@equiv _ (prop_of_iff T)).
Proof. firstorder. Qed.

Canonical Structure prop_ofO `{SI : indexT} (T : Type) := leibnizO (prop_of T).


(* FIXME : Move to somewhere else *)
Lemma sn_tc {X} (R : X → X → Prop) (x : X): sn R x ↔ sn (tc R) x.
Proof.
  split.
  - induction 1 as [x _ IH]; constructor; simpl; intros y Hy; revert IH; simpl.
    destruct Hy as [x y Honce|x y z Honce Hsteps]; intros IH; eauto.
    destruct (IH _ Honce) as [Hy]; eauto.
  - induction 1 as [z _ IH]; constructor; intros ??; apply IH; simpl in *; eauto using tc_once.
Qed.

Class obl_class (obl_ps : Type) (obl_count : Type) := {
    obl_count_ltR : obl_count → obl_count → Prop;
    obl_count_ltR_wf : well_founded obl_count_ltR;
  }.

Inductive obl_state `{Δ : obl_class} : Type :=
| obl_init (a : obl_count) | obl_live (a : obl_count) | obl_done (P : prop_of obl_ps).

Definition obl_state_step `{Δ : obl_class} (s : obl_ps) : relation obl_state :=
  λ o1 o2,
    match o1, o2 with
    | obl_init a1, obl_init a2 => a1 = a2
    | obl_live a1, obl_live a2 => obl_count_ltR a2 a1
    | obl_done P1, obl_done P2 => P1 ≡ P2
    | obl_init a1, obl_live a2 => a1 = a2
    | obl_live a, obl_done P => P s
    | _, _ => False
    end.

Definition obl_id := positive.
Canonical Structure obl_idO `{SI : indexT} := leibnizO obl_id.

Notation obl_ids := (gset obl_id).
Notation obl_states := (gmap obl_id obl_state).
Notation obl_states' Δ := (gmap obl_id (obl_state (Δ:=Δ))).

Definition obl_states_step_one `{Δ : obl_class} (s : obl_ps) (x : obl_id) : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ k o1 o2, if decide (k = x) then obl_state_step s o1 o2 else o1 = o2) Ω1 Ω2.

Notation "a ↪ₒ b @ s , x" := (obl_states_step_one s x a b) (at level 20, format "a  ↪ₒ  b  @  s ,  x ").
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Notation "a ↪ₒ⁺ b @ s , x" := (tc (obl_states_step_one s x) a b) (at level 20, format "a  ↪ₒ⁺  b  @  s ,  x ").
Notation "a ↪ₒ⋆ b @ s , x" := (rtc (obl_states_step_one s x) a b) (at level 20, format "a  ↪ₒ⋆  b  @  s ,  x ").

Definition obl_states_progress `{Δ : obl_class} (s : obl_ps) : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ _ o1 o2, obl_state_step s o1 o2) Ω1 Ω2.

Notation "a ↪ₚ b @ s" := (obl_states_progress s a b) (at level 20, format "a  ↪ₚ  b  @  s ").
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Notation "a ↪ₚ⁺ b @ s" := (tc (obl_states_progress s) a b) (at level 20, format "a  ↪ₚ⁺  b  @  s").
Notation "a ↪ₚ⋆ b @ s" := (rtc (obl_states_progress s) a b) (at level 20, format "a  ↪ₚ⋆  b  @  s").

Definition obl_states_alloc `{Δ : obl_class} : relation obl_states :=
  λ Ω1 Ω2, ∃ i a, Ω1 !! i = None ∧ Ω2 = <[i:=obl_init a]> Ω1.

Infix "↪ₐ" := (obl_states_alloc) (at level 20).
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Infix "↪ₐ⁺" := (tc obl_states_alloc) (at level 20).
Infix "↪ₐ⋆" := (rtc obl_states_alloc) (at level 20).

Variant obl_states_step `{Δ : obl_class} (s : obl_ps) : relation obl_states :=
  | obl_states_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → obl_states_step s Ω1 Ω2
  | obl_states_step_step_one x Ω1 Ω2 :
    Ω1 ↪ₒ Ω2 @ s, x → obl_states_step s Ω1 Ω2
  | obl_states_step_progress Ω1 Ω2 :
    Ω1 ↪ₚ Ω2 @ s → obl_states_step s Ω1 Ω2.

Notation "a ↪ₛ b @ s" := (obl_states_step s a b) (at level 20, format "a  ↪ₛ  b  @  s").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "a ↪ₛ⁺ b @ s" := ((tc (obl_states_step s)) a b) (at level 20, format "a  ↪ₛ⁺  b  @  s").
Notation "a ↪ₛ⋆ b @ s" := ((rtc (obl_states_step s)) a b) (at level 20, format "a  ↪ₛ⋆  b  @  s").
