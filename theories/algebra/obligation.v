From iris.proofmode Require Import proofmode.
From liveness Require Export wfOrderedCM.

(* FIXME : Move to somewhere else *)
Lemma sn_tc {X} (R : X → X → Prop) (x : X): sn R x ↔ sn (tc R) x.
Proof.
  split.
  - induction 1 as [x _ IH]; constructor; simpl; intros y Hy; revert IH; simpl.
    destruct Hy as [x y Honce|x y z Honce Hsteps]; intros IH; eauto.
    destruct (IH _ Honce) as [Hy]; eauto.
  - induction 1 as [z _ IH]; constructor; intros ??; apply IH; simpl in *; eauto using tc_once.
Qed.


(* Program state. *)
Class obl_ps : Type := {Π : Type}.

Notation obl_ps_prop := (Π → Prop).

Global Instance obl_ps_prop_iff `{obl_ps} : Equiv obl_ps_prop :=
  λ P1 P2, ∀ (s : Π), (P1 s) ↔ (P2 s).

Global Instance obl_ps_prop_iff_equivalence `{obl_ps} : Equivalence (@equiv _ obl_ps_prop_iff).
Proof. firstorder. Qed.

Canonical Structure obl_ps_propO `{SI : indexT} `{obl_ps} := leibnizO obl_ps_prop.


Inductive obl_state `{WFOrderedCM.t A leR addO ltR} `{obl_ps} : Type :=
| obl_init (a : A) | obl_live (a : A) | obl_done (P : Π → Prop).

Definition obl_state_step `{WFOrderedCM.t A leR addO ltR} `{obl_ps} (s : Π) : relation obl_state :=
  λ o1 o2,
    match o1, o2 with
    | obl_init a1, obl_init a2 => a1 = a2
    | obl_live a1, obl_live a2 => ltR a2 a1
    | obl_done P1, obl_done P2 => P1 ≡ P2
    | obl_init a1, obl_live a2 => a1 = a2
    | obl_live a, obl_done P => P s
    | _, _ => False
    end.

Definition obl_id := positive.
Canonical Structure obl_idO `{SI : indexT} := leibnizO obl_id.

Notation obl_ids := (gset obl_id).
Notation obl_states := (gmap obl_id obl_state).

Definition obl_states_step' `{WFOrderedCM.t A leR addO ltR} `{obl_ps} (s : Π) (K : obl_ids) : relation obl_states :=
  λ os1 os2, map_Forall2 (λ k o1 o2, k ∈ K → obl_state_step s o1 o2) os1 os2.

Variant obl_states_step `{WFOrderedCM.t A leR addO ltR} `{obl_ps} (s : Π) (K : obl_ids) : relation obl_states :=
  | obl_states_step_alloc os1 os2 i a :
    os1 !! i = None →
    os2 = <[i:=obl_init a]> os1 →
    obl_states_step s K os1 os2
  | obl_states_step_step os1 os2 :
    obl_states_step' s K os1 os2 →
    obl_states_step s K os1 os2.

Notation "'[[' a ↪ b ':' s ',' K ']]'" := (obl_states_step s K a b) (at level 60, format "[[ a  ↪  b  :  s ,  K ]]").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "'[[' a ↪⁺ b ':' s ',' K ']]'" := ((tc (obl_states_step s K)) a b) (at level 60, format "[[ a  ↪⁺  b  :  s ,  K ]]").
Notation "'[[' a ↪⋆ b ':' s ',' K ']]'" := ((rtc (obl_states_step s K)) a b) (at level 60, format "[[ a  ↪⋆  b  :  s ,  K ]]").

(* test. *)
(* Global Instance obl_ps_nat : obl_ps := {Π := prod nat nat}. *)
(* Print Instances obl_ps. *)
(* Definition obl_state_test `{WFOrderedCM.t A leR addO ltR} (s : prod nat nat) o1 o2 := obl_state_step s o1 o2. *)
