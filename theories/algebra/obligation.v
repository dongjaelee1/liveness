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


Notation ps_prop Π := (Π → Prop).

Global Instance ps_prop_iff (Π : Type) : Equiv (ps_prop Π) :=
  λ P1 P2, ∀ (s : Π), (P1 s) ↔ (P2 s).

Global Instance ps_prop_iff_equivalence Π : Equivalence (@equiv _ (ps_prop_iff Π)).
Proof. firstorder. Qed.

Canonical Structure ps_propO `{SI : indexT} Π := leibnizO (ps_prop Π).


Inductive obl_state `{WFOrderedCM.t A leR addO ltR} {Π : Type} : Type :=
| obl_init (a : A) | obl_live (a : A) | obl_done (P : ps_prop Π).

Definition obl_state_step `{WFOrderedCM.t A leR addO ltR} {Π} (s : Π) : relation obl_state :=
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
Notation obl_states' Π := (gmap obl_id (obl_state (Π:=Π))).

Definition obl_states_step_one `{WFOrderedCM.t A leR addO ltR} {Π} (s : Π) (x : obl_id) : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ k o1 o2, if (decide (k = x)) then obl_state_step s o1 o2 else o1 = o2) Ω1 Ω2.

Notation "'<<' a ↪ b '|' x ',' s '>>'" := (obl_states_step_one s x a b) (at level 60, format "<< a  ↪  b  |  x ,  s >>").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "'<<' a ↪⁺ b '|' x ',' s '>>'" := ((tc (obl_states_step_one s x)) a b) (at level 60, format "<< a  ↪⁺  b  |  x ,  s >>").
Notation "'<<' a ↪⋆ b '|' x ',' s '>>'" := ((rtc (obl_states_step_one s x)) a b) (at level 60, format "<< a  ↪⋆  b  |  x ,  s >>").

Inductive obl_states_step_list `{WFOrderedCM.t A leR addO ltR} {Π} (s : Π) : list obl_id → relation obl_states :=
| obl_states_step_list_nil Ω :
  obl_states_step_list s [] Ω Ω
| obl_states_step_list_cons hd tl Ω1 Ω2 Ω3 :
  <<Ω1 ↪ Ω2 | hd, s>> →
  obl_states_step_list s tl Ω2 Ω3 →
  obl_states_step_list s (hd :: tl) Ω1 Ω3.

Notation "'[[' a ↪ b '|' K ',' s ']]'" := (obl_states_step_list s K a b) (at level 60, format "[[ a  ↪  b  |  K ,  s ]]").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "'[[' a ↪⁺ b '|' K ',' s ']]'" := ((tc (obl_states_step_list s K)) a b) (at level 60, format "[[ a  ↪⁺  b  |  K ,  s ]]").
Notation "'[[' a ↪⋆ b '|' K ',' s ']]'" := ((rtc (obl_states_step_list s K)) a b) (at level 60, format "[[ a  ↪⋆  b  |  K ,  s ]]").

Variant obl_states_step `{WFOrderedCM.t A leR addO ltR} {Π} (s : Π) : relation obl_states :=
  | obl_states_step_alloc Ω1 Ω2 i a :
    Ω1 !! i = None →
    Ω2 = <[i:=obl_init a]> Ω1 →
    obl_states_step s Ω1 Ω2
  | obl_states_step_progress os Ω1 Ω2 :
    [[Ω1 ↪ Ω2 | os, s]] →
    obl_states_step s Ω1 Ω2.

Notation "'{{' a ↪ b '|' s '}}'" := (obl_states_step s a b) (at level 60, format "{{ a  ↪  b  |  s }}").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "'{{' a ↪⁺ b '|' s '}}'" := ((tc (obl_states_step s)) a b) (at level 60, format "{{ a  ↪⁺  b  |  s }}").
Notation "'{{' a ↪⋆ b '|' s '}}'" := ((rtc (obl_states_step_list s)) a b) (at level 60, format "{{ a  ↪⋆  b  |  s }}").
