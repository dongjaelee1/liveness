(** Shared notation file for WP connectives. *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Global Instance stuckness_le : SqSubsetEq stuckness := stuckness_leb.
Global Instance stuckness_le_po : PreOrder (⊑@{stuckness}).
Proof. split; by repeat intros []. Qed.

(** Weakest preconditions [WP e @ s ; i ; E {{ Φ }}] have an additional argument [s]
of arbitrary type [A], that can be chosen by the one instantiating the [Wp] type
class. This argument can be used for e.g. the stuckness bit (as in Iris) or
thread IDs (as in iGPS).

For the case of stuckness bits, there are two specific notations
[WP e @ i ; E {{ Φ }}] and [WP e @ i ; E ?{{ Φ }}], which forces [A] to be [stuckness],
and [s] to be [NotStuck] or [MaybeStuck].  This will fail to typecheck if [A] is
not [stuckness].  If we ever want to use the notation [WP e @ i ; E {{ Φ }}] with a
different [A], the plan is to generalize the notation to use [Inhabited] instead
to pick a default value depending on [A]. *)
Class Wp (PROP EXPR VAL A B : Type) :=
  wp : A → B → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments wp {_ _ _ _ _ _} _ _ _ _%_E _%_I.
Global Instance: Params (@wp) 10 := {}.

Class Twp (PROP EXPR VAL A B : Type) :=
  twp : A → B → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments twp {_ _ _ _ _ _} _ _ _ _%_E _%_I.
Global Instance: Params (@twp) 10 := {}.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; i ; E {{ Φ } }" := (wp s i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ; E {{ Φ } }" := (wp NotStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ; E ? {{ Φ } }" := (wp MaybeStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i {{ Φ } }" := (wp NotStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ? {{ Φ } }" := (wp MaybeStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
(** The general approach we use for all these complex notations: an outer '[hv'
to switch bwteen "horizontal mode" where it all fits on one line, and "vertical
mode" where each '/' becomes a line break. Then, as appropriate, nested boxes
('['...']') for things like preconditions and postconditions such that they are
maximally horizontal and suitably indented inside the parentheses that surround
them. *)
Notation "'WP' e @ s ; i ; E {{ v , Q } }" := (wp s i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ i ; E {{ v , Q } }" := (wp NotStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' i ;  '/' E  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ i ; E ? {{ v , Q } }" := (wp MaybeStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' i ;  '/' E  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ i {{ v , Q } }" := (wp NotStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  i  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ i ? {{ v , Q } }" := (wp MaybeStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  i  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; i ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; i; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ; E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  i  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  i  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; i ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; i; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ; E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i; E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  i  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ i ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  i  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; i ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; i; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; i ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; i; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ; E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ i ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ i ?{{ Φ }}) : stdpp_scope.

(** Notations for total weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; i ; E [{ Φ } ]" := (twp s i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ; E [{ Φ } ]" := (twp NotStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ; E ? [{ Φ } ]" := (twp MaybeStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i [{ Φ } ]" := (twp NotStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ i ? [{ Φ } ]" := (twp MaybeStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
Notation "'WP' e @ s ; i ; E [{ v , Q } ]" := (twp s i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e @ i ; E [{ v , Q } ]" := (twp NotStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' i ;  '/' E  ']'  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e @ i ; E ? [{ v , Q } ]" := (twp MaybeStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' i ;  '/' E  ']'  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e @ i [{ v , Q } ]" := (twp NotStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  i  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e @ i ? [{ v , Q } ]" := (twp MaybeStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  i  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.

(* Texan triples *)
Notation "'[[{' P } ] ] e @ s ; i ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; i; E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ; E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  i  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  i  '/' ? [[{  '[hv' x  ..  y ,   RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

Notation "'[[{' P } ] ] e @ s ; i ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; i; E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i; E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ; E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i; E ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  i  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ i ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  i  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'[[{' P } ] ] e @ s ; i ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; i; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ; E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i; E ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ i ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ s ; i ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; i; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ; E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i; E ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ i ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ i ?[{ Φ }]) : stdpp_scope.
