(** Shared notation file for lWP connectives. *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

(** Weakest preconditions [lWP e @ s ; i ; E {{ Φ }}] have an additional argument [s]
of arbitrary type [A], that can be chosen by the one instantiating the [lWp] type
class. This argument can be used for e.g. the stuckness bit (as in Iris) or
thread IDs (as in iGPS).

For the case of stuckness bits, there are two specific notations
[lWP e @ i ; E {{ Φ }}] and [lWP e @ i ; E ?{{ Φ }}], which forces [A] to be [stuckness],
and [s] to be [NotStuck] or [MaybeStuck].  This will fail to typecheck if [A] is
not [stuckness].  If we ever want to use the notation [lWP e @ i ; E {{ Φ }}] with a
different [A], the plan is to generalize the notation to use [Inhabited] instead
to pick a default value depending on [A]. *)
Class lWp (PROP EXPR VAL A B : Type) :=
  lwp : A → B → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments lwp {_ _ _ _ _ _} _ _ _ _%_E _%_I.
Global Instance: Params (@lwp) 10 := {}.

(** Notations for liveness weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'lWP' e @ s ; i ; E {{ Φ } }" := (lwp s i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'lWP' e @ i ; E {{ Φ } }" := (lwp NotStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'lWP' e @ i ; E ? {{ Φ } }" := (lwp MaybeStuck i E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'lWP' e @ i {{ Φ } }" := (lwp NotStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'lWP' e @ i ? {{ Φ } }" := (lwp MaybeStuck i ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
(** The general approach we use for all these complex notations: an outer '[hv'
to switch bwteen "horizontal mode" where it all fits on one line, and "vertical
mode" where each '/' becomes a line break. Then, as appropriate, nested boxes
('['...']') for things like preconditions and postconditions such that they are
maximally horizontal and suitably indented inside the parentheses that surround
them. *)
Notation "'lWP' e @ s ; i ; E {{ v , Q } }" := (lwp s i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'lWP'  e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'lWP' e @ i ; E {{ v , Q } }" := (lwp NotStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'lWP'  e  '/' @  '[' i ;  '/' E  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'lWP' e @ i ; E ? {{ v , Q } }" := (lwp MaybeStuck i E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'lWP'  e  '/' @  '[' i ;  '/' E  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'lWP' e @ i {{ v , Q } }" := (lwp NotStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'lWP'  e  '/' @  '[' i  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'lWP' e @ i ? {{ v , Q } }" := (lwp MaybeStuck i ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'lWP'  e  '/' @  '[' i  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'l{{{' P } } } e @ s ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ s; i; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ; E l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ; E ? l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ? l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' ? l{{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'l{{{' P } } } e @ s ; i ; E l{{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ s; i; E {{ Φ }})%I
    (at level 20,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ; E l{{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E {{ Φ }})%I
    (at level 20,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ; E ? l{{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i l{{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i {{ Φ }})%I
    (at level 20,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'l{{{' P } } } e @ i ? l{{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i ?{{ Φ }})%I
    (at level 20,
     format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'l{{{' P } } } e @ s ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ s; i; E {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ; E l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ; E ? l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E ?{{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ? l{{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i ?{{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ s ; i ; E l{{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ s; i; E {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ; E l{{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ; E ? l{{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E ?{{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i l{{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i {{ Φ }}) : stdpp_scope.
Notation "'l{{{' P } } } e @ i ? l{{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i ?{{ Φ }}) : stdpp_scope.



(* (** Weakest preconditions [lWP e @ s ; i ; E {{ Φ }}] have an additional argument [s] *)
(* of arbitrary type [A], that can be chosen by the one instantiating the [lWp] type *)
(* class. This argument can be used for e.g. the stuckness bit (as in Iris) or *)
(* thread IDs (as in iGPS). *)

(* For the case of stuckness bits, there are two specific notations *)
(* [lWP e @ i ; E {{ Φ }}] and [lWP e @ i ; E ?{{ Φ }}], which forces [A] to be [stuckness], *)
(* and [s] to be [NotStuck] or [MaybeStuck].  This will fail to typecheck if [A] is *)
(* not [stuckness].  If we ever want to use the notation [lWP e @ i ; E {{ Φ }}] with a *)
(* different [A], the plan is to generalize the notation to use [Inhabited] instead *)
(* to pick a default value depending on [A]. *) *)
(* Class lWp (PROP EXPR VAL A B : Type) := *)
(*   lwp : A → PROP → B → coPset → EXPR → (VAL → PROP) → PROP. *)
(* Global Arguments lwp {_ _ _ _ _ _} _ _ _ _ _%_E _%_I. *)
(* Global Instance: Params (@lwp) 11 := {}. *)

(* (** Notations for liveness weakest preconditions *) *)
(* (** Notations without binder -- only parsing because they overlap with the *)
(* notations with binder. *) *)
(* Notation "'lWP' e @ s ; ς ; i ; E {{ Φ } }" := (lwp s ς i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ; E {{ Φ } }" := (lwp NotStuck ς i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ; E ? {{ Φ } }" := (lwp MaybeStuck ς i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ ς ; i {{ Φ } }" := (lwp NotStuck ς i ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ? {{ Φ } }" := (lwp MaybeStuck ς i ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(* Notation "'lWP' e @ s ; i ; E {{ Φ } }" := (lwp s emp%I i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ i ; E {{ Φ } }" := (lwp NotStuck emp%I i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ i ; E ? {{ Φ } }" := (lwp MaybeStuck emp%I i E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ i {{ Φ } }" := (lwp NotStuck emp%I i ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'lWP' e @ i ? {{ Φ } }" := (lwp MaybeStuck emp%I i ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(** Notations with binder. *)
(** The general approach we use for all these complex notations: an outer '[hv'
to switch bwteen "horizontal mode" where it all fits on one line, and "vertical
mode" where each '/' becomes a line break. Then, as appropriate, nested boxes
('['...']') for things like preconditions and postconditions such that they are
maximally horizontal and suitably indented inside the parentheses that surround
them. *)
(* Notation "'lWP' e @ s ; ς ; i ; E {{ v , Q } }" := (lwp s ς i E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' s ;  '/' ς ;  '/' i ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ; E {{ v , Q } }" := (lwp NotStuck ς i E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ; E ? {{ v , Q } }" := (lwp MaybeStuck ς i E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ ς ; i {{ v , Q } }" := (lwp NotStuck ς i ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' ς ;  '/' i  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ ς ; i ? {{ v , Q } }" := (lwp MaybeStuck ς i ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' ς ;  '/' i  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(* (* Notation "'lWP' e @ s ; i ; E {{ v , Q } }" := (lwp s emp%I i E e%E (λ v, Q)) *) *)
(* (*   (at level 20, e, Q at level 200, *) *)
(* (*    format "'[hv' 'lWP'  e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *) *)
(* Notation "'lWP' e @ i ; E {{ v , Q } }" := (lwp NotStuck emp%I i E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' i ;  '/' E  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ i ; E ? {{ v , Q } }" := (lwp MaybeStuck emp%I i E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' i ;  '/' E  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ i {{ v , Q } }" := (lwp NotStuck emp%I i ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' i  ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)
(* Notation "'lWP' e @ i ? {{ v , Q } }" := (lwp MaybeStuck emp%I i ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[hv' 'lWP'  e  '/' @  '[' i  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(* (* Texan triples *) *)
(* Notation "'l{{{' P } } } e @ s ; ς ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ s; ς; i; E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' ς ;  '/' i ;  '/' E  ']' '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i; E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E ? l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i; E ?{{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' ? l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/' i  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ? l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i ?{{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/'  i  ']'  '/' ? l{{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* (* Notation "'l{{{' P } } } e @ s ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *) *)
(* (*   (□ ∀ Φ, *) *)
(* (*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ s; i; E {{ Φ }})%I *) *)
(* (*     (at level 20, x closed binder, y closed binder, *) *)
(* (*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *) *)
(* Notation "'l{{{' P } } } e @ i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* (* Notation "'l{{{' P } } } e @ i ; E ? l{{{ x .. y , 'RET' pat ; Q } } }" := *) *)
(* (*   (□ ∀ Φ, *) *)
(* (*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i; E ?{{ Φ }})%I *) *)
(* (*     (at level 20, x closed binder, y closed binder, *) *)
(* (*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *) *)
(* Notation "'l{{{' P } } } e @ i l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' l{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ i ? l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ i ?{{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' ? l{{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* Notation "'l{{{' P } } } e @ s ; ς ; i ; E l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ s; ς; i; E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' ς ;  '/' i ;  '/' E  ']' '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i; E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E ? l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i; E ?{{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/' i ;  '/' E  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/'  i  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ? l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i ?{{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ς ;  '/'  i  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* (* Notation "'l{{{' P } } } e @ s ; i ; E l{{{ 'RET' pat ; Q } } }" := *) *)
(* (*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ s; i; E {{ Φ }})%I *) *)
(* (*     (at level 20, *) *)
(* (*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' i ;  '/' E  ']' '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *) *)
(* (* Notation "'l{{{' P } } } e @ i ; E l{{{ 'RET' pat ; Q } } }" := *) *)
(* (*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E {{ Φ }})%I *) *)
(* (*     (at level 20, *) *)
(* (*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *) *)
(* (* Notation "'l{{{' P } } } e @ i ; E ? l{{{ 'RET' pat ; Q } } }" := *) *)
(* (*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i; E ?{{ Φ }})%I *) *)
(* (*     (at level 20, *) *)
(* (*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i ;  '/' E  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *) *)
(* Notation "'l{{{' P } } } e @ i l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'l{{{' P } } } e @ i ? l{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ i ?{{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' l{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' i  ']'  '/' ? l{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* (** Aliases for stdpp scope -- they inherit the levels and format from above. *) *)
(* Notation "'l{{{' P } } } e @ s ; ς ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ s; ς; i; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E ? l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i; E ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ? l{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ lWP e @ ς; i ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ s ; ς ; i ; E l{{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ s; ς; i; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E l{{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ; E ? l{{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i; E ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i l{{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i {{ Φ }}) : stdpp_scope. *)
(* Notation "'l{{{' P } } } e @ ς ; i ? l{{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ lWP e @ ς; i ?{{ Φ }}) : stdpp_scope. *)
