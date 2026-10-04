(** Notations for the liveness weakest precondition: the class [Lwp] and the [lWP] and
    texan-triple notations (as Iris' [bi/weakestpre.v], with a thread id). *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.

(** [lWP e @ s; i; E {{ Φ }}] is [lwp s i E e Φ] for thread [i] of type [B]; as in Iris, [s]
    has an arbitrary type [A]. The notations without [s] fix [A] to [stuckness]: [s] is
    [NotStuck] for [lWP e @ i; E {{ Φ }}] and [MaybeStuck] for [lWP e @ i; E ?{{ Φ }}]. *)
Class Lwp (PROP EXPR VAL A B : Type) :=
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
to switch between "horizontal mode" where it all fits on one line, and "vertical
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
