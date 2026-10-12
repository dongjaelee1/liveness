(** Notations for the liveness weakest precondition: the class [Lwp] and the [lWP] and
    texan-triple notations, with a thread id. Adapted from Iris's [iris.bi.weakestpre]. *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.

(** [lWP e @ s; i; E {{ Φ }}] is [lwp s i E e Φ] for thread [i]; as in Iris, [s] has any
    type. Without [s]: [NotStuck] for [{{ Φ }}], [MaybeStuck] for [?{{ Φ }}]. *)
Class Lwp (PROP EXPR VAL A B : Type) :=
  lwp : A → B → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments lwp {_ _ _ _ _ _} _ _ _ _%_E _%_I.
Global Instance: Params (@lwp) 10 := {}.

(** Notations without binder: only parsing, as they overlap with those with binder. *)
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
(** Formats: an outer '[hv' box (one line if it fits, else a break at each '/'), and nested
    boxes for pre- and postconditions. *)
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

(** Aliases in stdpp scope, with the levels and formats from above. *)
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
