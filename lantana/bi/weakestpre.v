(** The interface and notations for Lantana's weakest preconditions [lWP] and
    Hoare triples. Adapted from Iris's [iris/bi/weakestpre.v]. *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

(** [lWP e @ s ; i ; E {{ Φ }}]: the weakest precondition of [e], executed by thread [i],
with mask [E] and postcondition [Φ]. As in Iris, [s] has a type [A] chosen by the
instance; in Lantana it is a stuckness bit. The notations without [s] require [A]
to be [stuckness]: they set [s] to [NotStuck], or to [MaybeStuck] for the [?]
variants. *)
Class Lwp (PROP EXPR VAL A B : Type) :=
  lwp : A → B → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments lwp {_ _ _ _ _ _} _ _ _ _%_E _%_I.
Global Instance: Params (@lwp) 10 := {}.

(** Notations without binder. They are only for parsing because they overlap with
the notations with binder. *)
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

(** Notations with binder. Each is printed on one line if it fits, and otherwise
with a line break at each ['/']. Nested boxes keep preconditions and
postconditions together and indented. *)
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
