From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.

From liris.heap_lang.examples Require Import ticket_lock.

Module LockCouplingSet.
  (** https://www.cs.toronto.edu/~azadeh/resources/papers/tada-live.pdf
      Fig 27 and 28

      Each node is a contiguous block of three cells:
        offset 0: lock      (a [TicketLock] value)
        offset 1: value     (NONE for the tail sentinel = +∞, SOME z otherwise)
        offset 2: next      (location of the successor; unused on the tail)

      The set is represented by a pointer to its head sentinel.  The head's
      value is never compared, so we pick an arbitrary placeholder. *)

  Definition lockRef : val := λ: "x", "x" +ₗ #0.
  Definition valRef  : val := λ: "x", "x" +ₗ #1.
  Definition nextRef : val := λ: "x", "x" +ₗ #2.

  (** Order on node values: [NONE] denotes +∞, [SOME z] denotes [z]. *)
  Definition val_lt : val :=
    λ: "a" "b",
      match: "a" with
        NONE => #false
      | SOME "x" =>
          match: "b" with
            NONE => #true
          | SOME "y" => "x" < "y"
          end
      end.

  Definition lockNode : val :=
    λ: "x", TicketLock.acquire !(lockRef "x").

  Definition unlockNode : val :=
    λ: "x", TicketLock.release !(lockRef "x").

  (** Allocate a new node with the given value and next pointer.  The lock
      starts unlocked. *)
  Definition newNode : val :=
    λ: "v" "nxt",
      let: "n" := AllocN #3 #0 in
      lockRef "n" <- TicketLock.init #();;
      valRef  "n" <- "v";;
      nextRef "n" <- "nxt";;
      "n".

  Definition makeSet : val :=
    λ: <>,
      let: "tail" := newNode NONE #() in
      let: "head" := newNode (SOME #0) "tail" in
      "head".

  (** Traverse the list hand-over-hand, starting from a locked [curr], until
      we find a successor [next] with value ≥ v.  Returns the locked pair
      (curr, next) where curr.next = next. *)
  Definition locate : val :=
    λ: "x" "e",
      lockNode "x";;
      Fst ((rec: "loop" "curr" "v" :=
              let: "next" := !(nextRef "curr") in
              lockNode "next";;
              if: val_lt !(valRef "next") (SOME "v") then
                unlockNode "curr";;
                "locate" "next" "v"
              else ("curr", "next")) "x" "e").

  Definition member : val :=
    λ: "head" "v",
      lockNode "head";;
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      let: "r" := ~ (val_lt (SOME "v") !(valRef "next")) in
      unlockNode "curr";;
      unlockNode "next";;
      "r".

  Definition add : val :=
    λ: "head" "v",
      lockNode "head";;
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      let: "r" :=
        if: val_lt (SOME "v") !(valRef "next") then
          let: "n" := newNode (SOME "v") "next" in
          nextRef "curr" <- "n";;
          #true
        else #false in
      unlockNode "curr";;
      unlockNode "next";;
      "r".

  Definition remove : val :=
    λ: "head" "v",
      lockNode "head";;
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      let: "r" :=
        if: val_lt (SOME "v") !(valRef "next") then #false
        else
          nextRef "curr" <- !(nextRef "next");;
          #true in
      unlockNode "curr";;
      unlockNode "next";;
      "r".

End LockCouplingSet.
