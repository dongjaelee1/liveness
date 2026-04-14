From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.

From liris.heap_lang.examples Require Import ticket_lock.

(** Reference: Iron (https://gitlab.mpi-sws.org/iris/iron/-/blob/master/theories/heap_lang/lib/queue.v) *)

(** Use a ticket lock. *)
Definition new_queue : val :=
  λ: <>,
    let: "node" := ref NONE in
    let: "lock" := TicketLock.init #() in
    (ref "node", ref "node", "lock").

Definition enqueue : val :=
  λ: "q" "x",
    let: "lock" := Snd "q" in
    TicketLock.acquire "lock";;
    let: "tptr" := Snd (Fst "q") in
    let: "t" := !"tptr"  in
    let: "newt" := ref NONE in
    "t" <- SOME ("x", "newt");;
    "tptr" <- "newt";;
    TicketLock.release "lock".

Definition dequeue : val :=
  λ: "q",
    let: "lock" := Snd "q" in
    TicketLock.acquire "lock";;
    let: "hptr" := Fst (Fst "q") in
    let: "h" := !"hptr" in
    match: !"h" with
      NONE =>
        (* Empty queue. *)
        TicketLock.release "lock";;
        NONE
    | SOME "node" =>
        let: "newh" := Snd "node" in
        "hptr" <- "newh";;
        Free "h";;
        TicketLock.release "lock";;
        SOME (Fst "node")
    end.


