# `lantana_heap_lang/examples/`

The case studies: modules with their specifications (a flag, a handoff cell, ticket locks, a
queue and a task queue), client programs with end-to-end theorems, two refutations of rules that
would be unsound, and a test of the adequacy proof.

Builds on `lantana_heap_lang/` (and `lantana/trace/adequacy_safety.v`, `lantana/base_logic/`,
`lantana/algebra/` directly). Used by no other directory.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `step_tactics.v` | — | Tactics for pure steps shared by the examples: they pay the step with the fuel of the thread's obligations and no witnesses (`post_lwp_lc n` also takes `n` later credits). |
| `flag.v` | `step_tactics.v` | A flag: `set` writes `1` and `wait` spins until it reads `1`. The cell is "`0` until `1`", an until on the flag's obligation, so `wait` terminates. `is_flag` with its guarantee `is_flag_temporal` and trace property `flag_itrProp` (on traces, `is_flag_tr`); `Flag_init_spec`, `Flag_set_spec`, `Flag_wait_spec`, and the variants `Flag_init_thread_spec`, `Flag_set_thread_spec`. |
| `flag_stable.v` | `step_tactics.v` | The flag of `flag.v` with the set value in a nested `alwaysI`: the cell is "`0` until always `1`", so the flag stays set (`flag_itrProp_stays`). The same specifications. |
| `flag_client.v` | `flag.v`, `step_tactics.v` | A writer thread sets the flag and returns `#()`, and a reader thread waits for it and returns `#1` (`writer_spec`, `reader_spec`). `flag_client_adequacy`: the flag is "`0` until `1`" at the cell `X`, and both threads exit with their values. |
| `flag_stable_client.v` | `flag_stable.v`, `step_tactics.v` | `flag_client.v` with the flag of `flag_stable.v`: its adequacy theorem gives "`0` until always `1`". |
| `flag_fork.v` | `flag.v`, `step_tactics.v` | The program `main` of §2: a forked thread sets a flag, and the main thread waits for it and returns `#42` (`FlagFork_main_spec`). `main_adequacy`: the main thread eventually exits with `#42`, and a flag is created. |
| `nondet.v` | `flag.v`, `step_tactics.v` | Nested waits on flags to a nondeterministically chosen depth (§4.3): `Nondet_nest_spec`, `Nondet_nondet_spec`. |
| `handoff.v` | `step_tactics.v` | A handoff cell: `send` puts a task `f a` into the cell, and `receive` waits for a task and runs it; a task comes with the obligations it discharges (`is_handoff`, `is_task`, `Handoff_send_spec`, `Handoff_receive_spec`). On traces, the cell always holds `NONE` or a task (`handoff_tr`). |
| `handoff_client.v` | `flag.v`, `handoff.v`, `step_tactics.v` | `handoffMain` of §5.2: the main thread sends the task `Flag.set x` to a forked receiver and waits on the flag `x` (`main_spec`). `handoff_client_adequacy`: the main thread exits with `#1`, a flag is created, and a handoff cell is created that always holds `NONE` or a task. |
| `handoff_flag_stable_client.v` | `flag_stable.v`, `handoff.v`, `step_tactics.v` | `handoff_client.v` with the flag of `flag_stable.v`. |
| `paradox.v` | — | The unsoundness counterexample of §6.2. The class `lantanaGS_no_lc` assumes, for HeapLang, a rule for one pure step that pays no fuel and still yields witness credits. With it, two looping threads prove "eventually False" (`loop_paradox`), and a fair behavior of the loops refutes the rule (`no_lc_absurd`). |
| `nonstrict_move.v` | — | The class `obl_move_nonstrict` assumes a non-strict `obl_move` (the new parent's layer may equal the payment layer). A loop then moves the old root below a fresh root at layer `0` in every iteration, and adequacy gives "eventually False" (`nonstrict_move_unsound`, `nonstrict_move_absurd`). |
| `ticket_lock.v` | `step_tactics.v` | The ticket lock of §7.1, which can be deleted: the releasing thread allocates the unlock obligation of the next ticket (`is_fair_lock`, `lock_token`, `TicketLock_init_spec`, `TicketLock_acquire_spec`, `TicketLock_release_spec`, `TicketLock_delete_spec`). On traces, a lock that cannot be deleted (`is_fair_lock_alive`) makes release progress (`release_progress`), and release progress gives starvation freedom when `next` never decreases (`release_progress_starvation_free`). |
| `ticket_lock_mono.v` | `step_tactics.v` | The ticket lock of `ticket_lock.v`, whose guarantee also records that `next` never decreases (an invariant per value `next` reaches), so a lock that cannot be deleted is starvation free without hypotheses (`alive_fair_lock_starvation_free`). The same code and specifications. |
| `ticket_lock2.v` | `step_tactics.v` | A starvation-free ticket lock: each ticket comes with an unlock obligation, allocated by its acquiring thread, so every pending ticket is eventually served (`fair_lock_starvation_free`). |
| `ticket_lock2_client.v` | `ticket_lock2.v`, `step_tactics.v` | A client that creates a lock, acquires and releases it, and returns `#42` (`TicketLockClient_main_spec`). `ticket_lock_client_adequacy`: the main thread exits with `#42`, and a lock is created that is starvation free (`client_spec`). |
| `queue.v` | `ticket_lock.v`, `step_tactics.v` | The queue of §7.2, protected by a ticket lock, whose elements carry obligations: while an element is in the queue, its obligations are children of the worker's inbox (`is_queue`, `queue_worker`, `Queue_init_spec`, `Queue_enqueue_spec`, `Queue_dequeue_spec`). |
| `task_queue.v` | `queue.v`, `handoff.v`, `step_tactics.v` | The task queue of §7.3: a queue of tasks `f a`, as in the handoff, run by a forked worker thread (`is_task_queue`, `TaskQueue_init_spec`, `TaskQueue_put_task_spec`, `TaskQueue_run_task_spec`, `TaskQueue_worker_spec`). |
| `task_queue_client.v` | `flag.v`, `task_queue.v`, `step_tactics.v` | The reentrant client of §7.3: a task `decr_reentrant` puts itself back `n` times before setting a flag, which the main thread waits on (`decr_reentrant_spec`, `main_spec`). `task_queue_client_adequacy`: the main thread exits with `#1`, a flag is created, and a task queue is created whose lock makes release progress. |
| `task_queue_flag_stable_client.v` | `flag_stable.v`, `task_queue.v`, `step_tactics.v` | `task_queue_client.v` with the flag of `flag_stable.v`. |
| `cert_discharge.v` | `step_tactics.v` | A test of the adequacy proof: the commitment `◇ (x ↦ #1 ∗ alwaysI Na (y ↦ #7) ∗ ◇ (x ↦ #2))` is discharged in the pre-step model update of `x <- #2`, which destroys `x ↦ #1` (`main_spec`). `cert_discharge_adequacy`: eventually `x` holds `1` while `y` holds `7` from then on and `x` later holds `2`. |
| `extended_int.v` | — | Integers extended with `±∞` as HeapLang values, and the specification of their comparison. Not imported by any file. |

## Notes

- Each client program has three end-to-end theorems, over all fair behaviors from its initial
  configuration: `*_adequacy` (an instance of `lwp_adequacy_temporal`, giving the trace
  property described above), `*_safety_adequacy` (an instance of `lwp_adequacy_safety_iris`:
  the scheduled thread is never stuck, and a returned thread has its return value), and
  `*_liveness_safety` (both). The clients are `flag_fork.v`, `flag_client.v`,
  `handoff_client.v`, `task_queue_client.v`, `ticket_lock2_client.v`, `cert_discharge.v`, and
  the three `*flag_stable_client.v` copies.
- Beyond the paper: `flag_stable.v` and its clients, `ticket_lock_mono.v`, `ticket_lock2.v` and
  its client, `nonstrict_move.v`, and `cert_discharge.v`.
- `lcset_notes.txt` holds design notes for a lock-coupling set example, not formalized.
