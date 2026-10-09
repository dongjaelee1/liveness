# `lantana_heap_lang/examples/`

The paper's case studies: libraries (flag, handoff, ticket lock, queue, task queue) specified in
the fuel-burning logic, and closed client programs whose adequacy theorems give liveness and
safety for every fair execution. The proofs use the Iris proof mode, and ghost state from Iris
and Transfinite Iris.

Builds on `lantana/algebra/`, `lantana/base_logic/`, `lantana/program_logic/`, `lantana_heap_lang/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `flag.v` | — | The flag module (`init`/`set`/`wait`): `is_flag` (isFlag), `flag_tk` (FlagObl), and SPEC-INIT/SPEC-SET/SPEC-WAIT (`Flag_init_fbspec`, `Flag_set_fbspec`, `Flag_wait_fbspec`). `wait` is proved by witness induction. |
| `flag_client.v` | `flag.v` | A client not in the paper: a writer sets a flag at a fixed location and a reader waits on it. Closed specifications `writer_fbspec` and `reader_fbspec`; the adequacy theorems state a property of the location, beyond termination. |
| `flag_fork.v` | `flag.v` | The paper's first example `main`: allocate a flag, fork a thread that sets it, and wait. `FlagFork_main_fbspec` is proved with the rules of `triple.v` and the flag specifications only, following the paper's walkthrough (with small derived rules and the tactics `fb_pure` and `fb_call`). |
| `handoff.v` | — | The handoff buffer (`send`/`receive`): the task predicate `is_task` (TaskSpec), the invariant `handoff_inv` (HandoffBuf), `is_handoff` (HInv), and SPEC-SEND/SPEC-RECEIVE (`Handoff_send_fbspec`, `Handoff_receive_fbspec`). |
| `handoff_client.v` | `flag.v`, `handoff.v` | `main` (handoffMain): hand the task `Flag.set x` to a forked receiver, and wait on the flag. SPEC-HANDOFF-MAIN (`main_fbspec`) and the adequacy theorems. |
| `nondet.v` | `flag.v` | `nest` and `nondet`: a chain of `n` nested threads, each waiting on a flag that the next one sets, with `n` chosen nondeterministically. SPEC-NEST and SPEC-NONDET (`Nondet_nest_fbspec`, `Nondet_nondet_fbspec`); `nondet` needs fuel at layer ω. |
| `paradox.v` | — | Why pure steps must burn fuel: with a fuel-free pure-step rule (class `lantanaGS_no_lc`), two looping threads get a specification whose adequacy gives "eventually False" (`loop_paradox`); a fair run of the loops then yields `False` (`no_lc_absurd`). |
| `ticket_lock.v` | — | A fair ticket lock (`init`/`acquire`/`release`/`delete`): `is_fair_lock` and the alive and configuration (layer) tokens `↪LOCK_AL`/`↪LOCK_CF` (TLInv is `is_fair_lock` with both tokens made persistent), `lock_token` (TLObl), and SPEC-ACQUIRE/SPEC-RELEASE (`TicketLock_acquire_fbspec`, `TicketLock_release_fbspec`). The waiting loop is proved by induction on the threads ahead and on witnesses. |
| `queue.v` | `ticket_lock.v` | A lock-based linked-list queue whose elements carry obligations, which pass to the thread that dequeues them: `is_queue` (QInv), `queue_worker` (QPrimary), and SPEC-ENQUEUE/SPEC-DEQUEUE (`Queue_enqueue_fbspec`, `Queue_dequeue_fbspec`). |
| `task_queue.v` | `handoff.v`, `queue.v` | A task queue with one worker thread that runs the queued tasks forever: `is_task_queue` (TQInv), and SPEC-PUT-TASK/SPEC-WORKER (`TaskQueue_put_task_fbspec`, `TaskQueue_worker_fbspec`), with `run_task` and `init`. |
| `task_queue_client.v` | `flag.v`, `task_queue.v` | The reentrant client: `decr_reentrant` (decr) puts itself back on the task queue `n` times, then sets a flag, which `main` (clientMain) waits on. SPEC-DECR and SPEC-DECR-CLIENTMAIN (`decr_reentrant_fbspec`, `main_fbspec`), and the adequacy theorems. |
| `assumptions.v` | `flag.v`, `flag_client.v`, `flag_fork.v`, `handoff.v`, `handoff_client.v`, `nondet.v`, `paradox.v`, `queue.v`, `task_queue.v`, `task_queue_client.v`, `ticket_lock.v` | `Print Assumptions` for the main results: the adequacy theorems, the client theorems, `no_lc_absurd`, and (as two groups) the rules of `triple.v` and the case-study specifications. Building it prints their axioms. |

## Notes

- Each module has texan specifications `*_spec` and, as corollaries, specifications in the
  paper's format `*_fbspec`. The clients' closed specifications go the other way: `*_fbspec`
  is proved first, and the texan form follows from it. Each client has `*_adequacy`
  (liveness, from the adequacy theorem), `*_safety_adequacy` (safety) and `*_liveness_safety`
  (both at once).
- The top-level README's "Case studies" table maps the paper's names to these files.
- `queue.v` cites as references the queue of Iron and the event-loop example of Transfinite
  Iris.
