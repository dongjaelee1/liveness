(** The axioms the main results assume.

    Building this file prints the axioms of each result below. Each assumes at most these seven,
    all from Rocq's standard library: [Classical_Prop.classic], [Epsilon.epsilon_statement],
    [FunctionalExtensionality.functional_extensionality_dep],
    [ProofIrrelevance.proof_irrelevance], [PropExtensionality.propositional_extensionality],
    [ClassicalUniqueChoice.dependent_unique_choice] and [RelationalChoice.relational_choice]. *)
From lantana.program_logic Require adequacy adequacy_iris.
From lantana.heap_lang Require triple.
From lantana.heap_lang.examples Require flag nondet handoff ticket_lock queue task_queue.
From lantana.heap_lang.examples Require flag_fork handoff_client task_queue_client flag_client.
From lantana.heap_lang.examples Require paradox.

(** * Adequacy (Theorem 1) and Iris-style safety *)
Print Assumptions adequacy.lwp_adequacy.
Print Assumptions adequacy_iris.lwp_adequacy_safety_iris.

(** * The clients: liveness, safety, and both *)
Print Assumptions flag_fork.main_adequacy.
Print Assumptions flag_fork.main_safety_adequacy.
Print Assumptions flag_fork.main_liveness_safety.
Print Assumptions handoff_client.handoff_client_adequacy.
Print Assumptions handoff_client.handoff_client_safety_adequacy.
Print Assumptions handoff_client.handoff_client_liveness_safety.
Print Assumptions task_queue_client.task_queue_client_adequacy.
Print Assumptions task_queue_client.task_queue_client_safety_adequacy.
Print Assumptions task_queue_client.task_queue_client_liveness_safety.
Print Assumptions flag_client.flag_client_adequacy.
Print Assumptions flag_client.flag_client_safety_adequacy.
Print Assumptions flag_client.flag_client_liveness_safety.

(** * The paradox: a fuel-free pure-step rule is unsound *)
Print Assumptions paradox.no_lc_absurd.

(** * The rules of the fuel-burning triple ([triple.v]), all at once *)
Definition triple_rules :=
    (@triple.spec_persistent_intro, @triple.fbtriple_gen_texan, @triple.fbtriple_texan,
     @triple.fbtriple_gen_conseq, @triple.fbtriple_conseq, @triple.fbtriple_top_texan,
     @triple.fbtriple_value, @triple.fbtriple_exit, @triple.fbtriple_top_lwp,
     @triple.fbtriple_bind, @triple.fbtriple_frame, @triple.fbtriple_gen_bind,
     @triple.fbtriple_gen_frame, @triple.fbtriple_gen_wand_pre, @triple.fbtriple_wand_pre,
     @triple.fbtriple_upd_elim, @triple.fbtriple_gupd_elim, @triple.fbtriple_always_alloc,
     @triple.fbtriple_always_acc, @triple.fbtriple_carrier_alloc,
     @triple.fbtriple_carrier_delete, @triple.fbtriple_obls_offload,
     @triple.fbtriple_until_alloc, @triple.fbtriple_finally_alloc, @triple.fbtriple_until_acc,
     @triple.fbtriple_until_discharge, @triple.fbtriple_wit_ind, @triple.fbtriple_step_pure_wit,
     @triple.fbtriple_step_pure_lc, @triple.fbtriple_step_pure, @triple.fbtriple_gen_pure_step,
     @triple.fbtriple_pure_step, @triple.fbtriple_step_ref, @triple.fbtriple_step_store,
     @triple.fbtriple_step_load, @triple.fbtriple_fork, @triple.fbtriple_step_pure_wit1,
     @triple.fbtriple_fork1, @triple.fbtriple_finally_exit, @triple.fuels_add,
     @triple.fuels_union, @triple.fuels_empty, @triple.fuels_mono, @triple.fuels_weaken,
     @triple.fuels_layer_eq, @triple.fuels_layer, @triple.always_persistent,
     @triple.persistently_persistent, @triple.persistent_dup, @triple.wit_layer_persistent,
     @triple.obl_done_persistent, @triple.lob, @triple.lc_spend, @triple.until_done_false,
     @triple.until_split).
Print Assumptions triple_rules.

(** * The case-study specifications in the paper's format, all at once *)
Definition case_study_specs :=
    (@flag.Flag_init_fbspec, @flag.Flag_set_fbspec, @flag.Flag_wait_fbspec,
     @nondet.Nondet_nest_fbspec, @nondet.Nondet_nondet_fbspec, @handoff.Handoff_send_fbspec,
     @handoff.Handoff_receive_fbspec, @handoff.is_task_fbtriple,
     @ticket_lock.TicketLock_init_fbspec, @ticket_lock.TicketLock_acquire_fbspec,
     @ticket_lock.TicketLock_release_fbspec, @ticket_lock.TicketLock_delete_fbspec,
     @queue.Queue_init_fbspec, @queue.Queue_enqueue_fbspec, @queue.Queue_dequeue_fbspec,
     @task_queue.TaskQueue_init_fbspec, @task_queue.TaskQueue_put_task_fbspec,
     @task_queue.TaskQueue_run_task_fbspec, @task_queue.TaskQueue_worker_fbspec,
     @flag_fork.FlagFork_main_fbspec, @handoff_client.main_fbspec,
     @task_queue_client.decr_reentrant_fbspec, @task_queue_client.main_fbspec,
     @flag_client.writer_fbspec, @flag_client.reader_fbspec).
Print Assumptions case_study_specs.
