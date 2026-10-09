(** Proof-mode tactics for HeapLang's [lWP], adapted from Iris's
[heap_lang/proofmode.v]. The tactics expect the thread-expression token
[thread_expr] in a hypothesis named "TE", and keep it focused on the current
expression. Only tactics for pure steps and for bind are provided; for heap
operations, proofs apply the rules of [primitive_laws] (e.g. [lwp_load])
directly. *)

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From lantana.program_logic Require Import atomic.
From lantana.heap_lang Require Export tactics derived_laws.
From lantana.heap_lang Require Import notation.
From iris.prelude Require Import options.
Import uPred.

(** Move evaluation-context items between the expression and the context of a
[thread_expr] token. The filled expression [fill C e] does not change. Context
lists are innermost first. *)
Lemma thread_expr_focus_eq `{!heapGS Σ} i C D e e' :
  e = fill D e' →
  thread_expr i C e ⊢ thread_expr i (D ++ C) e'.
Proof. intros ->. by rewrite thread_expr_fill. Qed.

Lemma thread_expr_cons `{!heapGS Σ} i C Ki e :
  thread_expr i (Ki :: C) e ⊣⊢ thread_expr i C (fill_item Ki e).
Proof. by rewrite /thread_expr /=. Qed.

(** [thread_expr_focus H efoc] rewrites the token [H] so that its expression is
[efoc]. It moves context items from the expression into the token's context,
or, if [efoc] is not inside the expression, back out of the context. *)
Ltac thread_expr_focus H efoc :=
  lazymatch iTypeOf H with
  | Some (false, thread_expr ?i ?C ?e) =>
      let e := eval simpl in e in
      first
        [ unify e efoc
        | reshape_expr e ltac:(fun D e' =>
            unify e' efoc;
            iPoseProof (thread_expr_focus_eq i C D e e' with H) as H;
            [reflexivity|])
        | lazymatch eval hnf in C with
          | ?Ki :: ?D =>
              iEval (rewrite (thread_expr_cons i D Ki e)) in H;
              thread_expr_focus H efoc
          end ]
  | _ => fail "thread_expr_focus: expected a spatial thread_expr hypothesis"
  end.

Tactic Notation "thread_expr_focus" constr(H) open_constr(efoc) :=
  thread_expr_focus H efoc.

(** Focus the token "TE" on the expression of the [lWP] or [lwpupd] goal. *)
Ltac thread_expr_focus_goal :=
  lazymatch goal with
  | |- envs_entails _ (lwp _ _ _ ?e _) => thread_expr_focus "TE" e
  | |- envs_entails _ (lwpupd _ _ ?e _) => thread_expr_focus "TE" e
  end.

Lemma tac_lwp_expr_eval `{!heapGS Σ} Δ s i E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (lWP e' @ s; i; E {{ Φ }}) →
  envs_entails Δ (lWP e @ s; i; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "lwp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
      notypeclasses refine (tac_lwp_expr_eval _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "lwp_expr_eval: not a 'lwp'"
  end.
Ltac lwp_expr_simpl := lwp_expr_eval simpl.

(** General form of a pure-step tactic lemma: each of the [n] steps pays one
unit of fuel for every carrier. The [lwp_pure] tactic uses
[tac_lwp_pure_simple] below instead. *)
Lemma tac_lwp_pure `{!heapGS Σ} Δ (s : stuckness) i E
    (K : list (ectxi_language.ectx_item _)) e1 e2 φ n (Φ : val → iProp Σ) {C} :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (thread_expr i C (fill K e1) ∗ ∃ E' G R (o : Ord.t),
        ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
        (Nat.iter n (λ (P : iProp Σ), |={E,E'}=>
                       thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ 1) ∗
                       (thP_carriers i G -∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                        ALC (£ o ={E',E}=∗ |={E}=>m P)))
           (thread_expr i C (fill K e2) -∗
            lwpupd i E (fill K e2) (lWP (fill K e2) @ s; i; E {{ Φ }}))))%I →
  envs_entails Δ (lWP (fill K e1) @ s; i; E {{ Φ }})%I.
Proof.
  rewrite envs_entails_unseal=> ?? ->.
  pose proof @pure_exec_fill.
  iIntros "(TE& %&%&%&%& #Rs& Iter)".
  iApply (lifting.lwp_pure_step_alt _ _ _ _ _ _ _ _ _ _ _ _
    (λ i e, thread_expr i C e)); first auto.
  iFrame "∗ #".
Qed.

(** The lemma behind [lwp_pure]: [n] pure steps take [n] units out of fuel
[m = n + m'] of every carrier. The remaining fuel [m'], the witness credits for
[R] and the later credits [£ o] go to the continuation. *)
Lemma tac_lwp_pure_simple `{!heapGS Σ} Δ s i E K e1 e2 φ (n m' : nat) Φ {C} :
  PureExec φ n e1 e2 →
  φ →
  0 < n →
  envs_entails Δ (thread_expr i C (fill K e1) ∗ ∃ G (m : nat) R (o : Ord.t),
        (thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ m) ∗
         ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∧ ⌜ (m = n + m')%nat ⌝) ∗
        (thP_carriers i G -∗
         ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ m') -∗
         ([∗ set] r ∈ R, witP_cred r 1 ∨ oblP_discharged r) -∗
         £ (o)%ord -∗
         thread_expr i C (fill K e2) -∗
         lwpupd i E (fill K e2) (lWP (fill K e2) @ s; i; E {{ Φ }})))%I →
  envs_entails Δ (lWP (fill K e1) @ s; i; E {{ Φ }})%I.
Proof.
  rewrite envs_entails_unseal=> ?? ? ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  iIntros "(TE& %&%&%&%& T& H)".
  iApply (lifting.lwp_pure_step_simple _ _ _ o _ _ _ _ _ _ _
    (λ i e, thread_expr i C e)). 1: auto.
  iFrame "TE".
  iDestruct "T" as "($& Fs& $& %)". subst.
  iAssert (([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ n) ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ m'))%I with "[Fs]" as "[$ Fs]".
  { iApply big_sepS_sep. iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& H)".
    rewrite (crP_fuel_eq _ _ _ (n ⊕ m')%M).
    - iPoseProof (crP_fuel_add with "H") as "[$ $]".
    - rewrite measure_rep_add !measure_rep_nat Hessenberg.add_from_nat. done. }
  iIntros "TE TG Ws LC".
  iAssert (|==> ([∗ set] r ∈ R, witP_cred r 1 ∨ oblP_discharged r))%I with "[Ws]" as ">Ws".
  { iApply big_sepS_bupd. iApply (big_sepS_impl with "Ws"). iIntros "!> %% [H | H]". 2: by iFrame.
    iMod (witP_cred_lt with "H") as "[_ H]".
    { apply OrdArith.lt_from_nat. eauto. }
    by iFrame. }
  iApply lwpupd_fupd_l. iApply rupd_fupd. iMod (tlc_weaken _ o with "LC") as "LC".
  { unshelve etransitivity. 1: exact (o × 1)%ord.
    - rewrite Jacobsthal.mult_1_r. done.
    - apply Jacobsthal.le_mult_r, OrdArith.le_from_nat. lia. }
  iApply ("H" with "TG Fs Ws LC TE").
Qed.

Lemma tac_lwp_value_nofupd `{!heapGS Σ} Δ s i E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (lWP (Val v) @ s; i; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply lwp_value. Qed.

Lemma tac_lwp_value `{!heapGS Σ} Δ s i E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=>g Φ v) → envs_entails Δ (lWP (Val v) @ s; i; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. iIntros "H". iApply lwp_value_sfgupd. by iMod "H". Qed.

(** Simplify the goal if it is [lWP] of a value. If the postcondition already
is a fancy update or an [lWP], do not add an update. Otherwise add a ghost
update [|={E}=>g]: [lWP] of a value is equivalent to it ([lwp_value_sfgupd]), so
this never makes the goal unprovable. *)
Ltac lwp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (lwp ?s ?i ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_lwp_value_nofupd
  | |- envs_entails _ (lwp ?s ?i ?E (Val _) (λ _, lwp _ _ ?E _ _)) =>
      eapply tac_lwp_value_nofupd
  | |- envs_entails _ (lwp ?s ?i ?E (Val _) _) =>
      eapply tac_lwp_value
  end.

Ltac lwp_finish :=
  lwp_expr_simpl;      (* simplify occurrences of subst/fill *)
  try thread_expr_focus_goal;
  try lwp_value_head;  (* in case we have reached a value, get rid of the lWP *)
  pm_prettify.        (* prettify λs caused by [lwp_value] *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [lwp_pure (If _ _ _)], which will search
for an [If _ _ _] in the expression, and reduce it. The new goal asks for the
carriers and the fuel that pay for the step (see [tac_lwp_pure_simple]).

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurrence is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "lwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
    let e := eval simpl in e in
    thread_expr_focus "TE" e;
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_lwp_pure_simple _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |try lia (* must take at least one step *)
      |iFrame "TE" (* frame the token for the redex *)
      ])
    || fail "lwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "lwp_pure: not a 'lwp'"
  end.
Tactic Notation "lwp_pure" :=
  lwp_pure _.

(** Unlike [lwp_pure _], the tactics [lwp_rec] and [lwp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "lwp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  lwp_pure (App _ _);
  clear H.

Tactic Notation "lwp_if" := lwp_pure (If _ _ _).
Tactic Notation "lwp_if_true" := lwp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "lwp_if_false" := lwp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "lwp_unop" := lwp_pure (UnOp _ _).
Tactic Notation "lwp_binop" := lwp_pure (BinOp _ _ _).
Tactic Notation "lwp_op" := lwp_unop || lwp_binop.
Tactic Notation "lwp_lam" := lwp_rec.
Tactic Notation "lwp_let" := lwp_pure (Rec BAnon (BNamed _) _).
Tactic Notation "lwp_seq" := lwp_pure (Rec BAnon BAnon _).
Tactic Notation "lwp_proj" := lwp_pure (Fst _) || lwp_pure (Snd _).
Tactic Notation "lwp_case" := lwp_pure (Case _ _ _).
Tactic Notation "lwp_inj" := lwp_pure (InjL _) || lwp_pure (InjR _).
Tactic Notation "lwp_pair" := lwp_pure (Pair _ _).
Tactic Notation "lwp_closure" := lwp_pure (Rec _ _ _).

(** [lwp_bind_step efoc] binds on an [lWP] goal. The redex [efoc] must not be a
value, and the continuation is wrapped in [lwpupd]. *)
Lemma tac_lwp_bind_step `{!heapGS Σ} K Δ s i E Φ e f :
  TCEq (to_val e) None →
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (lWP e @ s; i; E {{ v, lwpupd i E (f (Val v)) (lWP f (Val v) @ s; i; E {{ Φ }}) }})%I →
  envs_entails Δ (lWP fill K e @ s; i; E {{ Φ }})%I.
Proof. intros He. rewrite envs_entails_unseal=> -> ->. by apply: lwp_bind_step. Qed.

Ltac lwp_bind_step_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_lwp_bind_step K); [tc_solve|simpl; reflexivity|reduction.pm_prettify; thread_expr_focus_goal]
  end.

Tactic Notation "lwp_bind_step" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; lwp_bind_step_core K)
          | fail 1 "lwp_bind: cannot find" efoc "in" e ]
  | _ => fail "lwp_bind: not a 'lwp'"
  end.

(** [lwp_bind efoc] binds on a goal [lwpupd i E e (lWP e ...)]. *)
Lemma tac_lwp_bind_gen `{!heapGS Σ} K Δ s i E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (lwpupd i E e (lWP e @ s; i; E {{ v, lwpupd i E (f (Val v)) (lWP f (Val v) @ s; i; E {{ Φ }}) }}))%I →
  envs_entails Δ (lwpupd i E (fill K e) (lWP fill K e @ s; i; E {{ Φ }}))%I.
Proof. rewrite envs_entails_unseal=> -> ->. by apply: lwp_bind_lwpupd. Qed.

Ltac lwp_bind_gen_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_lwp_bind_gen K); [simpl; reflexivity|reduction.pm_prettify; thread_expr_focus_goal]
  end.

Tactic Notation "lwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (lwpupd ?i ?E ?e (lwp ?s ?i ?E ?e ?Q)) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; lwp_bind_gen_core K)
          | fail 1 "lwp_bind: cannot find" efoc "in" e ]
  | _ => fail "lwp_bind: not a 'lwpupd lwp'"
  end.

(** Variants of [lwp_expr_eval] and [lwp_finish] for goals
[lwpupd i E e (lWP e ...)]. *)
Lemma tac_lwp_expr_eval_upd `{!heapGS Σ} Δ s i E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  environments.envs_entails Δ (lwpupd i E e' (lWP e' @ s; i; E {{ Φ }}))%I →
  environments.envs_entails Δ (lwpupd i E e (lWP e @ s; i; E {{ Φ }}))%I.
Proof. by intros ->. Qed.

Tactic Notation "lwp_expr_eval_upd" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (lwpupd ?i ?E ?e (lwp ?s ?i ?E ?e ?Q)) =>
      notypeclasses refine (tac_lwp_expr_eval_upd _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "lwp_expr_eval_upd: not a 'lwpupd lwp'"
  end.
Ltac lwp_expr_simpl_upd := lwp_expr_eval_upd simpl.

(* Simplify occurrences of subst/fill, and refocus the token. *)
Ltac lwp_finish_upd :=
  lwp_expr_simpl_upd; try thread_expr_focus_goal.
