From iris.proofmode Require Import rocq_tactics reduction.
From iris.proofmode Require Export proofmode.
From lantana.heap_lang Require Export tactics derived_laws.
From lantana.heap_lang Require Import notation.
From iris.prelude Require Import options.

(** Proof-mode tactics for lWP on heap_lang: focusing the thread's expression token ["TE"],
    pure steps ([lwp_pure] and the tactics built on it), binding ([lwp_bind]), and values
    ([lwp_finish]). *)

(** * Focusing the thread expression *)

(** Moving context items between [C] and [e]; context items are innermost first. *)
Lemma thread_expr_focus_eq `{!heapGS Σ} i C D e e' :
  e = fill D e' →
  thread_expr i C e ⊢ thread_expr i (D ++ C) e'.
Proof. intros ->. by rewrite thread_expr_fill. Qed.

Lemma thread_expr_cons `{!heapGS Σ} i C Ki e :
  thread_expr i (Ki :: C) e ⊣⊢ thread_expr i C (fill_item Ki e).
Proof. by rewrite /thread_expr /=. Qed.

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

Ltac thread_expr_focus_goal :=
  lazymatch goal with
  | |- envs_entails _ (lwp _ _ _ ?e _) => thread_expr_focus "TE" e
  | |- envs_entails _ (|={_}=>m (lwp _ _ _ ?e _)) => thread_expr_focus "TE" e
  end.

(** * Simplification and values *)
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

Lemma tac_lwp_value_nofupd `{!heapGS Σ} Δ s i E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (lWP (Val v) @ s; i; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply lwp_value. Qed.

Lemma tac_lwp_value `{!heapGS Σ} Δ s i E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=>m Φ v) → envs_entails Δ (lWP (Val v) @ s; i; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. iIntros "H". rewrite lwp_value_sfmupd. by iMod "H". Qed.

(** [lWP] of a value: add a model update unless the postcondition allows a fupd or is an
    [lWP], so that every lemma applied is bidirectional. *)
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
  pm_prettify.         (* prettify λs caused by lwp_value *)

(** * Pure steps *)

(** [n] pure steps at once: they burn [n] of the [m = n + m'] units of fuel of each of the
    thread's obligations [G], and give a witness credit for each [r ∈ R] (unless [r] is
    discharged) and [o] later credits. *)
Lemma tac_lwp_pure_simple `{!heapGS Σ} Δ s i E K e1 e2 φ (n m' : nat) Φ {C} :
  PureExec φ n e1 e2 →
  φ →
  0 < n →
  envs_entails Δ (thread_expr i C (fill K e1) ∗ ∃ G (m : nat) R (o : Ord.t),
        (thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ m) ∗
         ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∧ ⌜ (m = n + m')%nat ⌝) ∗
        (thP_kids i G -∗
         ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ m') -∗
         ([∗ set] r ∈ R, witP_cred r 1 ∨ oblP_discharged r) -∗
         £ (o)%ord -∗
         thread_expr i C (fill K e2) -∗
         (|={E}=>m (lWP (fill K e2) @ s; i; E {{ Φ }}))))%I →
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
  iAssert (([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ n) ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ m'))%I with "[Fs]" as "[$ Fs]".
  { iApply big_sepS_sep. iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& H)".
    rewrite (oblP_fuel_eq _ _ _ (n ⊕ m')%M).
    - iPoseProof (oblP_fuel_add with "H") as "[$ $]".
    - rewrite measure_rep_add !measure_rep_nat Hessenberg.add_from_nat. done. }
  iIntros "TE TG Ws LC".
  iAssert (|==> ([∗ set] r ∈ R, witP_cred r 1 ∨ oblP_discharged r))%I with "[Ws]" as ">Ws".
  { iApply big_sepS_bupd. iApply (big_sepS_impl with "Ws"). iIntros "!> %% [H | H]". 2: by iFrame.
    iMod (witP_cred_lt with "H") as "[_ H]".
    { apply OrdArith.lt_from_nat. eauto. }
    by iFrame. }
  iApply sfmupd_fupd_l. iApply rupd_fupd. iMod (tlc_weaken _ o with "LC") as "LC".
  { unshelve etransitivity. 1: exact (o × 1)%ord.
    - rewrite Jacobsthal.mult_1_r. done.
    - apply Jacobsthal.le_mult_r, OrdArith.le_from_nat. lia. }
  iApply ("H" with "TG Fs Ws LC TE").
Qed.

Ltac solve_vals_compare_safe :=
  (* [vals_compare_safe] or one of its disjuncts, in the context or trivial *)
  fast_done || (left; fast_done) || (right; fast_done).

(** [lwp_pure efoc] reduces a redex matching [efoc], e.g. [lwp_pure (If _ _ _)];
    [open_constr] turns the holes of [efoc] into evars. *)
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
      |try solve_vals_compare_safe    (* its pure condition *)
      |try lia (* at least one step *)
      |iFrame "TE"
      ])
    || fail "lwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "lwp_pure: not a 'lwp'"
  end.
Tactic Notation "lwp_pure" :=
  lwp_pure _.

(** [lwp_rec] also reduces recs hidden behind definitions: [AsRecV_recv] is put in the
    context as an instance (see class_instances.v). *)
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
Tactic Notation "lwp_label" := lwp_pure (Label _ _).

(** * Bind *)
Lemma tac_lwp_bind_gen `{!heapGS Σ} K Δ s i E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ ((|={E}=>m (lWP e @ s; i; E {{ v, (|={E}=>m (lWP f (Val v) @ s; i; E {{ Φ }})) }})))%I →
  envs_entails Δ ((|={E}=>m (lWP fill K e @ s; i; E {{ Φ }})))%I.
Proof. rewrite envs_entails_unseal=> -> ->. by apply: lwp_bind_sfmupd. Qed.

Ltac lwp_bind_gen_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_lwp_bind_gen K); [simpl; reflexivity|reduction.pm_prettify; thread_expr_focus_goal]
  end.

Tactic Notation "lwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ ((|={?E}=>m (lwp ?s ?i ?E ?e ?Q))) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; lwp_bind_gen_core K)
          | fail 1 "lwp_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (lwp ?s ?i ?E ?e ?Q) =>
    (* a plain [lWP] goal absorbs a model update ([sfmupd_lwp]) *)
    iApply sfmupd_lwp;
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; lwp_bind_gen_core K)
          | fail 1 "lwp_bind: cannot find" efoc "in" e ]
  | _ => fail "lwp_bind: not a 'lWP' or '|={E}=>m lWP'"
  end.
