From lantana.heap_lang Require Export lang.
From iris.prelude Require Import options.
Import heap_lang.

(** Tactics on heap_lang's operational semantics: [reshape_expr], [inv_base_step], and the
    [base_step] hint database. *)

(** [reshape_expr e tac] calls [tac K e'] for each decomposition [e = fill K e'] until [tac]
    succeeds. *)
Ltac reshape_expr e tac :=
  (* [K]: the finished items; [vs]: the (prophecy, value) pairs of the [ResolveLCtx] items
     under construction. [add_item] wraps a finished item in one [ResolveLCtx] per pair. *)
  let rec go K vs e :=
    match e with
    | _                               => lazymatch vs with [] => tac K e | _ => fail end
    | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2
    | Fst ?e                          => add_item FstCtx vs K e
    | Snd ?e                          => add_item SndCtx vs K e
    | InjL ?e                         => add_item InjLCtx vs K e
    | InjR ?e                         => add_item InjRCtx vs K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) vs K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) vs K e2
    | Free ?e                         => add_item FreeCtx vs K e
    | Load ?e                         => add_item LoadCtx vs K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2
    | Xchg ?e (Val ?v)                => add_item (XchgLCtx v) vs K e
    | Xchg ?e1 ?e2                    => add_item (XchgRCtx e1) vs K e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLCtx v1 v2) vs K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMCtx e0 v2) vs K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgRCtx e0 e1) vs K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLCtx v) vs K e
    | FAA ?e1 ?e2                     => add_item (FaaRCtx e1) vs K e2
    | Resolve ?ex (Val ?v1) (Val ?v2) => go K ((v1,v2) :: vs) ex
    | Resolve ?ex ?e1 (Val ?v2)       => add_item (ResolveMCtx ex v2) vs K e1
    | Resolve ?ex ?e1 ?e2             => add_item (ResolveRCtx ex e1) vs K e2
    | Label ?t ?e                     => add_item (LabelCtx t) vs K e
    end
  with add_item Ki vs K e :=
    lazymatch vs with
    | []               => go (Ki :: K) (@nil (val * val)) e
    | (?v1,?v2) :: ?vs => add_item (ResolveLCtx Ki v1 v2) vs K e
    end
  in
  go (@nil ectx_item) (@nil (val * val)) e.

(** [inv_base_step] inverts [base_step] hypotheses, discharges base steps from values, and
    simplifies value conversions and map operations. Tuned for the lifting lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step _ ?e _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inverting on a variable [e] gives many goals *)
     inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _ _ _) => eexists _, _, _, _; simpl : base_step.
Global Hint Extern 0 (base_reducible_no_obs _ _ _ _) => eexists _, _, _; simpl : base_step.

(* Extern hints, since [simple apply] fails on these goals. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _ _ _) => econstructor : base_step.
Global Hint Extern 0 (base_step _ (CmpXchg _ _ _) _ _ _ _ _ _) => eapply CmpXchgS : base_step.
Global Hint Extern 0 (base_step _ (AllocN _ _) _ _ _ _ _ _) => apply alloc_fresh : base_step.
Global Hint Extern 0 (base_step _ NewProph _ _ _ _ _ _) => apply new_proph_id_fresh : base_step.
Global Hint Extern 0 (base_step _ (Fork _) _ _ _ _ _ _) => apply new_thread_id_fresh : base_step.
