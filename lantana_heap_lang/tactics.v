From stdpp Require Import fin_maps.
From lantana.heap_lang Require Export lang.
From iris.prelude Require Import options.
Import heap_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => go (AppLCtx v :: K) e
    | App ?e1 ?e2                     => go (AppRCtx e1 :: K) e2
    | UnOp ?op ?e                     => go (UnOpCtx op :: K) e
    | BinOp ?op ?e (Val ?v)           => go (BinOpLCtx op v :: K) e
    | BinOp ?op ?e1 ?e2               => go (BinOpRCtx op e1 :: K) e2
    | If ?e0 ?e1 ?e2                  => go (IfCtx e1 e2 :: K) e0
    | Pair ?e (Val ?v)                => go (PairLCtx v :: K) e
    | Pair ?e1 ?e2                    => go (PairRCtx e1 :: K) e2
    | Fst ?e                          => go (FstCtx :: K) e
    | Snd ?e                          => go (SndCtx :: K) e
    | InjL ?e                         => go (InjLCtx :: K) e
    | InjR ?e                         => go (InjRCtx :: K) e
    | Case ?e0 ?e1 ?e2                => go (CaseCtx e1 e2 :: K) e0
    | AllocN ?e (Val ?v)              => go (AllocNLCtx v :: K) e
    | AllocN ?e1 ?e2                  => go (AllocNRCtx e1 :: K) e2
    | Free ?e                         => go (FreeCtx :: K) e
    | Load ?e                         => go (LoadCtx :: K) e
    | Store ?e (Val ?v)               => go (StoreLCtx v :: K) e
    | Store ?e1 ?e2                   => go (StoreRCtx e1 :: K) e2
    | Xchg ?e (Val ?v)                => go (XchgLCtx v :: K) e
    | Xchg ?e1 ?e2                    => go (XchgRCtx e1 :: K) e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => go (CmpXchgLCtx v1 v2 :: K) e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => go (CmpXchgMCtx e0 v2 :: K) e1
    | CmpXchg ?e0 ?e1 ?e2             => go (CmpXchgRCtx e0 e1 :: K) e2
    | FAA ?e (Val ?v)                 => go (FaaLCtx v :: K) e
    | FAA ?e1 ?e2                     => go (FaaRCtx e1 :: K) e2
    end
  in
  go (@nil ectx_item) e.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step _ ?e _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _ _ _) => eexists _, _, _, _; simpl : base_step.
Global Hint Extern 0 (base_reducible_no_obs _ _ _ _) => eexists _, _, _; simpl : base_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _ _ _) => econstructor : base_step.
Global Hint Extern 0 (base_step _ (CmpXchg _ _ _) _ _ _ _ _ _) => eapply CmpXchgS : base_step.
Global Hint Extern 0 (base_step _ (AllocN _ _) _ _ _ _ _ _) => apply alloc_fresh : base_step.
Global Hint Extern 0 (base_step _ (Fork _) _ _ _ _ _ _) => apply new_thread_id_fresh : base_step.
