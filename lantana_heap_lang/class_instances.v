From lantana.program_logic Require Export language.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [IntoVal], [AsVal], [Atomic] and [PureExec] instances of heap_lang. Adapted from
    Iris's [iris.heap_lang.class_instances]. *)

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

(** * Instances of the [Atomic] class *)
Section atomic.
  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
      [inversion 1; naive_solver
      |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  Global Instance rec_atomic s f x e : Atomic s (Rec f x e).
  Proof. solve_atomic. Qed.
  Global Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance injl_atomic s v : Atomic s (InjL (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injr_atomic s v : Atomic s (InjR (Val v)).
  Proof. solve_atomic. Qed.
  (** Generalizes [Skip]. *)
  Global Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
  Proof. destruct f, x; solve_atomic. Qed.
  Global Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic s v1 e2 :
    Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. solve_atomic. Qed.
  Global Instance if_false_atomic s e1 v2 :
    Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance fst_atomic s v : Atomic s (Fst (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance snd_atomic s v : Atomic s (Snd (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance fork_atomic s e : Atomic s (Fork e).
  Proof. solve_atomic. Qed.
  Global Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
  Proof. solve_atomic. Qed.
  Global Instance free_atomic s v : Atomic s (Free (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : Atomic s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance xchg_atomic s v1 v2 : Atomic s (Xchg (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

  Global Instance new_proph_atomic s : Atomic s NewProph.
  Proof. solve_atomic. Qed.
  Global Instance resolve_atomic s e v1 v2 :
    Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1. intros H i σ1 τ e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
    simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear step. by eapply (H i σ1 τ (Val _) _ σ2 efs), base_prim_step.
    - rewrite fill_app. rewrite fill_app in Hfill.
      assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
      { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
        apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
      destruct K; (inversion Hfill; clear Hfill; subst; try
        match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
      refine (_ (H i σ1 τ (fill (Ks ++ [_]) e2') _ σ2 efs _)).
      + destruct s; intro Hs; simpl in *.
        * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
        * apply irreducible_resolve. by rewrite fill_app in Hs.
      + econstructor; try done. simpl. by rewrite fill_app.
  Qed.

  Global Instance label_atomic s t v : Atomic s (Label t (Val v)).
  Proof. solve_atomic. Qed.

  Global Instance choosenat_atomic s : Atomic s (ChooseNat).
  Proof. solve_atomic. Qed.
End atomic.

(** * Instances of the [PureExec] class *)
(** [AsRecV v f x erec] turns [v] into [RecV f x erec]. Its instance [AsRecV_recv] is a
    [Hint Extern], used only when [v] is syntactically a rec, so [lwp_pure] does not reduce
    recs hidden behind definitions; [lwp_rec] and [lwp_lam] activate it by hand. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?;
    split; [lia | apply nsteps_once, pure_base_step_pure_step;
                  constructor; [solve_exec_safe | solve_exec_puredet]].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Lower-cost instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_label t v :
    PureExec True 1 (Label t (of_val v)) (of_val v).
  Proof. solve_pure_exec. Qed.

End pure_exec.
