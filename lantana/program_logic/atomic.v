(** Logically atomic triples for [lwp]. Adapted from Iris's
[iris/program_logic/atomic.v]. The notation is

  <<{ ∀∀ x, atomic_precondition }>>
    e @ i; E
  <<{ ∃∃ y, atomic_postcondition | z, RET v; private_postcondition }>>

where [i] is the thread and [E] the implementation mask. [x] is bound in the rest
of the triple, [y] in both postconditions and [v], and [z] in [v] and the private
postcondition; each can be any number of binders, including none. Unlike Texan
triples, atomic triples are not persistent. A private precondition is written as
a wand in front of the triple. The private postcondition can be left out (with
[| RET v]); with [z] binders it must be present.
*)

From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
From iris.proofmode Require Import proofmode classes.
From iris.bi.lib Require Export atomic.
From lantana.base_logic Require Import invariants.
From lantana.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else.

For the non-atomic post-condition, we use an [option PROP], combined with a
[-∗?]. This is to avoid introducing spurious [True -∗] into proofs that do not
need a non-atomic post-condition (which is most of them). *)
Definition atomic_lwp `{SI : indexT} `{!lantanaGS Λ Σ} {TA TB TP : tele}
  (i : thread_id)
  (e : expr Λ) (* expression *)
  (E : coPset) (* *implementation* mask *)
  (α : TA → iProp Σ) (* atomic pre-condition *)
  (β : TA → TB → iProp Σ) (* atomic post-condition *)
  (POST : TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f : TA → TB → TP → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val Λ → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            lWP e @ i {{ Φ }}.

(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ i ; E '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_lwp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             i
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, i, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ i ; E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_lwp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, i, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ i ; E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_lwp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, i, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ i ; E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_lwp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, i, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ i ; E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_lwp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, i, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ i ; E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_lwp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, i, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ i ; E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_lwp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, i, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ i ; E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_lwp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, i, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ i ; E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_lwp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             i
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, i, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  i ;  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{SI : indexT} `{!lantanaGS Λ Σ} {TA TB TP : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → val Λ).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_lwp_seq i e E α β POST f :
    atomic_lwp i e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ lWP e @ i {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (lwp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* [rewrite ->], since ssreflect [rewrite] fails here (Coq bug #7773). *)
    rewrite ->!tele_app_bind. iIntros (z) "Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_lwp_atomic i e E α β POST f `{!Atomic WeaklyAtomic e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ (lwp NotStuck i ∅ e Φ)) -∗
    atomic_lwp i e E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AU".
    iMod "AU" as (x) "[Hα [_ Hclose]]". iApply ("Hwp" with "Hα"). iIntros "%y Hβ %z Hpost".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_lwp_atomic i e E (α : [tele] → iProp) (β : [tele] → TB → iProp)
      (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → val Λ)
      {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ lWP e @ i {{ Φ }}) -∗
    atomic_lwp i e E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_lwp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply lwp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* [rewrite ->], since ssreflect [rewrite] fails here (Coq bug #7773). *)
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  Lemma atomic_lwp_mask_weaken i e E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_lwp i e E1 α β POST f -∗ atomic_lwp i e E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_lwp_inv i e E α β POST f N I :
    ↑N ⊆ E →
    atomic_lwp i e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_lwp i e E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
