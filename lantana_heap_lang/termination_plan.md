Only `lantana/program_logic/lifting.v`, its downstream files, and files in `lantana_heap_lang` needs to be edited.
If you have to edit other files in `lantana/`, please stop and report back with the reason.

The goal of the refactoring is to remove the `label_def` and related definitions, and instead use thread expressions directly for expressing thread properties, such as termination.
To begin with, remove `label_def` and any related definitions and lemmas.
Then, update `thread_expr` to something like this:
```
Definition thread_expr `{heap_stateGS Σ} (i : thread_id) (K : ectx_item _) (e : expr) : iProp Σ :=
  (thread i true (K e) 1).
```
Basically, what we want is a predicate that tracks the current context and the expression precisely.
The correct type of `K` and the exact definition can be modified if there are better options for making program proofs easier.
Note that `state_interp_aux` needs to be fixed; `True` should work.

Next, fix `state_pred` in `lang.v` by removing `pred_label` and instead having something like `pred_expr i K e`.
`state_pred_interp` should interpret `pred_expr` into `thread_expr`. 
Also, we need to update the step rules because they will require `thread_expr`.
In particular, several rules in `lantana/program_logic/lifting.v` and its downstream files will need to be generalized.
The triple specifications will also have to start with quantifications `∃ μ, ∀ K ...`, require `thread_expr` with the quantified context `K` and the function's expression `e` in the precondition, and return `thread_expr` with the same context `K` and the expression evaluated to the return value `v` in the postcondition.
One technical problem is the program proofs relies on tactics such as `lwp_bind` to manipulate the expression to massage it into the context and the atomic expression.
We will need similar tactics to manipulate `thread_expr`, so that it can have the same context-atomic expression setup.

The key insight is that `thread_expr` will preserve the precise context `K`.
Therefore, when a closed client program is proved with `thread_expr`, the proof will have `thread_expr empty_context v` for the terminating value `v`, and the adequacy will give us `pred_expr i empty_context v`, which clearly means thread `i` is evaluated to a value and terminated.
This is much clearer than the current label-based termination argument.

Please also fix the examples to drop `Label` decorations previously used to indicate termination.
Finally, fix all the examples to compile normally.
