Require Import String.
Require Import ZArith.
Require Import imp.

Local Open Scope Z.
Import List.ListNotations.
Local Open Scope list.
Local Open Scope string.

(** An execution trace is a sequence of zero or more steps.
    We will take the reflexive-transitive closure of the step
    relation using the library type clos_refl_trans_1n *)
Import Relation_Operators.

(** Execution tests can be written as a theorem claiming that
    an initial state reaches an expected final state *)
Lemma test_execution :
  clos_refl_trans_1n _ step_p (sum_pgm 100,[]) (pgm nil skip,[("sum",5050);("n",0)]).
Proof.
  Time repeat (eapply rt1n_trans;[once solve[repeat econstructor]|];simpl).
  apply rt1n_refl.
Time Qed.

(** The final state can also be filled in by the search.
    This statement uses a sort of existential quantification over the
    final environment e2 *)
Lemma test_execution2 :
  {e2:Env | clos_refl_trans_1n _ step_p (sum_pgm 100,[]) (pgm nil skip,e2)}.
Proof.
  eexists.
  Time repeat (eapply rt1n_trans;[once solve[repeat econstructor]|simpl]).
  apply rt1n_refl.
Time Defined.

(** The final environment can be extracted from this trace *)
Eval simpl in proj1_sig test_execution2.
