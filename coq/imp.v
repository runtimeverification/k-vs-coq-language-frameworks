(* Based on the imp example in coind,
   extracted to a single-file.
 *)
(* Developed with Coq 8.9.1 *)

Require Import String.
Require Import ZArith.
Require Import List.

Set Implicit Arguments.

Local Open Scope Z.
Import List.ListNotations.
Local Open Scope list.
Local Open Scope string.

(** * The syntax of IMP programs *)

Inductive AExp :=
  | var : string -> AExp
  | con : Z -> AExp
  | div : AExp -> AExp -> AExp
  | plus : AExp -> AExp -> AExp
  .

Inductive BExp :=
  | bcon : bool -> BExp
  | le : AExp -> AExp -> BExp
  | not : BExp -> BExp
  | and : BExp -> BExp -> BExp
  .

Inductive Stmt :=
  | assign : string -> AExp -> Stmt
  | cond : BExp -> Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | skip : Stmt
  .

Inductive Pgm :=
    pgm : list string -> Stmt -> Pgm.

(** Here is the sum program *)
Definition sum_pgm N : Pgm :=
 pgm ["n"; "sum"]
(seq (assign "n" (con N))
(seq (assign "sum" (con 0))
     (while (not (le (var "n") (con 0)))
     (seq (assign "sum" (plus (var "sum") (var "n")))
          (assign "n" (plus (var "n") (con (-1)))))))).

(** * The semantics of IMP programs *)

Definition Env := list (string * Z).
Definition empty_env : Env := [].
Fixpoint get x (env:Env) :=
  match env with
  | [] => None
  | (x',v)::env' =>
    if string_dec x x' then Some v else get x env'
  end.
Fixpoint set x v (env:Env) :=
  match env with
  | [] => []
  | (x',v')::env' =>
    if string_dec x x' then (x,v)::env' else (x',v')::set x v env'
  end.
  (* "simpl" should reduce set if concrete values are given for both variables *)

(* ** These "step" types together define single execution steps  *)
Inductive step_e : (AExp * Env) -> (AExp * Env) -> Prop :=
  | step_var: forall v x env, get v env = Some x ->
      step_e (var v, env) (con x, env)
  | step_plus: forall x y env,
      step_e (plus (con x) (con y), env) (con (Z.add x y), env)
  | step_div: forall x y env,
      y <> 0%Z ->
      step_e (div (con x) (con y), env) (con (Z.div x y), env)
  | cong_plus_r: forall e1 e2 e2' env env',
      step_e (e2, env) (e2', env') ->
      step_e (plus e1 e2, env) (plus e1 e2', env')
  | cong_plus_l: forall e2 e1 e1' env env',
      step_e (e1, env) (e1', env') ->
      step_e (plus e1 e2, env) (plus e1' e2, env')
  | cong_div_r: forall e1 e2 e2' env env',
      step_e (e2, env) (e2', env') ->
      step_e (div e1 e2, env) (div e1 e2', env')
  | cong_div_l: forall e2 e1 e1' env env',
      step_e (e1, env) (e1', env') ->
      step_e (div e1 e2, env) (div e1' e2, env')
  .

(* These abbreviations capture the pattern of the congruence rules *)
Notation cong_l op R1 R2 :=
  (forall a env a' env', R1 (a,env) (a',env') ->
   forall b, R2 (op a b, env) (op a' b, env')).
Notation cong_r op nf R1 R2 :=
  (forall b env b' env', R1 (b,env) (b',env') ->
   forall a, R2 (op (nf a) b, env) (op (nf a) b', env')).
Notation cong_1 op R1 R2 :=
  (forall a env a' env', R1 (a,env) (a',env') -> R2 (op a, env) (op a', env')).

Inductive step_b : (BExp * Env) -> (BExp * Env) -> Prop :=
  | eval_le : forall v1 v2 env,
      step_b (le (con v1) (con v2), env) (bcon (Z.leb v1 v2), env)
  | eval_not : forall b env,
      step_b (not (bcon b), env) (bcon (negb b), env)
  | eval_and : forall b e env,
      step_b (and (bcon b) e, env) (if b then e else bcon false, env)
  | cong_le_r : cong_r le con step_e step_b
  | cong_le_l : cong_l le step_e step_b
  | cong_not : cong_1 not step_b step_b
  | cong_and : cong_l and step_b step_b
  .

Inductive step_s : (Stmt * Env) -> (Stmt * Env) -> Prop :=
  | exec_assign : forall x v v0 env,  get x env = Some v0 ->
      step_s (assign x (con v),env) (skip, set x v env)
  | cong_assign : forall x,
      cong_1 (assign x) step_e step_s
  | exec_seq : forall s env,
      step_s (seq skip s,env) (s,env)
  | cong_seq : cong_l seq step_s step_s
  | exec_cond : forall b s1 s2 env,
      step_s (cond (bcon b) s1 s2, env) (if b then s1 else s2, env)
  | cong_cond : forall b b' env env' s1 s2, step_b (b,env) (b',env') ->
      step_s (cond b s1 s2,env) (cond b' s1 s2,env')
  | exec_while : forall b s env,
      step_s (while b s,env) (cond b (seq s (while b s)) skip, env)
  .

Inductive step_p : (Pgm * Env) -> (Pgm * Env) -> Prop :=
  | exec_init: forall x xs s env,
      step_p (pgm (x::xs) s,env) (pgm xs s, (x,0)::env)
  | exec_body: forall s env s' env',
      step_s (s, env) (s', env') ->
      step_p (pgm nil s, env) (pgm nil s', env')
  .

(** Now we verify the program *)
Require Import proof_system.

(** The claim about the loop says that running the loop in any enviroment
    with a non-negative n finishes with n set to zero, and sum increased
    from it's original value by the sum of numbers 0+1+...+n.
 *)
Inductive sum_spec : Spec (Pgm * Env) :=
 | sum_claim: forall n, 0 <= n ->
   sum_spec
     (pgm ["n"; "sum"]
       (seq (assign "n" (con n))
       (seq (assign "sum" (con 0))
            (while (not (le (var "n") (con 0)))
            (seq (assign "sum" (plus (var "sum") (var "n")))
                 (assign "n" (plus (var "n") (con (-1))))))))
     ,[])
     (fun cfg' => cfg' = (pgm [] skip, [("sum",((n + 1) * n)/2);("n",0)]))
 | sum_loop_claim : forall env n, get "n" env = Some n -> 0 <= n ->
                    forall s, get "sum" env = Some s ->
      sum_spec
         (pgm []
           (while (not (le (var "n") (con 0)))
             (seq (assign "sum" (plus (var "sum") (var "n")))
                  (assign "n" (plus (var "n") (con (-1))))))
         ,env)
      (fun cfg' => fst cfg' = pgm [] skip /\
         snd cfg' = set "n" 0 (set "sum" (s + ((n + 1) * n)/2) env)).

(* Some lemmas about enviroment stuff *)
Ltac env_ind_tac env :=
  induction env as [|[]];try reflexivity;simpl;
  repeat match goal with
  | [ |- context [string_dec ?a ?b]] => destruct (string_dec a b);simpl;try congruence
  end.

Lemma env_set_id: forall x v env,
    get x env = Some v ->
    set x v env = env.
Proof.
  env_ind_tac env.
  intro. f_equal. tauto.
Qed.

Lemma env_set_eq:
  forall x v1 v2 env,
    set x v1 (set x v2 env) = set x v1 env.
Proof. env_ind_tac env. Qed.

Lemma env_set_ne_comm:
  forall x1 x2, x1 <> x2 ->
  forall v1 v2 env,
    set x1 v1 (set x2 v2 env) = set x2 v2 (set x1 v1 env).
Proof. env_ind_tac env. Qed.

Lemma env_set_set: forall x1 x2 v1 v2 env,
    set x1 v1 (set x2 v2 env) =
    if string_dec x1 x2
    then set x1 v1 env
    else set x2 v2 (set x1 v1 env).
Proof. env_ind_tac env. Qed.

Definition env_has x env: bool :=
  match get x env with
  | Some _ => true
  | None => false
  end.

Lemma env_has_get x v env:
  get x env = Some v ->
  env_has x env = true.
Proof.
  unfold env_has;intros ->;reflexivity.
Qed.

Lemma env_get_set x x' v env:
  get x (set x' v env) =
  if string_dec x x'
  then if env_has x env then Some v else None
  else get x env.
Proof. unfold env_has; env_ind_tac env. Qed.

Lemma env_has_set x x' v env:
  env_has x (set x' v env) = env_has x env.
Proof.
  unfold env_has.
  rewrite env_get_set.
  unfold env_has.
  destruct (string_dec x x');[|reflexivity].
  destruct (get x env);reflexivity.
Qed.

Ltac step_tac :=
  match goal with
  | [ |- step_p _ _] => econstructor;step_tac
  | [ |- step_s _ _] => econstructor;step_tac
  | [ |- step_b _ _] => econstructor;step_tac
  | [ |- step_e _ _] => econstructor;step_tac
  | [ |- get _ _ = _] => rewrite ?env_get_set;(reflexivity || eassumption)
  end.

Ltac run := repeat first[
   eapply dtrans;[constructor|]
  |eapply ddone;simpl;split;[reflexivity|]
  |eapply dstep;[step_tac|]].

Require Import Recdef.
Function sum_to (n:Z) { wf (fun x y => 0 <= x < y) n } : Z :=
  if Z_lt_ge_dec 0 n then n + sum_to (n - 1) else 0.
intros;omega.
exact (Z.lt_wf 0).
Defined.

Lemma sum_algebra: forall s n, 0 < n ->
  s + n + (n + -1 + 1) * (n + -1) / 2
           = s + (n + 1) * n / 2.
Proof.
  intros s n H.
  rewrite <- Z.add_assoc.
  f_equal.
  rewrite <- Z.add_assoc, Z.add_0_r.
  rewrite <- Z.div_add_l by omega.
  f_equal.
  rewrite Z.mul_add_distr_r, Z.mul_add_distr_l.
  omega.
Qed.

Lemma sum_ok : sound step_p sum_spec.
apply proved_sound;destruct 1.

{ (* Overall claim, easily proved with loop claim *)
  eapply sstep;[solve[step_tac]|].
  run;[reflexivity || assumption ..|].
  destruct k';simpl.
  destruct 1 as [-> ->].
  apply ddone.
  reflexivity.
}


eapply sstep;[solve[step_tac]|].
run.
destruct (Z.leb_spec n 0);simpl.

(* when n = 0, loop exits.
   To conclude, need to prove that the initial
   environment env is an acceptable result *)
run.
replace n with 0 in H |- * by auto with zarith.
rewrite (env_set_id "sum") by (rewrite H1;f_equal;auto with zarith).
rewrite (env_set_id "n") by assumption.
reflexivity.

(* when n > 0, execution goes through the loop body,
   then sum_loop_claim is applied by transitivity,
   which takes us to a state satisfying the goal *)
run.
{ rewrite env_get_set, ?env_has_set.
  simpl.
  erewrite env_has_get by eassumption;reflexivity. }
  omega.
{ rewrite !env_get_set.
  simpl.
  erewrite env_has_get by eassumption;reflexivity. }
destruct k';simpl;intros [-> ->].

run.
rewrite (env_set_set "sum" "n"). simpl.
rewrite 2 env_set_eq.
f_equal.
f_equal.
apply sum_algebra.
assumption.
Qed.