Require Import List ZArith Psatz.
Import ListNotations.

Require Import Sets.


(** * Bruteforce existentials instantiation *)


(** The following few functions are used to generate a list of ALL expressions
 * of depth at most [n], using constants from a list [l] and operators from a
 * list [ops]. *)

(** Appends [op x y] to [acc] for every [op] in [ops]. *)
Fixpoint apply_ops (x y : Z) ops (acc : list Z) :=
  match ops with
    | op :: ops' =>
      apply_ops x y ops' ((op x y) :: acc)
    | nil => acc
  end.

(** Appends [op x y] to [acc] for every [y] in [ys] and every [op] in [ops]. *)
Fixpoint map_ops (x : Z) ys ops (acc : list Z) :=
  match ys with
    | y :: ys' =>
      map_ops x ys' ops (apply_ops x y ops acc)
    | nil => acc
  end.

(** Appends [op x y] to [acc] for every [x] in [xs], every [y] in [ys] and
 * every [op] in [ops]. *)
Fixpoint gen_expr_step xs ys ops acc :=
  match xs with
    | x :: xs' =>
      gen_expr_step xs' ys ops (map_ops x ys ops acc)
    | nil => acc
  end.

(** Iterates [gen_expr_step] on list [l] with operators from list [ops]. *)
Fixpoint gen_expr' l ops (n : nat) acc :=
  match n with
    | 0%nat => acc
    | S k =>
      gen_expr' l ops k (gen_expr_step l acc ops acc)
  end.
Definition gen_expr l ops n :=
  rev' (gen_expr' l ops n l).

(** Tries to solve an existential goal by exhaustive search from the list
 * [l] of instanciation candidates and finishing the work with tactic [tac]. *)
Ltac exists_from_list l tac :=
  match l with
    | ?x :: ?xs =>
      (exists x; now tac) || exists_from_list xs tac
    | _  => now tac
  end.

(** Tries to solve the current goals by exhaustive search, from the lists
 * [l] of constants and [ops] of operators. It generates expressions using at
 * most [n] operators and finishes the job with tactic [tac]. *)
Ltac exists_bruteforce l ops n tac :=
  let ls :=
      eval unfold gen_expr, gen_expr', gen_expr_step, map_ops, apply_ops,
      rev', rev_append in (gen_expr l ops n) in
      idtac ls.
(*      exists_from_list ls tac.*)



Tactic Notation "decide" constr(x) "=" constr(y) :=
  destruct (Z.eq_dec x y); subst; simpl in *.

(** * Automation for verification conditions *)


Ltac prove_vc l ops n :=
  try (progress step);
  match goal with
    | [ |- _ <= _ ] => nia
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      (lhs; now prove_vc l ops n)
        || (rhs; now prove_vc l ops n)
    | [ |- exists _, _] =>
      exists_bruteforce l ops n ltac:(prove_vc l ops n)
  end.
