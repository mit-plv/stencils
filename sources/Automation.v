Require Import List ZArith.
Require Import Psatz.
Import ListNotations.
Local Open Scope Z_scope.

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


(** ******************************************************************** *)

Tactic Notation "decide" constr(x) "=" constr(y) :=
  destruct (Z.eq_dec x y); subst; simpl in *.

Ltac inv H := inversion H; subst; clear H.

Ltac simplify_set_hyps :=
  repeat
    match goal with
      | [ H : @is_in _ _ (@empty _) |- _ ] => inv H
      | [ H : @is_in _ _ (@singleton _ _) |- _ ] => inv H
      | [ H : @is_in _ _ (@segment _ _) |- _ ] => inv H
      | [ H : @is_in _ _ (@bin_union _ _ _) |- _ ] => inv H
      | [ H : @is_in _ _ (@times _ _ _ _) |- _ ] => inv H
      | [ H : @is_in _ _ (@param_union _ _ _ _) |- _ ] => inv H

      | [ H : @empty _ _ |- _] => inversion H
      | [ H : @singleton _ _ _ |- _ ] => red in H
      | [ H : @segment _ _ _ |- _ ] => red in H
      | [ H : @bin_union _ _ _ _ |- _ ] => red in H
      | [ H : @times _ _ _ _ _ |- _ ] => destruct H
      | [ H : @param_union _ _ _ _ _ |- _ ] => destruct H as [? [? ?]]
    end.

Ltac iter_exists l tac :=
  match l with
    | ?x :: ?xs =>
      (exists x; tac) || iter_exists xs tac
  end.

Ltac bruteforce' l :=
  simplify_set_hyps;
  match goal with
    | [ |- @is_in _ _ (@singleton _ _) ] =>
      constructor; red; bruteforce' l
    | [ |- @is_in _ _ (@segment _ _) ] =>
      constructor; split; bruteforce' l
    | [ |- @is_in _ (@pair _ _ _ _) (@times _ _ _ _) ] =>
      constructor; split; bruteforce' l
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      (lhs; bruteforce' l) || (rhs; bruteforce' l)
    | [ |- @is_in _ _ (@param_union _ _ _ _) ] =>
      constructor; red; bruteforce' l

    | [ |- forall _, _ ] =>
      intro; bruteforce' l
    | [ |- exists _, _ ] =>
      iter_exists l ltac:(bruteforce' l)
    | [ |- ~ _ ] =>
      intro; bruteforce' l
    | [ |- _ /\ _ ] =>
      split; bruteforce' l
    | [ |- _ \/ _ ] =>
      (left; bruteforce' l) || (right; bruteforce' l)
    | [ H : _ \/ _ |- _ ] =>
      destruct H; bruteforce' l

    | [ |- False ] =>
      simpl in *; nia
    | [ |- _ <= _ ] =>
      simpl in *; nia
    | [ |- _ = _ ] =>
      simpl in *; nia
    | [ |- _ = _ ] =>
      progress f_equal; bruteforce' l
  end.

Ltac bruteforce :=
  bruteforce' ([] : list Z).
