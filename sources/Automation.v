Require Import List ZArith Psatz.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Sets.

Ltac inv H := inversion H; subst; clear H.

Tactic Notation "decide" constr(x) "=" constr(y) :=
  destruct (Z.eq_dec x y); subst; simpl in *.

(** * First automation layer: Simplifying goals. *)

Ltac simplify_hyps :=
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

      | [ x : @prod _ _ |- _ ] => destruct x

      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ \/ _ |- _ ] => destruct H
end.

Ltac simplify_goal' :=
  match goal with
    | [ |- @subset _ _ _ ] => intro

    | [ |- @is_in _ _ (@singleton _ _) ] =>
      constructor; red
    | [ |- @is_in _ _ (@segment _ _) ] =>
      constructor; split
    | [ |- @is_in _ (@pair _ _ _ _) (@times _ _ _ _) ] =>
      constructor; split
    | [ |- @is_in _ _ (@param_union _ _ _ _) ] =>
      constructor; red

    | [ H : @same _ ?A _ |- @is_in _ _ ?A ] => now apply H
    | [ H : @same _ _ ?A |- @is_in _ _ ?A ] => now apply H

    | [ |- forall _, _ ] => intro
    | [ |- _ /\ _ ] => split
    | [ |- _ <-> _ ] => split
    | [ |- ~ _ ] => intro

    | [ x : @prod _ _ |- _ ] => destruct x
    | [ |- @pair _ _ _ _ = @pair _ _ _ _ ] => f_equal
  end.

Ltac simplify_goal :=
  repeat progress simplify_goal'.

Ltac double_incl := match goal with [ |- @same _ _ _ ] => intro end.

Ltac forward :=
  repeat
    first [assumption | reflexivity |
           progress simplify_goal | progress simplify_hyps | double_incl].

(** [step] does set theoretic reasoning.  [lhs] and [rhs] allow one to prove
 * that an element belongs to a binary union, by proving that it belongs to one
 * of the two given sets. *)

Ltac lhs :=
  match goal with
    [ |- @is_in _ _ (@bin_union _ _ _) ] => constructor; left
  end.

Ltac rhs :=
  match goal with
      [ |- @is_in _ _ (@bin_union _ _ _) ] => constructor; right
  end.

Ltac forward' :=
  repeat first [lhs; now forward' | rhs; now forward' |
                progress forward].

(** * Bruteforce pass-or-fail automation. *)

Ltac iter_exists l tac :=
  match l with
    | ?x :: ?xs =>
      (exists x; tac) || iter_exists xs tac
  end.

(* [bruteforce' l] tries to solve the current goal.  If needed, it
 * instanciates existential variables using the variables provided in [l]. *)

Ltac bruteforce' l :=
  simplify_hyps;
  match goal with
    | [ |- @subset _ _ _ ] => intro; bruteforce' l

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

(** * Generating all expressions from a list of constants. *)

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
