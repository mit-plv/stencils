(* ========================================================================== *
 * Stencils                                                                   *
 * ========================================================================== *)

Require Import Main.Sets.
Require Import ZArith.
Local Open Scope Z_scope.

(* ========================================================================== *)
Module Type CELL.

  (** A space is defined by a type [Cell.t]... *)
  Parameter t : Type.

  (** ... with decidable equality... *)
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.

  (** ... and a group operation to be interpreted as translation.  *)
  Parameter add : t -> t -> t.
  Parameter minus : t -> t.
  Parameter zero : t.
  Parameter add_assoc : forall x y z, add x (add y z) = add (add x y) z.
  Parameter add_comm : forall x y, add x y = add y x.
  Parameter add_minus : forall x, add x (minus x) = zero.
  Parameter unit_left : forall x, add zero x = x.

  (** This may seem arbitrary--why not having two different types, one for
   * "points" and one for "translations"?  In fact, stencil code is almost
   * always executed on powers of [Z] or powers of modular integers.  This
   * captures both cases, while still being very simple. *)

  (** [expr A] is meant to be the type of expressions of type [Cell.t],
   * assuming that the type of arithmetic expressions is [A]. Similarly,
   * [eval A ev e] should denote the value of type [Cell.t] represented by
   * expression [e], assuming that the type of arithmetic expressions is [A]
   * and that [ev A ea] is the value of arithmetic expression [ea] in the
   * current context.
   *
   * [eval_ext] is a proof that [eval] depends only on the values returned by
   * the arithmetic evaluator. *)
  Parameter expr : Type -> Type.
  Parameter eval : forall A (ev : A -> Z), expr A -> t.
  Parameter eval_ext :
    forall A (ev ev' : A -> Z),
      (forall a, ev a = ev' a) -> forall e, eval A ev e = eval A ev' e.

End CELL.

(* ========================================================================== *)
Module CellNotations (Cell : CELL).

  (** Just a few straightforward notations for translations in any stencil
   * space. *)

  Delimit Scope group_scope with grp.

  Notation "a + b" :=
    (Cell.add a b) (at level 50, left associativity) : group_scope.
  Notation "a - b" :=
    (Cell.add a (Cell.minus b)) (at level 50, left associativity) : group_scope.
  Notation "0" := Cell.zero : group_scope.

End CellNotations.

(* ========================================================================== *)
Module Type STENCIL (Cell : CELL).

  (* XXX: Documentation *)

  Parameter space : set Cell.t.
  Parameter pattern : list Cell.t.
  Parameter center : Cell.t.

End STENCIL.
