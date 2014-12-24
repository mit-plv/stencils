(* From StLib. *)
Require Import Expressions Sets.

(** A domain is defined by:
 *  - [cell], a type representing cells.
 *  - [cexpr], a type representing expressions of type [cell].
 *  - [ceval], a function which evaluates a cell expression in a given
 *    environment and returns a [cell].
 *  - [csimpl], which simplifies [cexpr] objects by evaluating constants.
 *
 * Notice than when defining a new domain, all the definitions and functions
 * from Expression.v (e.g., [aeval] and [asimpl]) can be used. *)

Module Type DOMAIN.

  Parameter cell : Type.
  Parameter cexpr : Type.
  Parameter ceval : vars -> cexpr -> cell.
  Parameter csimpl : cexpr -> cexpr.

End DOMAIN.

(** A problem on a given domain is defined by:
 *  - [space], a subset of the set of cells, that we need to work in.
 *  - [dep], which maps any cell expression to the list of cells (or, more
 *    accurately, of the cell expressions corresponding to the cells) it
 *    depends on. *)

Module Type PROBLEM (D : DOMAIN).

  Export D.

  Parameter space : set cell.
  Parameter dep : cexpr -> list cexpr.

End PROBLEM.
