(* ========================================================================= *)
(* Stencils                                                                  *)
(* ========================================================================= *)

Require Import Common.Sets Common.Monoids.

Definition time := nat.

(** XXX: Describe this data structure. *)

Class Stencil {cell : Type} {add : cell -> cell -> cell} {zero : cell}
  `(CommMonoid cell add zero) :=
{
  space : set cell;
  nb_iter : time;
  pattern : list cell;
  center : cell
}.