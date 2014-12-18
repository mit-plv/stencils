Require Import ZArith.

Require Import Expressions Programs.

(** A few classical domains, to reduce the boilerplate to be written by the
 * end-user. *)

Module Z1 <: DOMAIN.

  Definition cell := Z.
  Definition cexpr := aexpr.
  Definition ceval (v : vars) (c : cexpr) : cell :=
    (aeval v c).
  Definition csimpl (c : cexpr) :=
    (asimpl c).

End Z1.

Module Z2 <: DOMAIN.

  Definition cell := (Z * Z)%type.
  Definition cexpr := (aexpr * aexpr)%type.
  Definition ceval (v : vars) (c : cexpr) : cell :=
    (aeval v (fst c), aeval v (snd c)).
  Definition csimpl (c : cexpr) :=
    (asimpl (fst c), asimpl (snd c)).

End Z2.

Module Z3 <: DOMAIN.

  Definition cell := (Z * Z * Z)%type.
  Definition cexpr := (aexpr * aexpr * aexpr)%type.
  Definition ceval (v : vars) (c : cexpr) : cell :=
    (aeval v (fst (fst c)), aeval v (snd (fst c)), aeval v (snd c)).
  Definition csimpl (c : cexpr) :=
    (asimpl (fst (fst c)), asimpl (snd (fst c)), asimpl (snd c)).

End Z3.

Module Z4 <: DOMAIN.

  Definition cell := (Z * Z * Z * Z)%type.
  Definition cexpr := (aexpr * aexpr * aexpr * aexpr)%type.
  Definition ceval (v : vars) (c : cexpr) : cell :=
    (aeval v (fst (fst (fst c))), aeval v (snd (fst (fst c))),
     aeval v (snd (fst c)), aeval v (snd c)).
  Definition csimpl (c : cexpr) :=
    (asimpl (fst (fst (fst c))), asimpl (snd (fst (fst c))),
     asimpl (snd (fst c)), asimpl (snd c)).

End Z4.
