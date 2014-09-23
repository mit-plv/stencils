Require Import List Sets Monoids Stencils.
Local Open Scope set_scope.
Import ListNotations.

(** Let us define a few classical stencils that are used in practice. *)

Section ClassicalStencils.
  Variables n m : nat.
  Variable T : nat.

  Instance VonNeumann1D : Stencil nat1 :=
  {
    space   := 〚0, n-1〛;
    nb_iter := T;
    pattern := [0; 1; 2];
    center  := 1
  }.

  Instance VonNeumann2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    nb_iter := T;
    pattern := [(0,1); (1,1); (2,1); (1,0); (1,2)];
    center  := (1,1)
  }.

  Instance Moore2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    nb_iter := T;
    pattern := [(0,0); (0,1); (0,2);
                (1,0); (1,1); (1,2);
                (2,0); (2,1); (2,2)];
    center  := (1,1)
  }.
End ClassicalStencils.

Section VN1D.
  Variables n : nat.

  Definition VN1D := VonNeumann1D (2 * n) n.
  Definition valid_strategy :
    valid VN1D ∅ (sp VN1D).

    unfold VN1D at 2; unfold sp, space, VonNeumann1D, nb_iter.

    (*apply seq with (⋃ ⎨〚i, 2 * n - 1 - i〛× ⎨i⎬, i ∈ 〚0, n - 1〛⎬).*)
  Abort.
End VN1D.