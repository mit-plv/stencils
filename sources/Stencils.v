(* ========================================================================= *)
(* Stencils                                                                  *)
(* ========================================================================= *)

Require Import Sets Monoids List.
Import ListNotations.
Local Open Scope set_scope.

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

Section Refinement.
  Generalizable Variables cell add zero.
  Context `{M : CommMonoid cell add zero}.
  Context `{St : @Stencil _ _ _ M}.
  Local Open Scope monoid.

  (** The actual spacetime into which the stencil code is executed. *)
  
  Definition sp : set (cell * time) :=
    space ×〚 0, nb_iter-1 〛.

  (** Dependency relation between two cells in [real_space]. *)
  
  Inductive neighbor : (cell * time) -> (cell * time) -> Prop :=
  | Neighb :
      forall (n c : cell) (t : time),
        space (c + n) -> space (c + center) ->
        In n pattern -> neighbor (c + n, t) (c + center, 1+t).

  Notation "c1 → c2" := (neighbor c1 c2) (at level 80).

  (** XXX: Describe this system. *)
  
  Definition group := set (cell * time).

  (** One-step closure *)

  Definition boundary (B : group) : group :=
    ⎨y ∈ sp | forall x, x ∈ sp -> x → y -> x ∈ B⎬.

  Definition next (CC : set group) : set group :=
    ⋃ ⎨⎨B ∪ P, P ∈ ℘ (boundary B)⎬, B ∈ CC⎬.

  (** Infinite-time closure *)

  Fixpoint iter_next (CC : set group) (n : nat) : set group :=
    match n with
      | 0 => CC
      | S k => next (iter_next CC k)
    end.

  Definition closure (CC : set group) : set group :=
    ⋃ ⎨iter_next CC n, n ∈ ⟨nat⟩⎬.

  Definition valid (A B : group) : Prop :=
    B ∈ closure ⎨A⎬.

End Refinement.