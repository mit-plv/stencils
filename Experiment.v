Require Import Omega.
Require Import List.
Import ListNotations.

(** Let us start by defining the domains on which our stencil codes will
 * operate.  One of the most important properties of stencils is their
 * translation-invariance.  It is therefore natural to restrict ourselves
 * to commutative monoids.  It also gives the opportunity to deal with
 * slightly more exotic spaces, e.g., with toroidal topology. *)

Class CommMonoid {A : Type} (add : A -> A -> A) (zero : A) : Prop :=
{
  add_assoc : forall x y z, add x (add y z) = add (add x y) z;
  add_comm : forall x y, add x y = add y x;
  unit_left : forall x, add zero x = x
}.

(** Trivial projections, to get nicer notations. *)
Section proj.
  Generalizable Variables A add zero.
  Context `{CommMonoid A add zero}.

  Definition add_proj := add.
  Definition zero_proj := zero.
End proj.

Notation "a + b" :=
  (add_proj a b)
  (at level 50, left associativity) : monoid.
Notation "0" := zero_proj : monoid.

(** We will mostly be working with low-dimensional powers of [nat], which are
 * defined by a few instances below. *)

Section CommMonoid_prod.
  Generalizable Variables A B addA addB zeroA zeroB.
  Context `(CommMonoid A addA zeroA) `(CommMonoid B addB zeroB).

  Definition add_prod : A * B -> A * B -> A * B :=
    fun p1 p2 => (addA (fst p1) (fst p2), addB (snd p1) (snd p2)).

  Definition zero_prod : A * B := (zeroA, zeroB).

  Instance CommMonoid_prod : CommMonoid add_prod zero_prod.
  Proof.
    unfold add_prod, zero_prod; constructor; intros;
    repeat match goal with
             | [ H : CommMonoid _ _ |- _ ] => destruct H; clear H
             | [ p : prod _ _ |- _ ] => destruct p; simpl in *
             | [ H : forall _ _ _, _ |- _ ] => rewrite H; clear H
             | [ H : forall _, _ |- _ ] => rewrite H; clear H
             | [ |- _ ] => reflexivity
           end.
  Qed.
End CommMonoid_prod.

Instance nat1 : CommMonoid plus 0.
Proof. constructor; intros; omega. Qed.

Instance nat2 : CommMonoid add_prod zero_prod :=
  CommMonoid_prod nat1 nat1.

Instance nat3 : CommMonoid add_prod zero_prod :=
  CommMonoid_prod nat2 nat1.





(** Commutative monoids are used to describe the sell in which a given stencil
 * lives.  Now, we define a notion of shapes.  A [shape] is simply a set of
 * objects of a given type, defined by a predicate.  Two shapes are equivalent
 * if they define the same set.
 * We define basic shapes, called segments.  Intuitively, a [segment] encodes
 * a subset of [nat] of the form [{n : nat | x <= n <= b}].  We also define a
 * simple combinator [times], corresponding to the cartesian product.
 *)

Definition shape (A : Type) := A -> Prop.

Definition same {A : Type} (s1 s2 : shape A) : Prop :=
  forall x, s1 x <-> s2 x.

Definition singleton {A : Type} (x : A) : shape A :=
  fun y => y = x.

Definition segment (x y : nat) : shape nat :=
  fun n => x <= n <= y.

Definition union {A : Type} (s1 s2 : shape A) : shape A :=
  fun x => s1 x \/ s2 x.

Definition times {A B : Type} (s1 : shape A) (s2 : shape B) : shape (A * B) :=
  fun p => s1 (fst p) /\ s2 (snd p).

Infix "≡" := same (at level 85) : shape.
Notation "〈 x 〉" := (singleton x) (at level 65) : shape.
Notation "〚 x , y 〛" := (segment x y) (at level 70) : shape.
Notation "s1 ∪ s2" := (union s1 s2) (at level 75) : shape.
Notation "s1 × s2" := (times s1 s2) (at level 75) : shape.
Local Open Scope shape.





(** Stencils *)

Class Stencil {cell : Type} {add : cell -> cell -> cell} {zero : cell}
  `(CommMonoid cell add zero) :=
{
  space : shape cell;
  pattern : list cell;
  centre : cell
}.

Section Dependencies.
  Generalizable Variables cell add zero.
  Context `{M : CommMonoid cell add zero}.
  Context `{S : @Stencil _ _ _ M}.
  Local Open Scope monoid.

  (** XXX: I cannot use the [+] notation here?! *)
  Inductive neighbor : cell -> cell -> Prop :=
    | Neighb :
      forall n c : cell,
        In n pattern -> neighbor (add c n) (add c centre).



(** PLAYGROUND *)

Check 〚 1, 2 〛×〚 3, 5 〛≡〚 1, 2 〛×〚 3, 5 〛.

Section ClassicalStencils.
  Variables n m k : nat.

  Instance VonNeumann2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    pattern := [(0,1); (1,1); (2,1); (1,0); (1,2)];
    center  := (1,1)
  }.

  Instance Moore2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    pattern := [(0,0); (0,1); (0,2);
                (1,0); (1,1); (1,2);
                (2,0); (2,1); (2,2)];
    center  := (1,1)
  }.
End ClassicalStencils.
