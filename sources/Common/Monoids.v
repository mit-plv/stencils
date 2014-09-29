(* ========================================================================= *)
(* Monoids                                                                   *)
(* ========================================================================= *)

Require Import Omega.

Delimit Scope monoid_scope with monoid.
Open Scope monoid_scope.

(** One of the most important properties of stencils is their translation
 * invariance.  We shall focus on commutative monoids, where the sum
 * operation is meant to represent translations.  This slightly more abstract
 * setting gives the opportunity to deal with slightly more exotic spaces,
 * e.g., with toroidal topology. *)

Class CommMonoid {A : Type} (add : A -> A -> A) (zero : A) : Prop :=
{
  add_assoc : forall x y z, add x (add y z) = add (add x y) z;
  add_comm : forall x y, add x y = add y x;
  unit_left : forall x, add zero x = x
}.

(** Trivial projections, to get nicer notations. *)
Section proj.
  Generalizable Variables A add zero.

  Definition add_proj `{c : CommMonoid A add zero} :=
    add.
  Definition zero_proj `{c : CommMonoid A add zero} :=
    zero.
End proj.

Notation "a + b" :=
  (add_proj a b) (at level 50, left associativity) : monoid_scope.
Notation "0" := zero_proj : monoid_scope.

(** We will mostly be working with low-dimensional powers of [nat], which are
 * defined by a few instances down below. *)

Section CommMonoid_prod.
  Generalizable Variables A B addA addB zeroA zeroB.
  Context `(CommMonoid A addA zeroA) `(CommMonoid B addB zeroB).

  Definition add_prod : A * B -> A * B -> A * B :=
    fun p1 p2 => (addA (fst p1) (fst p2), addB (snd p1) (snd p2)).

  Definition zero_prod : A * B :=
    (zeroA, zeroB).

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

Instance nat1 : CommMonoid plus O.
Proof. constructor; intros; omega. Qed.

Instance nat2 : CommMonoid add_prod zero_prod :=
  CommMonoid_prod nat1 nat1.

Instance nat3 : CommMonoid add_prod zero_prod :=
  CommMonoid_prod nat2 nat1.