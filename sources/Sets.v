(* From the standard library. *)
Require Import ZArith.
Local Open Scope Z_scope.

(** * Set theory
 *
 * A fragment of set theory using predicates.  This file contains definitions
 * and notations.  Automation is provided in Automation.v, while properties are
 * proved in SetsFacts.v.
 *)

Definition set U := U -> Prop.

(** Membership predicate. *)
Inductive is_in {U} : U -> set U -> Prop :=
  Is_in : forall x (A : set U), A x -> is_in x A.
Infix "∈" := is_in (at level 70, no associativity) : set_scope.
Local Open Scope set_scope.

(** Set inclusion. *)
Definition subset {U} (A B : set U) : Prop :=
  forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70, no associativity) : set_scope.

(** Set equivalence.  In SetsFacts.v, we register it as a setoid, with an
 * associated database of rewriting rules. *)
Definition same {U} (A B : U -> Prop) :=
  forall x, x ∈ A <-> x ∈ B.
Infix "≡" := same (at level 79, no associativity) : set_scope.

(** Empty sets. *)
Definition empty {U} : set U := fun _ : U => False.
Notation "∅" := (@empty _) : set_scope.

(** Singletons. *)
Definition singleton {U} (x : U) : set U := fun y => y = x.
Notation "⎨ a ⎬" := (singleton a) : set_scope.

(** Sets of the form { n integer | a <= n <= b }. *)
Definition segment (x y : Z) : set Z :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" :=
  (segment x y) (at level 0, format "'〚' x ','  '/' y '〛'") : set_scope.

(** Cartesian product. *)
Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => (fst p ∈ A /\ snd p ∈ B).
Infix "×" := times (at level 39, left associativity) : set_scope.

(** Binary unions. *)
Definition bin_union {U} (A B : set U) : set U :=
  fun x => x ∈ A \/ x ∈ B.
Infix "∪" := bin_union (at level 41, right associativity) : set_scope.

(** Union of a family of sets indexed by integers [n] such that
 * [a <= n <= b]. *)
Definition param_union {U} (a b : Z) (X : Z -> set U) :=
  fun x => exists i, a <= i <= b /\ x ∈ X i.
Notation "⋃ ⎨ A , k ∈ 〚 a , b 〛 ⎬" :=
  (param_union a b (fun k => A))
    (at level 0, k at next level, A at next level) : set_scope.