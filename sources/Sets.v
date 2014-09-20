(* ========================================================================= *)
(* Sets                                                                      *)
(* ========================================================================= *)

Require Import List.

Delimit Scope set_scope with set.
Local Open Scope set_scope.

Definition set (U : Type) :=
  U -> Prop.

Definition is_in {U} (x : U) (A : set U) :=
  A x.
Infix "∈" := is_in (at level 70, no associativity) : set_scope.

Definition subset {U} (A B : set U) :=
  forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70, no associativity) : set_scope.

Definition same {U} (A B : set U) :=
  forall x, x ∈ A <-> x ∈ B.
Infix "≡" := same (at level 70, no associativity) : set_scope.

Lemma mutual_inclusion : forall U (A B : set U), A ⊆ B -> B ⊆ A -> A ≡ B.
Proof. intros; split; intuition. Qed.

Definition empty (U : Type) : set U :=
  fun _ => False.
Notation "∅" := (empty _) : set_scope.

Definition full (U : Type) : set U :=
  fun _ => True.
Notation "⟨ U ⟩" := (full U) : set_scope.

Definition finite {U} (l : list U) : set U :=
  fun x => In x l.
Notation "⎨ x ; .. ; y ⎬" :=
  (finite (cons x .. (cons y nil) ..))
    (at level 0, x at next level, y at next level): set_scope.

(*Inductive union {U} (A : set (set U)) : set U :=
| union_ax : forall x y, x ∈ A -> y ∈ x -> y ∈ (union A).*)
Definition union {U} (A : set (set U)) : set U :=
  fun y => exists x, x ∈ A /\ y ∈ x.
Notation "⋃ A" := (union A) (at level 35) : set_scope.
Infix "∪" :=
  (fun A B => ⋃ ⎨A; B⎬) (at level 40, left associativity) : set_scope.

Definition powerset {U} (B : set U) : set (set U) := fun A => A ⊆ B.
Notation "'℘' A" := (powerset A) (at level 35) : set_scope.

(*Inductive extension {U} (A : set U) (P : U -> Prop) : set U :=
| extension_ax : forall x, x ∈ A -> P x -> x ∈ extension A P.*)
Definition extension {U} (A : set U) (P : U -> Prop) : set U :=
  fun x => x ∈ A /\ P x.
Notation "⎨ x ∈ A | P ⎬" :=
  (extension A (fun x => P))
    (at level 0, x at next level, A at next level, P at next level) : set_scope.

(*Inductive image {U V} (A : set U) (f : U -> V) : set V :=
| image_ax : forall x, x ∈ A -> f x ∈ image A f.*)
Definition image {U V} (A : set U) (f : U -> V) : set V :=
  fun y => exists x, x ∈ A /\ y = f x.
Notation "⎨ e , x ∈ A ⎬" :=
  (image A (fun x => e))
    (at level 0, x at next level, A at next level, e at next level) : set_scope.

(*Inductive times {U V} (A : set U) (B : set V) : set (U * V) :=
| times_ax : forall x y, x ∈ A -> y ∈ B -> (x, y) ∈ times A B.*)
Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => fst p ∈ A /\ snd p ∈ B.
Infix "×" := times (at level 39, left associativity) : set_scope.

Definition segment (x y : nat) : set nat :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" := (segment x y) (at level 0) : set_scope.