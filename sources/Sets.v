(* ========================================================================= *)
(* Sets                                                                      *)
(* ========================================================================= *)


Require Import List.

Delimit Scope set_scope with set.
Local Open Scope set_scope.





(** * Definitions *)

Definition set (U : Type) :=
  U -> Prop.


(** ** Membership, subsets, set equivalence and an extensionality axiom *)

Definition is_in {U} (x : U) (A : set U) :=
  A x.
Infix "∈" := is_in (at level 70, no associativity) : set_scope.

Definition subset {U} (A B : set U) :=
  forall x, x ∈ A -> x ∈ B.
Infix "⊆" := subset (at level 70, no associativity) : set_scope.

Definition same {U} (A B : set U) :=
  forall x, x ∈ A <-> x ∈ B.
Infix "≡" := same (at level 70, no associativity) : set_scope.
Axiom same_eq :
  forall U (A B : set U), A ≡ B -> A = B.


(** ** Empty and full set.  Finite sets *)

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


(** ** Set-theoretic and binary union *)

Definition union {U} (A : set (set U)) : set U :=
  fun y => exists x, x ∈ A /\ y ∈ x.
Notation "⋃ A" := (union A) (at level 35) : set_scope.

Definition bin_union {U} (A B : set U) :=
  ⋃ ⎨A; B⎬.
Infix "∪" := bin_union (at level 41, right associativity) : set_scope.


(** ** Power set and cartesian product *)

Definition powerset {U} (B : set U) : set (set U) := fun A => A ⊆ B.
Notation "'℘' A" := (powerset A) (at level 35) : set_scope.

Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => fst p ∈ A /\ snd p ∈ B.
Infix "×" := times (at level 39, right associativity) : set_scope.


(** ** Sets defined by extension.  Image of a set through a mapping *)

Definition extension {U} (A : set U) (P : U -> Prop) : set U :=
  fun x => x ∈ A /\ P x.
Notation "⎨ x ∈ A | P ⎬" :=
  (extension A (fun x => P))
    (at level 0, x at next level, A at next level, P at next level) : set_scope.

Definition image {U V} (A : set U) (f : U -> V) : set V :=
  fun y => exists x, x ∈ A /\ y = f x.
Notation "⎨ e , x ∈ A ⎬" :=
  (image A (fun x => e))
    (at level 0, x at next level, A at next level, e at next level) : set_scope.


(** ** Integer segments *)

Definition segment (x y : nat) : set nat :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" := (segment x y) (at level 0) : set_scope.





(** * Propositions *)

Lemma mutual_inclusion : forall U (A B : set U), A ⊆ B -> B ⊆ A -> A ≡ B.
Proof. intros; split; intuition. Qed.

Lemma bin_union_l :
  forall U (A B : set U) (x : U), x ∈ A -> x ∈ A ∪ B.
Proof.
  intros; exists A; split; [now left | assumption].
Qed.

Lemma bin_union_r :
  forall U (A B : set U) (x : U), x ∈ B -> x ∈ A ∪ B.
Proof.
  intros; exists B; split; [now (right; left) | assumption].
Qed.





(** * Tactics *)

Tactic Notation "mutual" "inclusion" :=
  match goal with
    | [ |- _ = _ ] => apply same_eq, mutual_inclusion
    | [ |- @same _ _ _ ] => apply mutual_inclusion
  end.

Tactic Notation "mem" "simpl" :=
  repeat match goal with
           | [ |- @is_in _ _ (@empty _) ] =>
             change False
           | [ |- @is_in _ _ (@full _) ] =>
             now red
           | [ |- @is_in _ ?A (@powerset _ ?B) ] =>
             change (A ⊆ B)
           | [ |- @is_in _ _ (@finite _ _) ] =>
             unfold finite, is_in, In; simpl
           | [ |- @is_in _ _ (@extension _ _ _) ] =>
             split
           | [ |- @is_in _ _ (@segment _ _) ] =>
             unfold segment, is_in
           | [ |- @is_in _ _ (@times _ _ _ _) ] =>
             split; simpl
         end.

Tactic Notation "union" "left" :=
  match goal with
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      apply bin_union_l; mem simpl
  end.

Tactic Notation "union" "right" :=
  match goal with
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      apply bin_union_r; mem simpl
  end.

Tactic Notation "union" "with" constr(x) :=
  match goal with
    | [ |- @is_in _ _ (@union _ _) ] => exists x; split; mem simpl
  end.

Tactic Notation "image" "with" constr(x) :=
  match goal with
    | [ |- @is_in _ _ (@image _ _ _ _)] => exists x; split; [mem simpl|]
  end.