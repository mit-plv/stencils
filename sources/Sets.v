Require Import ZArith Setoid Morphisms.
Local Open Scope Z_scope.

(** A fragment of set theory using predicates. *)

Definition set U := U -> Prop.

Inductive is_in {U} : U -> set U -> Prop :=
  Is_in : forall x (A : set U), A x -> is_in x A.
Infix "∈" := is_in (at level 70, no associativity) : set_scope.
Local Open Scope set_scope.

(** Set equivalence.  We register it as a setoid, with an associated database of
 * rewriting rules, proved later on. *)

Definition same {U} (A B : U -> Prop) :=
  forall x, x ∈ A <-> x ∈ B.
Infix "≡" := same (at level 79, no associativity) : set_scope.

Instance same_E : forall {U}, Equivalence (@same U).
Proof. firstorder. Qed.

Instance same_is_in_Proper :
  forall U, Proper (eq ==> same ==> iff) (@is_in U).
Proof.
  unfold Proper, respectful.
  split; intros; subst; firstorder.
Qed.

(** Basic constructors and notations. *)

Definition empty {U} : set U := fun _ : U => False.
Notation "∅" := (@empty _) : set_scope.

Definition singleton {U} (x : U) : set U := fun y => y = x.
Notation "⎨ a ⎬" := (singleton a) : set_scope.

Definition segment (x y : Z) : set Z :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" :=
  (segment x y) (at level 0, format "'〚' x ','  '/' y '〛'") : set_scope.

Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => (fst p ∈ A /\ snd p ∈ B).
Infix "×" := times (at level 39, left associativity) : set_scope.

Definition bin_union {U} (A B : set U) : set U :=
  fun x => x ∈ A \/ x ∈ B.
Infix "∪" := bin_union (at level 41, right associativity) : set_scope.

Definition param_union {U} (a b : Z) (X : Z -> set U) :=
  fun x => exists i, a <= i <= b /\ x ∈ X i.
Notation "⋃ ⎨ A , k ∈ 〚 a , b 〛 ⎬" :=
  (param_union a b (fun k => A))
    (at level 0, k at next level, A at next level)
  : set_scope.

(* The following tactics are meant for internal use only. *)

Ltac inv H := inversion H; subst; clear H.
Ltac set_reasoning :=
  match goal with
    | [ H : @is_in _ _ (@empty _) |- _ ] => inv H
    | [ H : @is_in _ _ (@singleton _ _) |- _ ] => inv H
    | [ H : @is_in _ _ (@segment _ _) |- _ ] => inv H
    | [ H : @is_in _ _ (@bin_union _ _ _) |- _ ] => inv H
    | [ H : @is_in _ _ (@times _ _ _ _) |- _ ] => inv H
    | [ H : @is_in _ _ (@param_union _ _ _ _) |- _ ] => inv H

    | [ H : @empty _ _ |- _] => inversion H
    | [ H : @singleton _ _ _ |- _ ] => red in H
    | [ H : @segment _ _ _ |- _ ] => red in H
    | [ H : @bin_union _ _ _ _ |- _ ] => red in H
    | [ H : @times _ _ _ _ _ |- _ ] => destruct H
    | [ H : @param_union _ _ _ _ _ |- _ ] => destruct H as [? [? ?]]

    | [ |- @is_in _ _ (@singleton _ _) ] =>
      constructor; red
    | [ |- @is_in _ _ (@segment _ _) ] =>
      constructor; split
    | [ |- @is_in _ (@pair _ _ _ _) (@times _ _ _ _) ] =>
      constructor; split
    | [ |- @is_in _ _ (@param_union _ _ _ _) ] =>
      constructor; red

    | [ H : @same _ ?A _ |- _ ∈ ?A ] => now apply H
    | [ H : @same _ _ ?A |- _ ∈ ?A ] => now apply H
  end.

Ltac fst_order :=
  match goal with
    | [ |- forall _, _ ] => intro
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ |- _ <-> _ ] => split
    | [ |- ~ _ ] => intro

    | [ x : @prod _ _ |- _ ] => destruct x
    | [ |- @pair _ _ _ _ = @pair _ _ _ _ ] => f_equal
  end.

Ltac double_incl :=
  match goal with
    | [ |- @same _ _ _ ] => intro
  end.

(** [step] does set theoretic reasoning.  [lhs] and [rhs] allow one to prove
 * that an element belongs to a binary union, by proving that it belongs to one
 * of the two given sets. *)

Ltac lhs :=
  match goal with
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      constructor; left
  end.

Ltac rhs :=
  match goal with
    | [ |- @is_in _ _ (@bin_union _ _ _) ] =>
      constructor; right
  end.

Ltac step :=
  repeat progress first [assumption | reflexivity |
                         fst_order | set_reasoning | double_incl].

Ltac step' :=
  (repeat progress first [lhs; now step' | rhs; now step' | step]);
  try firstorder.

(** The main rewriting system.  We prove compatibility of set theoretic operations
 * with [same] and prove a few identities, which are bundled in the [sets]
 * rewriting hints database. *)

Instance same_bin_union_Proper :
  forall U, Proper (same ==> same ==> same) (@bin_union U).
Proof.
  unfold Proper, respectful; step'.
Qed.

Instance same_times_Proper :
  forall U V, Proper (same ==> same ==> same) (@times U V).
Proof.
  unfold Proper, respectful; step.
Qed.

Instance same_param_union_Proper :
  forall U a b, Proper (pointwise_relation _ same ==> same) (@param_union U a b).
Proof.
  unfold Proper, respectful, pointwise_relation.
  step; exists x1; step; now apply H.
Qed.

Lemma bin_union_empty_l :
  forall U (A : set U), ∅ ∪ A ≡ A.
Proof. step'. Qed.
Hint Rewrite bin_union_empty_l : set_setoid.

Lemma bin_union_empty_r :
  forall U (A : set U), A ∪ ∅ ≡ A.
Proof. step'. Qed.
Hint Rewrite bin_union_empty_r : set_setoid.

Lemma bin_union_idem :
  forall U (A : set U), A ∪ A ≡ A.
Proof. step'. Qed.
Hint Rewrite bin_union_idem : set_setoid.

Lemma times_empty_l :
  forall U V (A : set V), (∅ : set U) × A ≡ ∅.
Proof. step. Qed.
Hint Rewrite times_empty_l : set_setoid.

Lemma times_empty_r :
  forall U V (A : set U), A × (∅ : set V) ≡ ∅.
Proof. step. Qed.
Hint Rewrite times_empty_r : set_setoid.

Lemma param_union_singleton :
  forall a b, ⋃⎨⎨k⎬, k ∈〚a, b〛⎬ ≡ 〚a, b〛.
Proof.
  step; [now subst | now subst | ].
  exists x; step.
Qed.
Hint Rewrite param_union_singleton : set_setoid.

Lemma param_union_singleton_l :
  forall U (B : set U) a b, ⋃ ⎨ ⎨k⎬ × B, k ∈〚a, b〛⎬ ≡ 〚a, b〛× B.
Proof.
  step.
  unfold fst, snd in *; now subst.
  unfold fst, snd in *; now subst.
  exists z; step.
Qed.
Hint Rewrite param_union_singleton_l : set_setoid.

Lemma param_union_singleton_r :
  forall U (A : set U) a b, ⋃ ⎨ A × ⎨k⎬, k ∈〚a, b〛⎬ ≡ A ×〚a, b〛.
Proof.
  step.
  unfold fst, snd in *; now subst.
  unfold fst, snd in *; now subst.
  exists z; step.
Qed.
Hint Rewrite param_union_singleton_r : set_setoid.

Tactic Notation "simplify" "sets" "with" reference(l) :=
  unfold l; simpl;
  repeat
    first
    [ setoid_rewrite bin_union_empty_l
    | setoid_rewrite bin_union_empty_r
    | setoid_rewrite bin_union_idem
    | setoid_rewrite times_empty_l
    | setoid_rewrite times_empty_r
    | setoid_rewrite param_union_singleton
    | setoid_rewrite param_union_singleton_l
    | setoid_rewrite param_union_singleton_r].

Lemma param_union_bin :
  forall U a b (A : Z -> set U),
    a <= b -> ⋃ ⎨ A k, k ∈〚a, b〛⎬ ≡ ⋃ ⎨ A k, k ∈〚a, b-1〛⎬ ∪ A b.
Proof.
  step.
  + destruct Z.eq_dec with x0 b; subst; [rhs | lhs]; step.
  exists x0; step; omega.
  + (exists x0; step; omega).
  + (exists b; step; omega).
Qed.

Lemma bin_union_assoc :
  forall U (A B C : set U), (A ∪ B) ∪ C ≡ A ∪ (B ∪ C).
Proof. step'. Qed.

(*Parameter U : Type.
Parameter A : set U.
Parameter x : U*U.

Goal x ∈ A × A -> x ∈ ((∅ × ∅ ∪ ∅) ∪ (∅ ∪ (A × ∅ ∪ ∅))) ∪ A × A.
intro; autorewrite with sets.
Abort.*)