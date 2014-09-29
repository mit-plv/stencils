(* ========================================================================= *)
(* Sets                                                                      *)
(* ========================================================================= *)

Require Import List Omega.

Delimit Scope set_scope with set.
Local Open Scope set_scope.

Definition set (U : Type) :=
  U -> Prop.


(** Membership, subsets, set equivalence and an extensionality axiom *)

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


(** Empty and full set.  Finite sets *)

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


(** Set-theoretic and binary union *)

Definition union {U} (A : set (set U)) : set U :=
  fun y => exists x, x ∈ A /\ y ∈ x.
Notation "⋃ A" := (union A) (at level 35) : set_scope.

Definition bin_union {U} (A B : set U) :=
  fun x => A x \/ B x.
Infix "∪" := bin_union (at level 41, right associativity) : set_scope.


(** Power set and cartesian product *)

Definition powerset {U} (B : set U) : set (set U) :=
  fun A => A ⊆ B.
Notation "'℘' A" := (powerset A) (at level 35) : set_scope.

Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => fst p ∈ A /\ snd p ∈ B.
Infix "×" := times (at level 39, right associativity) : set_scope.


(** Sets defined by extension.  Image of a set through a mapping *)

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


(** Integer segments *)

Definition segment (x y : nat) : set nat :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" := (segment x y) (at level 0) : set_scope.


(** A couple tactics to deal with set-theoretic proofs.  They are intended to be
 * used with firstorder. *)

(** Definition unfolding in goals. *)

Tactic Notation "sets" "red" :=
  match goal with
    | [ |- @is_in _ _ _ ]  => red
    | [ |- @subset _ _ _ ] => do 2 intro
    | [ |- _ ] => idtac
  end.

(** Equality/equivalence in goals *)

Tactic Notation "set" "eq" "simpl" :=
  match goal with
    | [ |- _ = _ ] => apply same_eq; split
    | [ |- @same _ _ _ ] => split
  end.

(** Membership in goals *)

Tactic Notation "sets" "simpl" :=
  repeat
    (sets red;
     match goal with
       | [ |- @empty _ _ ] =>
         change False
       | [ |- @full _ _ ] =>
         now red
       | [ |- @powerset _ ?B ?A ] =>
         change (A ⊆ B)
       | [ |- @finite _ _ _ ] =>
         unfold finite, is_in, In; simpl
       | [ |- @extension _ _ _ _ ] =>
         split
       | [ |- @segment _ _ _ ] =>
         unfold segment, is_in; try omega
       | [ |- @times _ _ _ _ _ ] =>
         split; simpl
     end).

Tactic Notation "image" "with" constr(x) :=
  progress
    (sets red;
     match goal with
       | [ |- @image _ _ _ _ _] => exists x; split; [sets simpl|]
     end).

Lemma union_image :
  forall U V (A : set U) f (y : V) z, z ∈ A -> y ∈ f z -> y ∈ (⋃⎨f x, x ∈ A⎬).
Proof.
  firstorder.
  eexists; split; [|eassumption].
  now image with z.
Qed.

Tactic Notation "union" "with" constr(x) :=
  progress
    (sets red;
     match goal with
       | [ |- @union _ _ _ ] =>
         apply union_image with x;
         sets simpl;
         try assumption
       | [ |- @union _ _ _ ] =>
         exists x;
         split;
         sets simpl;
         [|try assumption]
     end).


(** Propositions *)

Lemma mutual_inclusion : forall U (A B : set U), A ⊆ B -> B ⊆ A -> A ≡ B.
Proof. firstorder. Qed.

Lemma bin_union_l :
  forall U (A B : set U) (x : U), x ∈ A -> x ∈ A ∪ B.
Proof. firstorder. Qed.

Lemma bin_union_r :
  forall U (A B : set U) (x : U), x ∈ B -> x ∈ A ∪ B.
Proof. firstorder. Qed.

Lemma is_in_subset :
  forall U x (A B : set U), x ∈ A -> A ⊆ B -> x ∈ B.
Proof. firstorder. Qed.

Lemma union_subset :
  forall U (P Q A : set U), P ⊆ A -> Q ⊆ A -> P ∪ Q ⊆ A.
Proof. firstorder. Qed.

Lemma union_twice :
  forall U (A : set U), A ∪ A = A.
Proof. intros; set eq simpl; firstorder. Qed.

Lemma union_assoc :
  forall U (A B C : set U), (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof. intros; set eq simpl; firstorder. Qed.

Lemma union_comm :
  forall U (A B : set U), A ∪ B = B ∪ A.
Proof. intros; set eq simpl; firstorder. Qed.

Lemma empty_bin_union :
  forall U (A : set U), ∅ ∪ A = A.
Proof. intros; set eq simpl; firstorder. Qed.

Lemma union_segment :
  forall V (f : nat -> set V) a b,
    a <= b ->
    (⋃ ⎨f x , x ∈〚a, b〛⎬) ∪ (f (1+b)) = (⋃ ⎨f x , x ∈〚a, 1+b〛⎬).
Proof.
  intros; set eq simpl; firstorder.
  union with (f (1 + b)).
  image with (1 + b); firstorder omega.
  destruct eq_nat_dec with x1 (1 + b); subst; firstorder.
  left; union with (f x1).
  image with x1; firstorder omega.
Qed.

Lemma union_singleton :
  forall U (f : nat -> set U) a,
    (⋃⎨f i, i ∈ (〚a, a〛)⎬) = f a.
Proof.
  intros.
  apply same_eq; split; intros.
  destruct H as [? [[X [[? ?] ?]] ?]].
  assert (a = X) by omega; now subst.
  union with a.
Qed.