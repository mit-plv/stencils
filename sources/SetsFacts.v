(* From the standard library. *)
Require Import ZArith Setoid Morphisms.
Local Open Scope Z_scope.

(* From StLib. *)
Require Import Sets Automation.
Local Open Scope set_scope.

(** * A few facts in set theory.
 *
 * This is the main rewriting system.  We prove compatibility of set theoretic
 * operations with [same] and prove a few identities, which are bundled in the
 * [sets] rewriting hints database. *)

(** ** Compatibility of relations and operations with set equivalence. *)

(** [same] is an equivalence relation. *)
Instance same_E : forall {U}, Equivalence (@same U).
Proof. firstorder. Qed.

(** The membership relation is compatible with [same]. *)
Instance same_is_in_Proper :
  forall U, Proper (eq ==> same ==> iff) (@is_in U).
Proof.
  unfold Proper, respectful.
  split; intros; subst; firstorder.
Qed.

(** The inclusion relation is compatible with [same]. *)
Instance subset_is_in_Proper :
  forall U, Proper (same ==> same ==> iff) (@subset U).
Proof. unfold Proper, respectful; firstorder. Qed.

(** A binary union is unchanged if we replace any of its sets with an equivalent
 * one. *)
Instance same_bin_union_Proper :
  forall U, Proper (same ==> same ==> same) (@bin_union U).
Proof. unfold Proper, respectful. forward'. Qed.

(** Similarly, a Cartesian product is unchanged if we replace any of its sets
 * with an equivalent one. *)
Instance same_times_Proper :
  forall U V, Proper (same ==> same ==> same) (@times U V).
Proof. unfold Proper, respectful; forward. Qed.

(** Given a family of sets indexed by integers [n] such that [a <= n <= b], the
 * associated parametric union is unchanged if any set in the family is
 * replaced with an equivalent one. *)
Instance same_param_union_Proper :
  forall U a b, Proper (pointwise_relation _ same ==> same) (@param_union U a b).
Proof.
  unfold Proper, respectful, pointwise_relation.
  forward; exists x1; forward; now apply H.
Qed.

(** ** Simplification rules and lemmas. *)

Lemma bin_union_empty_l :
  forall U (A : set U), ∅ ∪ A ≡ A.
Proof. forward'. Qed.
Hint Rewrite bin_union_empty_l : set_setoid.

Lemma bin_union_empty_r :
  forall U (A : set U), A ∪ ∅ ≡ A.
Proof. forward'. Qed.
Hint Rewrite bin_union_empty_r : set_setoid.

Lemma bin_union_idem :
  forall U (A : set U), A ∪ A ≡ A.
Proof. forward'. Qed.
Hint Rewrite bin_union_idem : set_setoid.

Lemma times_empty_l :
  forall U V (A : set V), (∅ : set U) × A ≡ ∅.
Proof. forward. Qed.
Hint Rewrite times_empty_l : set_setoid.

Lemma times_empty_r :
  forall U V (A : set U), A × (∅ : set V) ≡ ∅.
Proof. forward. Qed.
Hint Rewrite times_empty_r : set_setoid.

Lemma param_union_singleton :
  forall a b, ⋃⎨⎨k⎬, k ∈〚a, b〛⎬ ≡ 〚a, b〛.
Proof.
  forward; [now subst | now subst | ].
  exists x; forward.
Qed.
Hint Rewrite param_union_singleton : set_setoid.

Lemma param_union_singleton_l :
  forall U (B : set U) a b, ⋃ ⎨ ⎨k⎬ × B, k ∈〚a, b〛⎬ ≡ 〚a, b〛× B.
Proof.
  forward.
  unfold fst, snd in *; now subst.
  unfold fst, snd in *; now subst.
  exists z; forward.
Qed.
Hint Rewrite param_union_singleton_l : set_setoid.

Lemma param_union_singleton_r :
  forall U (A : set U) a b, ⋃ ⎨ A × ⎨k⎬, k ∈〚a, b〛⎬ ≡ A ×〚a, b〛.
Proof.
  forward.
  unfold fst, snd in *; now subst.
  unfold fst, snd in *; now subst.
  exists z; forward.
Qed.
Hint Rewrite param_union_singleton_r : set_setoid.

(** The following lemma is very useful in For loops, when performing exactly
 * one step. *)
Lemma param_union_bin :
  forall U a b (A : Z -> set U),
    a <= b -> ⋃ ⎨ A k, k ∈〚a, b〛⎬ ≡ ⋃ ⎨ A k, k ∈〚a, b-1〛⎬ ∪ A b.
Proof.
  forward.
  + decide x0=b; subst; [rhs | lhs]; forward.
  exists x0; forward; omega.
  + (exists x0; forward; omega).
  + (exists b; forward; omega).
Qed.

(** Most properties of set-theoretic operations are handled automatically by the
 * automation provided in Automation.v, but binary union associativity is
 * explicitely used in a manual proof. *)
Lemma bin_union_assoc :
  forall U (A B C : set U), (A ∪ B) ∪ C ≡ A ∪ (B ∪ C).
Proof. forward'. Qed.

(** One more easy lemma about binary unions used in a manual proof. *)
Lemma bin_union_snd_third :
  forall U (A B C : set U), (A ∪ B) ∪ C ≡ (A ∪ C) ∪ B.
Proof. forward; bruteforce. Qed.

Lemma equiv_incl :
  forall U (A B : set U), A ≡ B -> A ⊆ B.
Proof. forward. Qed.


(** ** Automation for set simplification. *)
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
