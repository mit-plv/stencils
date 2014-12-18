Require Import ZArith Setoid Morphisms.
Local Open Scope Z_scope.
Require Import Sets Automation.
Local Open Scope set_scope.

(** The main rewriting system.  We prove compatibility of set theoretic operations
 * with [same] and prove a few identities, which are bundled in the [sets]
 * rewriting hints database. *)

Instance same_E : forall {U}, Equivalence (@same U).
Proof. firstorder. Qed.

Instance same_is_in_Proper :
  forall U, Proper (eq ==> same ==> iff) (@is_in U).
Proof.
  unfold Proper, respectful.
  split; intros; subst; firstorder.
Qed.

Instance subset_is_in_Proper :
  forall U, Proper (same ==> same ==> iff) (@subset U).
Proof. unfold Proper, respectful; firstorder. Qed.

Instance same_bin_union_Proper :
  forall U, Proper (same ==> same ==> same) (@bin_union U).
Proof. unfold Proper, respectful. forward'. Qed.

Instance same_times_Proper :
  forall U V, Proper (same ==> same ==> same) (@times U V).
Proof. unfold Proper, respectful; forward. Qed.

Instance same_param_union_Proper :
  forall U a b, Proper (pointwise_relation _ same ==> same) (@param_union U a b).
Proof.
  unfold Proper, respectful, pointwise_relation.
  forward; exists x1; forward; now apply H.
Qed.

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
  forward.
  + decide x0=b; subst; [rhs | lhs]; forward.
  exists x0; forward; omega.
  + (exists x0; forward; omega).
  + (exists b; forward; omega).
Qed.

Lemma bin_union_assoc :
  forall U (A B C : set U), (A ∪ B) ∪ C ≡ A ∪ (B ∪ C).
Proof. forward'. Qed.