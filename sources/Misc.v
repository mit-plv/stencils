Require Import Relations Omega.

Lemma nat_le_ind :
  forall P,
    reflexive nat P -> transitive nat P ->
    (forall n, P n (S n)) ->
    forall n m, n <= m -> P n m.
Proof.
  intros.
  assert (forall k, P n (n + k)).
  + induction k.
    * now rewrite <- plus_n_O.
    * replace (n + S k) with (S (n + k)) by omega.
      unfold transitive in H0.
      now apply H0 with (n + k).
  + replace m with (n + (m - n)) by omega.
    now apply H3.
Qed.

Lemma refl_trans_finite_weak :
  forall U (R : relation U),
    reflexive U R -> transitive U R ->
    forall f a k,
      (forall n, a <= n < a + k -> R (f n) (f (S n))) ->
      R (f a) (f (a + k)).
Proof.
  intros U R HR HT f a; induction k; intros.
  - rewrite <- plus_n_O.
    now apply HR.
  - apply HT with (f (a + k)).
    * apply IHk.
      intros; apply H; omega.
    * replace (a + S k) with (S (a + k)) by omega.
      apply H; omega.
Qed.

Lemma refl_trans_finite :
  forall U (R : relation U),
    reflexive U R -> transitive U R ->
    forall f a b,
      a <= b -> (forall n, a <= n < b -> R (f n) (f (S n))) ->
      R (f a) (f b).
Proof.
  intros. replace b with (a + (b - a)) in * by omega.
  now apply refl_trans_finite_weak.
Qed.