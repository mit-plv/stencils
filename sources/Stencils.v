(* ========================================================================= *)
(* Stencils                                                                  *)
(* ========================================================================= *)

Require Import Sets Monoids Misc.
Require Import List.
Import ListNotations.
Local Open Scope set_scope.

Definition time := nat.

(** XXX: Describe this data structure. *)

Class Stencil {cell : Type} {add : cell -> cell -> cell} {zero : cell}
  `(CommMonoid cell add zero) :=
{
  space : set cell;
  nb_iter : time;
  pattern : list cell;
  center : cell
}.

Section Refinement.
  Generalizable Variables cell add zero.
  Context `{M : CommMonoid cell add zero}.
  Context `(St : @Stencil _ _ _ M).
  Local Open Scope monoid.

  (** The actual spacetime into which the stencil code is executed. *)

  Definition group := set (cell * time).
  Definition sp : group :=
    space ×〚 0, nb_iter-1 〛.

  (** Dependency relation between two cells in [sp]. *)

  Inductive depends : (cell * time) -> (cell * time) -> Prop :=
  | Depends :
      forall (n c : cell) (t : time),
        In n pattern -> depends (c + n, t) (c + center, 1+t).
  Notation "c1 → c2" := (depends c1 c2) (at level 80).

  (** Here is the main, abstract formulation of correctness:
   *
   *  - For a group of cells [B], [boundary B] is the immediate neighborhood of
   * [B], that is, the set of those cells whose value can be computed provided
   * that the values of all cells in [B] are known;
   *  - [next] describes valid computation steps.  For a given collection of
   * sets [CC], [next CC] is the collection of those sets for which there is a
   * valid scheduling of computations from at least one set in [CC];
   *  - [iter_next CC n] is the collection of those sets that can be reached
   * from some set in [CC] after [n] (valid) steps;
   *  - [closure CC] is the collection of those sets that can be reached from
   * some set in [CC] after any finite number of steps.
   *
   *   Finally, the [valid] predicates captures the following idea: [valid A B]
   * holds if and only if there exists a correct scheduling of computations
   * allowing to go from [A] to [B].
   *)

  Definition boundary (B : group) : group :=
    (⎨y ∈ sp | forall x, x ∈ sp -> x → y -> x ∈ B⎬).

  Definition next (CC : set group) : set group :=
    ⋃ ⎨⎨B ∪ P, P ∈ ℘ (boundary B)⎬, B ∈ CC⎬.

  Fixpoint iter_next (CC : set group) (n : nat) : set group :=
    match n with
      | 0 => CC
      | S k => next (iter_next CC k)
    end.

  Definition closure (CC : set group) : set group :=
    ⋃ ⎨iter_next CC n, n ∈ ⟨nat⟩⎬.

  Definition valid (A B : group) : Prop :=
    B ∈ closure ⎨A⎬.

  (** A bunch of intermediate results used in the main combinators described
   * below.  The details should be irrelevant for most readers. *)

  Definition union_closed {U} (CC : set (set U)) :=
    forall A B, A ∈ CC -> B ∈ CC -> A ∪ B ∈ CC.

  (** Level 0: Proofs about [boundary]. *)

  Lemma boundary_bin_union :
    forall P Q A B, P ⊆ boundary A -> Q ⊆ boundary B ->
                    P ∪ Q ⊆ boundary (A ∪ B).
  Proof. firstorder. Qed.

  (** Level 1: Proofs about [next]. *)

  Lemma next_monotonic :
    forall (CC DD : set group),
      CC ⊆ DD -> next CC ⊆ next DD.
  Proof. firstorder. Qed.

  Lemma next_extensive :
    forall CC, CC ⊆ next CC.
  Proof.
    unfold next, subset; intros.
    union with x.
    image with (∅ : set (cell * time)); firstorder.
    apply same_eq; firstorder.
  Qed.

  Lemma next_union_closed :
    forall CC, union_closed CC -> union_closed (next CC).
  Proof.
    intros.
    intros A B Ha Hb.
    unfold next in *.
    destruct Ha as [xa [[P [HP1 HP2]] Ha]]; subst.
    destruct Ha as [R [HR1 HR2]]; subst.
    destruct Hb as [xb [[Q [HQ1 HQ2]] Hb]]; subst.
    destruct Hb as [T [HT1 HT2]]; subst.
    union with (P ∪ Q). firstorder.
    replace ((P ∪ R) ∪ Q ∪ T) with ((P ∪ Q) ∪ (R ∪ T)).
    image with (R ∪ T); firstorder.
    (* XXX: This should be some monoid tactic.  This is inefficient. *)
    apply same_eq; firstorder.
  Qed.

  Lemma next_subset :
    forall CC A,
      (forall B, B ∈ CC -> A ⊆ B) -> forall B, B ∈ next CC -> A ⊆ B.
  Proof.
    intros.
    destruct H0 as [? [[G1 [? ?]] ?]]; subst.
    destruct H2 as [G2 [? ?]]; subst.
    specialize (H _ H0); firstorder.
  Qed.

  (** Level 2: Proofs about [iter_next]. *)

  Lemma iter_in :
    forall A CC, A ∈ CC -> forall k, iter_next ⎨A⎬ k ⊆ iter_next CC k.
  Proof.
    intros A CC H; induction k.
    + unfold iter_next, subset.
      firstorder; now subst.
    + firstorder.
  Qed.

  Lemma iter_morphism :
    forall m n CC, iter_next CC (n + m) = iter_next (iter_next CC n) m.
  Proof.
    induction m.
    + simpl; firstorder.
    + intros; replace (n + S m)%nat with (S (n + m)) by omega; simpl.
      now rewrite IHm.
  Qed.

  Lemma iter_union_closed :
    forall CC, union_closed CC -> forall n, union_closed (iter_next CC n).
  Proof.
    induction n; simpl.
    + assumption.
    + now apply next_union_closed.
  Qed.

  Lemma iter_le :
    forall n m, n <= m -> forall CC, iter_next CC n ⊆ iter_next CC m.
  Proof.
    apply (nat_le_ind
             (fun n m =>
                forall (CC : set group), iter_next CC n ⊆ iter_next CC m)).
    + firstorder.
    + firstorder.
    + intros; simpl; now apply next_extensive.
  Qed.

  Lemma iter_subset :
    forall CC A n,
      (forall B, B ∈ CC -> A ⊆ B) -> forall B, B ∈ iter_next CC n -> A ⊆ B.
  Proof.
    induction n.
    + firstorder.
    + intros.
      apply next_subset with (iter_next CC n); [firstorder|assumption].
  Qed.

  Lemma iter_bin_union :
    forall n A B C,
      A ⊆ C -> B ∈ iter_next ⎨A⎬ n -> C ∪ B ∈ iter_next ⎨C⎬ n.
  Proof.
    induction n; intros.
    + simpl in *.
      destruct H0; subst.
      rewrite union_comm.
      rewrite <- (subset_bin_union _ B C); firstorder.
      destruct H0.
    + simpl in *.
      destruct H0 as [? [[G1 [? ?]] ?]]; subst.
      specialize (IHn _ _ C H H0).
      unfold next. union with (C ∪ G1).
      destruct H2 as [G2 [? ?]]; subst.
      image with (G2 ∖ C).
      firstorder.

      rewrite <- union_assoc.
      repeat rewrite (union_comm _ C G1).
      repeat rewrite union_assoc.
      now rewrite (diff_bin_union _ C G2).
  Qed.

  (** Level 4: Combinators. *)

  Lemma seq {A C} B : valid A B -> valid B C -> valid A C.
  Proof.
    intros Hb Hc.
    unfold valid, closure.
    destruct Hb as [? [[nb [? ?]] ?]]; subst.
    destruct Hc as [? [[nc [? ?]] ?]]; subst.

    union with (nb + nc).
    apply is_in_subset with (iter_next ⎨B⎬ nc); [assumption|].
    rewrite iter_morphism.
    now apply iter_in.
  Qed.

  Lemma split {A B C} : valid A B -> valid A C -> valid A (B ∪ C).
  Proof.
    intros Hb Hc.
    unfold valid, closure.
    destruct Hb as [? [[nb [? ?]] ?]]; subst.
    destruct Hc as [? [[nc [? ?]] ?]]; subst.

    union with (max nb nc).
    apply iter_union_closed.
    + unfold union_closed; intros x y [?|?] [?|?]; firstorder.
      subst x y; left.
      now rewrite union_twice.
    + eapply is_in_subset; [eassumption|].
      apply iter_le.
      apply Max.le_max_l.
    + eapply is_in_subset; [eassumption|].
      apply iter_le.
      apply Max.le_max_r.
  Qed.

  Lemma focus' A B C :
    valid A B -> A ⊆ C -> valid C (C ∪ B).
  Proof.
    unfold valid, closure; intros.
    destruct H as [? [[nb [? ?]] ?]]; subst.
    union with nb.
    now apply iter_bin_union with A.
  Qed.

  Lemma focus A B C :
    valid A (A ∪ B) -> A ⊆ C -> valid C (C ∪ B).
  Proof.
    intros H HA.
    generalize (focus' A (A ∪ B) C H HA); intro H'.
    rewrite <- union_assoc in H'.
    replace (C ∪ A) with C in H'.
    assumption.
    apply same_eq; firstorder.
  Qed.

  Lemma nop {A} : valid A A.
  Proof.
    unfold valid, closure.
    union with (0 : nat); firstorder.
  Qed.

  Lemma loop' {A B f} :
    forall a b,
      a <= b -> (f a) = A -> (f b) = B ->
      (forall i, a <= i < b -> valid (f i) (f (1+i))) -> valid A B.
  Proof.
    intros.
    rewrite <- H0, <- H1.
    apply refl_trans_finite; try assumption.
    intro; apply nop.
    repeat intro; now apply @seq with y.
  Qed.

  Lemma loop {A B}:
    forall a b,
      a <= b ->
      valid A (B a) ->
      (forall k, a <= k < b ->
                 valid (⋃ ⎨B i, i ∈〚a, k〛⎬)
                       (⋃ ⎨B i, i ∈〚a, 1+k〛⎬)) ->
      valid A (⋃ ⎨B i, i ∈〚a, b〛⎬).
  Proof.
    intros.
    apply (seq (B a)); [assumption|].
    apply
      (@loop' (B a) _  (fun k => ⋃⎨B i, i ∈〚a, k 〛⎬) a b);
      try firstorder.
    apply union_singleton.
  Qed.
End Refinement.