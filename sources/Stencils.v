(* ========================================================================= *)
(* Stencils                                                                  *)
(* ========================================================================= *)

Require Import Sets Monoids List.
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
  Context `{St : @Stencil _ _ _ M}.
  Local Open Scope monoid.

  (** The actual spacetime into which the stencil code is executed. *)

  Definition group := set (cell * time).
  Definition sp : group :=
    space ×〚 0, nb_iter-1 〛.

  (** Dependency relation between two cells in [real_space]. *)

  Inductive neighbor : (cell * time) -> (cell * time) -> Prop :=
  | Neighb :
      forall (n c : cell) (t : time),
(*        (c + n) ∈ space -> (c + center) ∈ space ->*)
        In n pattern -> neighbor (c + n, t) (c + center, 1+t).
  Notation "c1 → c2" := (neighbor c1 c2) (at level 80).

  (** One-step closure *)

  Definition boundary (B : group) : group :=
    ⎨y ∈ sp | forall x, x ∈ sp -> x → y -> x ∈ B⎬.

  Definition next (CC : set group) : set group :=
    ⋃ ⎨⎨B ∪ P, P ∈ ℘ (boundary B)⎬, B ∈ CC⎬.

  (** Infinite-time closure *)

  Fixpoint iter_next (CC : set group) (n : nat) : set group :=
    match n with
      | 0 => CC
      | S k => next (iter_next CC k)
    end.

  Definition closure (CC : set group) : set group :=
    ⋃ ⎨iter_next CC n, n ∈ ⟨nat⟩⎬.

  (** XXX: Describe this system. *)

  Definition valid (A B : group) : Prop :=
    B ∈ closure ⎨A⎬.

  (** XXX: I do not believe these proofs should be fully automated yet.  It
   * would be nice to have a few tactics to make the process smoother, though.
   *)

  Lemma boundary_bin_union :
    forall P Q A B, P ⊆ boundary A -> Q ⊆ boundary B ->
                    P ∪ Q ⊆ boundary A ∪ boundary B.
  Proof.
    unfold boundary; intros P Q A B HP HQ.
  Admitted.

  Lemma next_monotonic :
    forall (CC DD : set group),
      CC ⊆ DD -> next CC ⊆ next DD.
  Proof.
    intros.
    unfold subset; intros.
    unfold next in *.
    destruct H0.
    exists x0; intuition.
    destruct H1.
    exists x1; intuition.
  Qed.

  (** XXX: This is ugly! *)
  Lemma next_extensive :
    forall CC, CC ⊆ next CC.
  Proof.
    intros. unfold next.
    eexists.
    split.
    exists x.
    split; auto.
    exists ∅.
    split.
    repeat intro; destruct H0.
    apply same_eq.
    unfold union.
    split.
    intros.
    exists x; intuition.
    now constructor.
    intros.
    destruct H0.
    destruct H0.
    destruct H0; subst.
    auto.
    destruct H0; subst.
    destruct H1.
    destruct H0.
  Qed.

  Definition union_closed {U} (CC : set (set U)) :=
    forall A B, A ∈ CC -> B ∈ CC -> A ∪ B ∈ CC.

  Lemma next_union_closed :
    forall CC, union_closed CC -> union_closed (next CC).
  Proof.
    intros.
    intros A B Ha Hb.
    unfold next.
    eexists; split.
  Admitted.

  Lemma iter_in :
    forall A CC, A ∈ CC -> forall k, iter_next ⎨A⎬ k ⊆ iter_next CC k.
  Proof.
    intros A CC H; induction k.
    unfold iter_next, subset.
    intros. destruct H0; subst.
    intuition.
    destruct H0.
    simpl.
    now apply next_monotonic.
  Qed.

  Lemma iter_morphism :
    forall m n CC, iter_next CC (n + m) = iter_next (iter_next CC n) m.
  Proof.
    induction m.
    simpl; intuition.
    intros.
    replace (n + S m)%nat with (S (n + m)) by omega; simpl.
    now rewrite IHm.
  Qed.

  Lemma iter_union_closed :
    forall CC, union_closed CC -> forall n, union_closed (iter_next CC n).
  Proof.
    induction n; simpl.
    * assumption.
    * now apply next_union_closed.
  Qed.

  Lemma iter_le :
    forall n m CC, n <= m -> iter_next CC n ⊆ iter_next CC m.
  Proof.
  Admitted.

  (** XXX: This should be in the set library. *)
  Lemma is_in_subset :
    forall U x (A B : set U), x ∈ A -> A ⊆ B -> x ∈ B.
  Proof. intuition. Qed.

  Lemma seq_weak {A B C} : valid A B -> valid B C -> valid A C.
  Proof.
    intros Hb Hc.
    unfold valid, closure.
    destruct Hb as [? [[nb [? ?]] ?]]; subst.
    destruct Hc as [? [[nc [? ?]] ?]]; subst.
    exists (iter_next ⎨A⎬ (nb + nc)).
    split. exists (nb + nc); intuition.
    apply is_in_subset with (iter_next ⎨B⎬ nc).
    assumption.
    rewrite iter_morphism.
    now apply iter_in.
  Qed.

  Lemma valid_weaken {A B} C : valid A B -> valid (C ∪ A) B.
  Proof.
  Admitted.

  Lemma par {A B C} : valid A B -> valid A C -> valid A (B ∪ C).
  Proof.
    intros Hb Hc.
    unfold valid, closure.
    destruct Hb as [? [[nb [? ?]] ?]]; subst.
    destruct Hc as [? [[nc [? ?]] ?]]; subst.
    eexists; split.
    exists (max nb nc).
    split. intuition.
    reflexivity.
    apply iter_union_closed.
    * admit.
    * eapply is_in_subset; [eassumption|].
      apply iter_le.
      apply Max.le_max_l.
    * eapply is_in_subset; [eassumption|].
      apply iter_le.
      apply Max.le_max_r.
  Qed.

  Lemma valid_bin_union {A B} : valid A B -> valid A (A ∪ B).
  Proof.
  Admitted.

  Lemma seq {A B C} : valid A B -> valid B C -> valid A (A ∪ B ∪ C).
  Proof.
    intros.
    apply valid_bin_union in H.
    apply valid_weaken with A in H0.
    apply (@seq_weak A (A ∪ B)).
    assumption.
(*    now apply valid_bin_union.
  Qed.*)
  Admitted.

End Refinement.