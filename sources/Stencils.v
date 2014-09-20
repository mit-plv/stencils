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

(** Let us define a few classical stencils that are used in practice. *)

Section ClassicalStencils.
  Variables n m : nat.
  Variable T : nat.

  Instance VonNeumann1D : Stencil nat1 :=
  {
    space   := 〚0, n-1〛;
    nb_iter := T;
    pattern := [0; 1; 2];
    center  := 1
  }.

  Instance VonNeumann2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    nb_iter := T;
    pattern := [(0,1); (1,1); (2,1); (1,0); (1,2)];
    center  := (1,1)
  }.

  Instance Moore2D : Stencil nat2 :=
  {
    space   := 〚0, n-1〛×〚0, m-1〛;
    nb_iter := T;
    pattern := [(0,0); (0,1); (0,2);
                (1,0); (1,1); (1,2);
                (2,0); (2,1); (2,2)];
    center  := (1,1)
  }.
End ClassicalStencils.

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

  Lemma par {A B C} : valid A B -> valid A C -> valid A (B ∪ C).
  Proof.
  Admitted.

  Lemma seq {A B C} : valid A B -> valid B C -> valid A (B ∪ C).
  Proof.
  Admitted.

End Refinement.