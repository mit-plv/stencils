Require Import List Sets Monoids Stencils.
Local Open Scope set_scope.
Import ListNotations.

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

Section VN1D.
  Variables n : nat.

  Definition VN1D := VonNeumann1D (2 * n) n.

  Lemma compute_row :
    forall a b c d t,
      a <= b < 2 * n -> 1 + t <= n - 1 ->
      c = 1 + a -> b = 1 + d ->
      valid VN1D (〚a, b〛 × ⎨t⎬)
            (〚a, b〛 × ⎨t⎬ ∪〚c, d〛 × ⎨1+t⎬).
  Proof.
  Admitted.

(*  Lemma compute_row :
    forall a b t,
      a <= b < 2 * n -> 1 + t <= n - 1 ->
      valid VN1D (〚a, 1+b〛 × ⎨t⎬)
            (〚a, 1+b〛 × ⎨t⎬ ∪〚1+a, b〛 × ⎨1+t⎬).
  Proof.
    intros.
    unfold valid, closure.
    eexists; split.
    image with 1; reflexivity.
    unfold iter_next, next.
    eexists; split.
    image with (〚a, 1+b〛 × ⎨t⎬); intuition.
    image with (〚1+a, b〛 × ⎨1+t⎬).
    2: reflexivity.
    intros x Hx.
    split.
    + unfold sp, space, VN1D, VonNeumann1D, nb_iter.
      admit. (* arithmetics tactic *)
    + intros.
      inversion H2; clear H2; subst.
      unfold pattern, center, sp, nb_iter, space, VN1D, VonNeumann1D
        in *.
      inversion H3; clear H3; subst.
    - admit. (* arithmetics, again *)
    - inversion H2; clear H2; subst.
      * admit. (* again *)
      * inversion H3; clear H3; subst.
        admit. (* last one! *)
        inversion H2.
  Qed.*)

  Definition valid_strategy :
    valid VN1D ∅ (sp VN1D).
  Proof.
    unfold VN1D at 2; unfold sp, space, VonNeumann1D, nb_iter.

    apply seq with (⋃ ⎨〚i, 2 * n - 1 - i〛× ⎨i⎬, i ∈ 〚0, n - 1〛⎬).
    apply loop.
    + omega.
    + unfold valid, closure.
      eexists; split.
      image with 1; reflexivity.
      unfold iter_next, next.
      eexists; split.
      image with (∅ : set (nat*nat)); intuition.
      eexists; split.
      2: rewrite empty_bin_union; reflexivity.
      sets simpl; repeat intro.
      split.
      unfold sp, space, VN1D, VonNeumann1D.
      admit. (* set theory tactic here *)
      intros.
      inversion H1; sets simpl.
      admit. (* arithmetics tactic here *)
    + intros.
      rewrite <- union_segment by omega.
      apply focus with (〚k, 2 * n - 1 - k〛 × ⎨k⎬).
      apply compute_row; try omega.
      reflexivity.
      admit. (* arithmetics + fix *)
      repeat intro.
      union with k; destruct x; simpl in *.
      destruct H0; simpl in *.
      destruct H0, H1; subst; omega.
      destruct H0; simpl in *.
      destruct H1; subst.
      now left.
      destruct H1.
    +
  Abort.

End VN1D.