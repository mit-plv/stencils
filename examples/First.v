Require Import StLib.Core.

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
  Hypothesis n_gt_1 : n > 1.

  Definition VN1D := VonNeumann1D (2 * n) n.

  Check (Spawn Node i ∈〚0, n〛
               With
               Compute 〚0, 0〛× ⎨i⎬).

  Lemma compute_row :
    forall a b c d t,
      a <= b < 2 * n -> 1 + t <= n - 1 ->
      c = 1 + a -> b = 1 + d ->
      valid VN1D (〚a, b〛 × ⎨t⎬)
            (〚a, b〛 × ⎨t⎬ ∪〚c, d〛 × ⎨1+t⎬).
  Proof.
    intros; unfold valid, closure.
    union with 1; simpl.
    unfold next.
    union with (〚a, b〛 × ⎨t⎬).
    left; set eq simpl; firstorder.
    image with (〚c, d 〛 × ⎨1 + t⎬).
    unfold boundary.
    sets red; sets simpl.

    + unfold sp, space, nb_iter, VN1D, VonNeumann1D.
      destruct x; firstorder; simpl in *; subst; unfold add_proj in *; omega.

    + intros.
      inversion H5; clear H5.
      unfold pattern, VN1D, VonNeumann1D, sp in *; simpl in *.
      firstorder; subst; simpl in *; unfold add_proj in *; try firstorder omega.
      eauto with arith.
  Qed.

  Definition valid_strategy :
    valid VN1D ∅ (sp VN1D).
  Proof.
    unfold VN1D at 2; unfold sp, space, VonNeumann1D, nb_iter.

    apply sequ with (⋃ ⎨〚i, 2 * n - 1 - i〛× ⎨i⎬, i ∈ 〚0, n - 1〛⎬).
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
      destruct x; firstorder. (* set theory *)
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