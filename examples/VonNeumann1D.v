(* ========================================================================= *)
(* Example: The 1D Von Neumann stencil                                        *)
(* ========================================================================= *)

Require Import StLib.Core.
Require Import Psatz.





(**
 * The one-dimensional Von Neumann stencil is defined by the following pattern:
 *
 *      +---+---+---+
 *      |   |   |   |
 *      | +==> <==+ |
 *      |   |   |   |
 *      +---+---+---+
 *
 * As usual, there is a time-dependency, so that the stencil is, in fact,
 * two-dimensional. The corresponding pattern is:
 *
 *          +---+
 *          |   |
 *        +==> <==+
 *        ‖ |   | ‖
 *      +-‖-------‖-+
 *      | ‖ |   | ‖ |
 *      | + |   | + |
 *      |   |   |   |
 *      +---+---+---+
 *
 *)

Section VonNeumann1D.
  Variables n : nat.
  Variable T : nat.

  Instance VonNeumann1D : Stencil nat1 :=
  {
    space   := 〚0, n-1〛;
    nb_iter := T;
    pattern := [0; 1; 2];
    center  := 1
  }.
End VonNeumann1D.





Section Triangles.
  Variable n : nat.
  Variable N : nat. (* # of nodes *)

  Hypothesis n_ge_1 : n >= 1.
  Hypothesis N_ge_1 : N >= 1.





  (** Warm-up: If we know the values in a row [r], we can compute the row
   * above [r], apart from its endpoints.  *)

  Lemma compute_row :
    forall a b c d t,
      a <= b < 2 * n * N -> 1 + t <= n - 1 ->
      c = 1 + a -> b = 1 + d ->

      (〚a, b〛 × ⎨t⎬ ⟿〚a, b〛 × ⎨t⎬ ∪〚c, d〛 × ⎨1+t⎬
                                                // VonNeumann1D (2 * n * N) n).
  Proof.
    forward.
    union with 1; forward.
    union with (〚a, 1+d〛 × ⎨t⎬); forward.
    image with (〚1 + a, d 〛 × ⎨1 + t⎬); forward.

    (** Now this is just arithmetics *)
    + nia.
    + split; [omega | eauto with arith].
  Qed.





  (** Now, let's write programs.  This one is the first computation step of
   * a higher-level strategy.  It spawns [N] nodes, which compute one triangle
   * each.  This program is not completely refined.  It does not specify how
   * the [Compute] command should be executed. *)

  Definition compute_triangles :=
    (For i ∈〚0, n-1〛 Do
         Spawn Node k ∈〚0, N-1〛 With
           Compute 〚2 * n * k + i, 2 * n * (k + 1) - 1 - i〛× ⎨i⎬).

  (** The set of cells whose value is known at the end of the execution of
   * [compute_triangle] can be inferred automatically.  Notice that there is no
   * proof of correctness yet. *)

  Eval simpl in (shape compute_triangles).





  (** Proof of correctness. *)

  Theorem compute_triangles_valid :
    ∅ ⟿ ∅ ∪ shape compute_triangles // VonNeumann1D (2 * n * N) n.
  Proof.
    generate proof obligations.

    (** Bootstrapping, the first row of every triangle can be computed *)
    + forward.
      union with 1; forward.
      easy union image; forward.
      nia. (* arithmetics *)

    (** Now we use the previous lemma to show the correctness of this
     * strategy.  Since we are proving a partial strategy, the lemma could
     * have been an hypothesis in this theorem. *)

    + repeat rewrite empty_bin_union.
      eapply focus; try reflexivity.
      apply compute_row; try reflexivity; forward.
      nia. (* arithmetics *)
      forward.
      union with t; forward.
      union with p; forward.
      nia. (* arithmetics *)
  Qed.
End Triangles.