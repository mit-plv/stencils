Require Import StLib.Main StLib.Kernels.
Require Import Psatz.

Parameters P N : Z.
Axiom Ngt0 : N > 0.
Axiom Pgt0 : P > 0.

(** Let's start with the 1D Jacobi kernel. *)
Module Jacobi1D <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, N-1〛 × 〚0, N*2*P-1〛.
  Definition target := 〚0, N-1〛 × 〚0, N*2*P-1〛.
  (** Every cell depends on its former value, as well as the one of its
   * neighbors. *)
  Definition dep c :=
    match c with
      | (t,i) =>
        [(t-1,i); (t-1,i-1); (t-1,i+1)]
    end.
End Jacobi1D.

(** Specialize the library for this stencil. *)
Module P := Kern Z2 Jacobi1D.
Import P.

(** We're now going to write a distributed stencil algorithm. It goes as
 * follows:
 *
 * (1) (COMP) Thread number "I" computes the "triangle"
 *   T[I] = { u[t,x] : 0 <= t < N, 2NI + t <= x < 2NI + 2N-t }.
 *
 * Rk: in particular, threads which are assigned the "endpoint", that is,
 * threads 0 and P, compute some virtual values, that are ignored thanks
 * to the definition of [space] in Jacobi1D. These two will have a
 * separate treatment in the proof.
 *
 * (2) (COMM) Thread number "I" sends to thread I+1 the "right border" of
 * T[I]
 *   RB[I] = { u[t, 2NI + 2N-t-1] : 0 <= t < N }.
 * and to thread I-1 the "left border" of T[I]
 *   LB[I] = { u[t, 2NI + t] : 0 <= t < N }
 *
 * (3) (COMP) Thread number "I" computes the two "triangles"
 *   TL[I] = { u[t,x] : 0 <= t < N, 2N(I-1) + 2N-t <= x < 2NI + t }
 * and
 *   TR[I] = { u[t,x] : 0 <= t < N, 2NI + 2N-t <= x < 2N(I+1) + t}.
 *)

(** Step 1, (COMP). *)
Definition my_comp0 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id"+"t" To N*2*"id" + N*2-"t"-1 Do
       Fire ("t":aexpr, "x" : aexpr))%code.

(** Step 2, (COMM). *)
Definition my_send :=
  (If "to" =? "id" - 1 Then
    For "t" From 0 To N-1 Do
      Fire ("t":aexpr, N*2*"id" + "t")
   Else
     If "to" =? "id" + 1 Then
       For "t" From 0 To N-1 Do
         Fire ("t":aexpr, N*2*"id" + N*2-"t"-1)
     Else
       Nop)%code.

(** Step 3, (COMP), TL *)
Definition my_comp1_0 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id" - "t" To N*2*"id" + "t" - 1 Do
       Fire ("t":aexpr, "x":aexpr))%code.

(** Step 3, (COMP), TR *)
Definition my_comp1_1 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id" + N*2-"t" To N*2*"id" + N*2+"t"-1 Do
       Fire ("t":aexpr, "x":aexpr))%code.

(** Merge all computation steps together. *)
Definition my_comp :=
  (If "T" =? 0 Then
     my_comp0
   Else
     If "T" =? 1 Then
       my_comp1_0;; my_comp1_1
     Else
       Nop)%code.

(** And here is the kernel! *)
Definition my_code :=
  makeKernel my_comp my_send.

Ltac to_ctx H := generalize H; intro.

(** The following two arithmetic lemma will be used in the proof of
 * correctness. *)
Lemma Z_div_mod_spec :
  forall a b,
    b > 0 ->
    0 <= a - b * (a / b) < b.
Proof.
  intros.
  to_ctx (Z_div_mod_eq a b H);
  to_ctx (Z_mod_lt a b H);
  omega.
Qed.

Lemma seg_dec :
  forall a b n, a <= n <= b \/ n < a \/ n > b.
Proof.
  intros.
  destruct Z_le_gt_dec with a n;
    destruct Z_le_gt_dec with n b;
  firstorder.
Qed.

(** Let's now prove the correctness of this kernel. *)
Theorem my_code_correct :
  kcorrect my_code (P-1) 1.
Proof.
  to_ctx Ngt0; to_ctx Pgt0.

  synthesize trace; intros.

  (** First goal is the verification conditions for the computation steps,
   * which encapsulate the dependencies. *)
  - decide T=0.

    + simplify sets with ceval; forward.

      (** COMP0, first dependency (south). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists i0; forward; omega.

      (** COMP0, second dependency (south-west). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists (i0-1); forward; omega.

      (** COMP0, last dependency (south-east). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists (i0+1); forward; omega.

    + decide T=1.
      simplify sets with ceval; forward.

      (** COMP1, TL, first dependency (south). *)
      assert (HT : N*2*id - i = i0 \/ i0 = N*2*id + i - 1
                   \/ N*2*id - i < i0 < N*2*id + i - 1)
        by omega; destruct HT as [?|[?|?]].

      (* Left edge of TL[id]. *)
      decide id=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id-1); forward; try omega.
      unfold sends_synth; simpl; forward.

      Ltac destr_case b :=
        let bb := fresh in
        let Hbb := fresh in
        remember b as bb eqn:Hbb;
        symmetry in Hbb; destruct bb;
        (apply Z.eqb_eq in Hbb || apply Z.eqb_neq in Hbb);
        try (exfalso; omega).

      destr_case (id =? id - 1 - 1).
      destr_case (id =? id - 1 + 1).
      forward.
      exists (i-1); forward; try omega.
      simplify sets with ceval.
      f_equal; try omega; nia.
      
      (* Right edge of TL[id]. *)
      left. lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (* Interior of TL[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (** COMP1, TL, second dependency (south-west). *)
      admit.

      (** COMP1, TL, last dependency (south-east). *)
      admit.

      (** COMP1, TR, first dependency (south). *)
      assert (HT : N*2*id + N*2 - i = i0 \/ i0 = N*2*id + N*2 + i - 1
                   \/ N*2*id + N*2 - i < i0 < N*2*id + N*2 + i - 1)
        by omega; destruct HT as [?|[?|?]].

      (* Left edge of TR[id]. *)
      left; lhs; lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.
      
      (* Right edge of TR[id]. *)
      decide id=(P-1); [right; unfold space; forward; unfold fst, snd in *; nia|].

      left; lhs; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id+1); forward; try omega.
      unfold sends_synth; simpl; forward.

      destr_case (id =? id + 1 - 1).
      forward.
      exists (i-1); forward; try omega.
      simplify sets with ceval.
      f_equal; try omega; nia.

      (* Interior of TR[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (** COMP1, TR, second dependency (south-west). *)
      admit.

      (** COMP1, TR, last dependency (south-east). *)
      admit.

      omega.

  (** Second goal is the verification conditions for the communication steps,
   * which are trivial. *)
  - destruct (to =? id - 1); forward.
    destruct (to =? id + 1); forward.

  (** Third goal is "conservation of knowledge": we are not allowed to send
   * a value that we don't know. *)
  - unfold af_synth, computes_synth, sends_synth in *; simpl in *.
    simplify sets with ceval.
    repeat intro; lhs.

    destruct (to =? id - 1); forward.
    (* Left border *)
    exists 0; simpl; forward. (* Time step 0 *)
    exists x0; forward.
    exists (snd x); rewrite H6; simpl; forward'; omega.

    destruct (to =? id + 1); simpl; forward.
    (* Right border *)
    exists 0; simpl; forward. (* Time step 0 *) 
    exists x0; forward.
    exists (snd x); rewrite H9; simpl; forward'; try omega.

  (** Last goal is completeness: we computed all the cells we were supposed
   * to compute. *)
  - unfold target, bf_synth, computes_synth, sends_synth; simpl.
    repeat intro.
    destruct x; forward; unfold fst, snd in *.

    (** We have to prove that [x] belongs to some T[I], TL[I] or TR[I], for
     * some "I". This "I" is obtained by take the quotient of x's abscissa
     * by 2N. *)
    pose (I := z0 / (N*2)).
    assert (HNT : N*2 > 0) by omega.
    to_ctx (Z_div_mod_spec z0 (N*2) HNT).
    exists I; forward.
    unfold I; nia.
    unfold I; nia.

    destruct seg_dec with (N*2*I + z) (N*2*I + N*2-z-1) z0 as [?|[?|?]];
      lhs; forward.
   
    (* Case T[I]. *)
    exists 0; simpl; simplify sets with ceval;
    forward; try omega. (* First computation step. *)
    exists z; forward.
    exists z0; forward.

    (* Case TL[I]. *)
    exists 1; simpl; simplify sets with ceval;
    forward; try omega. (* Second computation step. *)
    lhs; forward. (* First sub-step *)
    exists z; forward.
    exists z0; forward.
    unfold I; omega.
    omega.

    (* Case TR[I] *)
    exists 1; simpl; simplify sets with ceval;
    forward; try omega. (* Second computation step. *)
    rhs; forward. (* Second sub-step *)
    exists z; forward.
    exists z0; forward.
    omega.
    unfold I; omega.
Qed.
