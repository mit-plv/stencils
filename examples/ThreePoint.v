Require Import StLib.Main StLib.Kernels.
Require Import Psatz.

Parameters P N : Z.
Axiom Ngt0 : N > 0.
Axiom Pgt0 : P > 0.

Module Jacobi1D <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, N-1〛×〚0, N*2*P-1〛.
  Definition target := 〚0, N-1〛×〚0, N*2*P-1〛.
  Definition dep c :=
    match c with
      | (t,i) =>
        [(t-1,i); (t-1,i-1); (t-1,i+1)]
    end.
End Jacobi1D.

Module P := Kern Z2 Jacobi1D.
Import P.

Definition my_comp1 :=
  (For "t" From 0 To N-1 Do
     For "i" From "t" To N*2-"t"-1 Do
       Fire ("t":aexpr, N*2*"id" + "i"))%code.

Definition my_comp2 :=
  (For "t" From 0 To N-1 Do
     For "i" From N*2-"t"+1 To "t"-1 Do
       Fire ("t":aexpr, N*2*"id" + "i"))%code.

Definition my_comp3 :=
  (For "t" From 0 To N-1 Do
     For "i" From N*2-"t" To "t"-1 Do
       Fire ("t":aexpr, N*2*"id" + "i"))%code.

Definition my_comp :=
  (If "T" =? 0 Then
     my_comp1
   Else
     If "T" =? 1 Then
       my_comp2;; my_comp3
     Else
       Nop)%code.

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

Definition my_code :=
  makeKernel my_comp my_send.

(*Require Import Morphisms.
Instance same_ite_Proper :
  forall U V W (b : {U}+{V}),
    Proper (same ==> same ==> same) (fun (A B : set W) => if b then A else B).
Proof.
  unfold Proper, respectful.
  intros.
  destruct b; firstorder.
Qed.*)

Lemma Z_div_mod_spec :
  forall a b,
    b > 0 ->
    a = b * (a / b) + a mod b /\ 0 <= a mod b < b.
Proof.
  intros; split.
  now apply Z_div_mod_eq.
  now apply Z_mod_lt.
Qed.

Lemma seg_dec :
  forall a b n,
    {a <= n <= b} + {n < a \/ n > b}.
Proof.
  intros.
  destruct Z_le_gt_dec with a n;
    destruct Z_le_gt_dec with n b.
  left; omega.
  right; now right.
  right; left; omega.
  right; now right.
Qed.

Theorem my_code_correct :
  kcorrect my_code (P-1) 1.
Proof.
  synthesize trace; intros.

  - decide T=0.
    + simplify sets with ceval.
      repeat (intro || split).
      (* Dependencies, first computation step. *)
      * admit.
      * admit.
      * admit.
    + decide T=1.
      * simplify sets with ceval.
        repeat (intro || split).
        (* Dependencies, second computation step. *)
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
      * omega.

  (* The communication program is correct. *)
  - destruct (to =? id - 1).
    forward.
    destruct (to =? id + 1); forward.

  (* Threads do not send a value they do not know. *)
  - unfold af_synth, computes_synth, sends_synth in *; simpl in *.
    simplify sets with ceval.
    repeat intro.

    destruct (to =? id-1); forward; lhs; forward.
    * (exists 0; simpl; forward).
      exists x0; forward.
      exists x0; forward'. omega.
    * destruct (to =? id + 1); forward.
      (exists 0; simpl; forward).
      exists x0; forward.
      exists (N*2 - x0 - 1); forward'; try omega.
      repeat rhs; constructor; unfold singleton.
      subst; f_equal; omega.

  (* Completeness *)
  - unfold target, bf_synth, computes_synth, sends_synth; simpl.
    repeat intro.
    destruct x; forward; unfold fst, snd in *.
    Ltac to_loc H := generalize H; intro.
    to_loc Ngt0.
    assert (H' : N*2 > 0) by omega.
    to_loc (Z_div_mod_spec z0 (N*2) H').
    exists (z0 / (N*2)); forward.
    nia. nia.

    destruct (seg_dec z (N*2 - z - 1) (z0 mod (N*2))).

    + lhs; forward.
      exists 0; simpl; forward.
      omega.
      exists z; forward.
      exists (z0 mod (N*2)); forward.
      simplify sets with ceval.
      forward.

    + destruct o.
      * lhs; forward.
      exists 1; simpl; forward.
      omega.
Abort.