Require Import StLib.Main StLib.Kernels.
Require Import Psatz.

Parameters P N : Z.
Axiom Ngt0 : N > 0.
Axiom Pgt0 : P > 0.

(** Let's start with the 1D Jacobi kernel. *)
Module Jacobi1D <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, N-1〛 × 〚0, N*P-1〛.
  Definition target := 〚0, N-1〛 × 〚0, N*P-1〛.
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

Definition my_comp :=
  (If "T" <? N Then
     For "x" From N*"id" To N*"id" + N-1 Do
       Fire ("T":aexpr, "x" : aexpr)     
   Else
     Nop)%code.

Definition my_send :=
  (If "to" =? "id" - 1 Then
     Fire ("T":aexpr, N*"id")
   Else
     If "to" =? "id" + 1 Then
       Fire ("T":aexpr, N*"id" + N-1)
     Else
       Nop)%code.

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

Ltac destr_case b :=
  let bb := fresh in
  let Hbb := fresh in
  remember b as bb eqn:Hbb;
  symmetry in Hbb; destruct bb;
  (apply Z.eqb_eq in Hbb || apply Z.eqb_neq in Hbb);
  try (exfalso; omega).

Ltac destr_case_lt b :=
  let bb := fresh in
  let Hbb := fresh in
  remember b as bb eqn:Hbb;
  symmetry in Hbb; destruct bb;
  (apply Z.ltb_lt in Hbb || apply Z.ltb_ge in Hbb);
  try (exfalso; omega).

Theorem my_code_correct :
  kcorrect my_code (P-1) (N-1).
Proof.

  synthesize trace; intros.

  (** First goal is the verification conditions for the computation steps,
   * which encapsulate the dependencies. *)
  - destr_case_lt (T <? N); forward; simplify sets with ceval.

    (* South dependency. *)
    decide T=0; [right; unfold space; forward; unfold fst, snd in *; omega|left].
    lhs; lhs; forward.
    exists (T-1); forward; try omega.
    unfold computes_synth; simpl; simplify sets with ceval.
    destr_case_lt (T - 1 <? N); forward.
    exists i; forward'; omega.

    (* South-west dependency. *)
    decide T=0; [right; unfold space; forward; unfold fst, snd in *; omega|].
    decide i=(N*id).

    decide id=0; [right; unfold space; forward; unfold fst, snd in *; omega|].
    left; lhs; rhs; forward.
    exists (T - 1); forward; try omega.
    exists (id - 1); forward; try omega.
    unfold sends_synth; simpl; simplify sets with ceval.
    destr_case (id =? id - 1 - 1); destr_case (id =? id - 1 + 1); forward; nia.
        
    left; lhs; lhs; forward.
    exists (T - 1); forward; try omega.
    unfold computes_synth; simpl; simplify sets with ceval.
    destr_case_lt (T - 1 <? N); forward.
    exists (i-1); forward'; omega.

    (* South-east dependency. *)
    decide T=0; [right; unfold space; forward; unfold fst, snd in *; omega|].
    decide i=(N*id + N-1).

    decide id=(P-1); [right; unfold space; forward; unfold fst, snd in *; nia|].
    left; lhs; rhs; forward.
    exists (T - 1); forward; try omega.
    exists (id + 1); forward; try omega.
    unfold sends_synth; simpl; simplify sets with ceval.
    destr_case (id =? id + 1 - 1); forward; nia.

    left; lhs; lhs; forward.
    exists (T - 1); forward; try omega.
    unfold computes_synth; simpl; simplify sets with ceval.
    destr_case_lt (T - 1 <? N); forward.
    exists (i+1); forward'; omega.

  (** Second goal is the verification conditions for the communication steps,
   * which are trivial. *)
  - destruct (to =? id - 1); forward.
    destruct (to =? id + 1); forward.

  (** Third goal is "conservation of knowledge": we are not allowed to send
   * a value that we don't know. *)
  - unfold af_synth, computes_synth, sends_synth in *; simpl in *.
    simplify sets with ceval.
    repeat intro; lhs.

    (* Left side *)
    destruct (to =? id - 1); forward.
    exists T; forward.
    destr_case_lt (T <? N); forward.
    exists (N*id); forward'; omega.

    (* Right side *)
    destruct (to =? id + 1); forward.
    exists T; forward.
    destr_case_lt (T <? N); forward.
    exists (N*id + N-1); forward'; omega.

  (** Last goal is completeness: we computed all the cells we were supposed
   * to compute. *)
  - unfold target, bf_synth, computes_synth, sends_synth; simpl.
    repeat intro.
    destruct x; forward; unfold fst, snd in *.

    (** We have to prove that [x] belongs to some T[I], TL[I] or TR[I], for
     * some "I". This "I" is obtained by take the quotient of x's abscissa
     * by 2N. *)
    pose (I := z0 / N).
    to_ctx (Z_div_mod_spec z0 N Ngt0).
    exists I; forward.
    unfold I; nia.
    unfold I; nia.

    lhs; forward.
    exists z; forward. omega.
    destr_case_lt (z <? N); forward.
    simplify sets with ceval.
    exists z0; forward; unfold I; omega.
Qed.