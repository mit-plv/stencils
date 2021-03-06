Require Import StLib.Main StLib.Kernels.
Require Import Psatz.
Require Import Utils.

Parameters N P : Z.
Axiom Ngt0 : N > 0.
Axiom Pgt0 : P > 0.

Module AmPutOpt <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, N-1〛×〚0, N*P-1〛.
  Definition target := 〚0, N-1〛×〚0, N*P-1〛.
  Definition dep c :=
    match c with
      | (t,s) =>
        [(t+1,s); (t+1,s-1); (t+1,s+1)]
    end.
End AmPutOpt.

Module P := Kern Z2 AmPutOpt.
Import P.

Definition my_comp :=
  (If "T" <? N Then
     For "x" From N*"id" To N*"id" + N-1 Do
       Fire (N - 1 - "T", "x" : aexpr)
   Else
     Nop)%code.

Definition my_send :=
  (If "to" =? "id" - 1 Then
     Fire (N - 1 - "T", N*"id")
   Else
     If "to" =? "id" + 1 Then
       Fire (N - 1 - "T", N*"id" + N-1)
     Else
       Nop)%code.

Definition my_code :=
  makeKernel my_comp my_send.

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
    exists i. forward. repeat rhs. forward; omega.

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
    exists (i-1); forward'; try omega.
    repeat rhs; forward; omega.

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
    exists (i+1); forward'; try omega.
    repeat rhs; forward; omega.

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

    pose (I := z0 / N).
    to_ctx (Z_div_mod_spec z0 N Ngt0).
    exists I; forward.
    unfold I.
    unfold I; nia.
    unfold I; nia.

    lhs; forward.
    exists (N - 1 - z); forward; [omega | omega |].
    destr_case_lt (N - 1 - z <? N); forward.
    simplify sets with ceval.
    exists z0; forward; unfold I; omega.
Qed.