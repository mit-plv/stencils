Require Import StLib.Main StLib.Kernels.
Require Import Psatz.

Parameters P N : Z.

Module Jacobi1D <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, N-1〛×〚0, N*P-1〛.
  Definition target := 〚0, N-1〛×〚0, N*P-1〛.
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
     For "i" From "t" To N-"t"-1 Do
       Fire ("t":aexpr, N*"id" + "i"))%code.

Definition my_comp2 :=
  (For "t" From 0 To N-1 Do
     For "i" From N-"t"+1 To "t"-1 Do
       Fire ("t":aexpr, N*"id" + "i"))%code.

Definition my_comp3 :=
  (For "t" From 0 To N-1 Do
     For "i" From N-"t" To "t"-1 Do
       Fire ("t":aexpr, N*"id" + "i"))%code.

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
      Fire ("t":aexpr, N*"id" + "t")
   Else
     If "to" =? "id" + 1 Then
       For "t" From 0 To N-1 Do
         Fire ("t":aexpr, N*"id" + N-"t"-1)
     Else
       Nop)%code.

Definition my_code :=
  makeKernel my_comp my_send.

Theorem my_code_correct :
  kcorrect my_code (P-1) 1.
Proof.
  eexists; eapply trace_synth_correct; simpl.

  repeat (intro || split).
Abort.