(* ========================================================================== *
 * Example                                                                    *
 * ========================================================================== *)

Require Import StLib.Core.
Require Import StLib.Univ.Z2.

Parameters N P K : Z.

Module VonNeumann1D <: (STENCIL Z2).
  Definition space := 〚0, N*P-1〛×〚0, K-1〛.
  Definition pattern := [(-1,-1); (0,-1); (1,-1)].
  Definition center  := (0,0).
End VonNeumann1D.

Module Verif := (Make Z2 VonNeumann1D).
Import Verif.

(** A simple kernel *)

Definition comp_p :=
  (If (0 <=? "id") && ("id" <? P)
   && (0 <=? "T") && ("T" <? K) Then
     For "i" From 0 To N-1 Do
       Fire (N*"id" + "i", "T" : Arith.t)
   Else
     Nop)%step_t.

Definition comm_p :=
  (If (0 <=? "id") && ("id" <? P)
   && (0 <=? "T") && ("T" <? K) Then
     If "to" =? "id"-1 Then
       Fire (N*"id", "T" : Arith.t)
     Else
       If "to" =? "id"+1 Then
         Fire (N*"id" + N-1, "T" : Arith.t)
       Else
         Nop
   Else
     Nop)%step_t.

Definition naive := Kernel.make comp_p comm_p.

Theorem naive_correct :
  Kernel.correct naive.
Proof.
  halts after K steps.
Abort.