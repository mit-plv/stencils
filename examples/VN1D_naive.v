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
  (For "i" From 0 To N-1 Do
       Fire (N*"id" + "i", "T" : Arith.t))%step_t.

Definition comm_p :=
  (If "to" =? "id"-1 Then
     Fire (N*"id", "T" : Arith.t)
   Else
     If "to" =? "id"+1 Then
       Fire (N*"id" + N-1, "T" : Arith.t)
     Else
       Nop)%step_t.

Goal forall x id T s,
       x = (Symbolic.exec (Comp.denote comp_p) (s⟨"id" ← id; "T" ← T⟩)).
intros; simpl; unfold CEval, Z2.eval; simpl.
Abort.

Goal
  forall x id to T s,
    x =
    (Symbolic.exec (Comm.denote comm_p) (s⟨"id" ← id; "T" ← T; "to" ← to⟩)).
intros; simpl; unfold CEval, Z2.eval; simpl.
Abort.

Goal forall id T s S,
       Symbolic.VC (Comp.denote comp_p) (s⟨"id" ← id; "T" ← T⟩) S.
intros; simpl; unfold Comp.F, Z2.add, CEval, Z2.eval; simpl.
intuition.
Abort.

Goal forall id T s S,
       Symbolic.VC (Comp.denote (Fire ("id"+"T", "id" : Arith.t);;
                                 Fire ("id"+"T"+1, "id"+1))%step_t)
                   (s⟨"id" ← id; "T" ← T⟩) S.
intros; simpl; unfold Comp.F, Z2.add, CEval, Z2.eval; simpl.
intuition.
Transparent State.get_cell.
rewrite (H (id + T + fst k + 0, id + snd k + 0)).
Focus 4.
Abort.



Definition naive := Kernel.make comp_p comm_p.

Theorem naive_correct :
  Kernel.correct naive (Z.to_nat K) (Z.to_nat P).
Proof.
  unfold Kernel.correct.
  unfold Kernel.trace_correct.
(*  exists (fun T => Symbolic.Trace.s naive T (Z.to_nat P)).
  exists (fun T => Symbolic.Trace.t naive T (Z.to_nat P)).
  exists (fun T => Symbolic.Trace.u naive T).
  unfold Kernel.trace_correct, Kernel.step, Kernel.comp_step, Kernel.send_step,
  Kernel.merge_step.
  repeat (intro || split).*)
Abort.