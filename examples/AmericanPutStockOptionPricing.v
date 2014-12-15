Require Import StLib.Main.
Require Import Psatz.

(**
 *)

Parameters T Smax : Z.

Module AmPutOpt <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, T〛×〚0, Smax〛.
  Definition dep c :=
    match c with
      | (t,i) =>
        [(t+1,i); (t+1,i-1); (t+1,i+1)]
    end.
End AmPutOpt.

Module P := Prog Z2 AmPutOpt.
Import P.

Definition naive_st :=
  (For "t" From 0 To T Do
     For "i" From 0 To Smax Do
         Fire ((T - "t")%aexpr, "i":aexpr))%prog.

Definition v := [] : vars.
Definition C := ∅ : set cell.

Fact naive_st_correct_semi_auto :
  exec v C naive_st (C ∪ shape v naive_st).
Proof.

  symbolic execution.

  unfold C, space; simplify sets with ceval.

  firstorder.

  - decide i=0.
    + right; step. simpl in *; nia.
    + left. lhs; step.
      exists (i-1); step. nia.
      exists i0; step. nia.

  - decide i=0.
    + right; step. simpl in *; nia.
    + decide i0=0.
      * right; step. simpl in *; nia.
      * left. lhs; step.
        exists (i - 1); step. nia.
        exists (i0 - 1); step; nia.

  - decide i=0.
    + right; step. simpl in *; nia.
    + decide i0=Smax.
      * right; step. simpl in *; nia.
      * left. lhs; step.
        exists (i - 1); step. nia.
        exists (i0 + 1); step; nia.

Qed.