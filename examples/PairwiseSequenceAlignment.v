Require Import StLib.Main.
Require Import Psatz.

Module PSA_Domain <: DOMAIN.

  Inductive Var : Set := P | Q | D.

  Definition cell := (Var * Z * Z)%type.
  Definition cexpr := (Var * aexpr * aexpr)%type.
  Definition ceval (v : vars) (c : cexpr) : cell :=
    (fst (fst c), aeval v (snd (fst c)), aeval v (snd c)).

End PSA_Domain.

Parameters M N : Z.

Module PSA <: (PROBLEM PSA_Domain).
  Local Open Scope aexpr.
  Import PSA_Domain.

  Definition space := ⎨P⎬ ×〚0, M〛×〚0, N〛
                       ∪ ⎨Q⎬ ×〚0, M〛×〚0, N〛
                       ∪ ⎨D⎬ ×〚0, M〛×〚0, N〛.
  Definition dep c :=
    match c with
      | (P,m,n) =>
        [(D,m-1,n); (P,m-1,n)]
      | (Q,m,n) =>
        [(D,m,n-1); (Q,m,n-1)]
      | (D,m,n) =>
        [(D,m-1,n-1); (P,m,n); (Q,m,n)]
    end.
End PSA.

Module P := Prog PSA_Domain PSA.
Import P.

Definition naive_st :=
  (For "m" From 0 To M Do
     For "n" From 0 To N Do
       Fire (P, "m":aexpr, "n":aexpr);;
       Fire (Q, "m":aexpr, "n":aexpr);;
       Fire (D, "m":aexpr, "n":aexpr))%prog.

Definition v := [] : vars.
Definition C := ∅ : set cell.

Fact naive_st_correct_semi_auto :
  exec v C naive_st (C ∪ shape v naive_st).
Proof.

  symbolic execution.

  unfold C, space; simplify sets with ceval.

  firstorder.

  - decide i=0.
    + right. step; simpl in *; nia.
    + left. lhs; step.
      exists (i - 1); step. nia.
      exists i0; step.
      rhs; rhs; step.

  - decide i=0.
    + right. step; simpl in *; nia.
    + left. lhs; step.
      exists (i - 1); step. nia.
      exists i0; step.
      lhs; step.

  - decide i0=0.
    + right. step; simpl in *; nia.
    + left. lhs. rhs; step.
      exists (i0 - 1); step. nia.
      rhs; rhs; step.

  - decide i0=0.
    + right. step; simpl in *; nia.
    + left. lhs. rhs; step.
      exists (i0 - 1); step. nia.
      rhs; lhs; step.

  - decide i=0.
    + right. step; simpl in *; nia.
    + decide i0=0.
      * right. step; simpl in *; nia.
      * left. lhs; lhs; lhs; step.
        exists (i - 1); step. nia.
        exists (i0 - 1); step. nia. nia.
        rhs; rhs; step.

  - left. lhs; rhs; step.

  - left. rhs; step.
Qed.

Fact naive_st_correct_auto :
  exec v C naive_st (C ∪ shape v naive_st).
Proof.

  symbolic execution.

  unfold C, space; simplify sets with ceval.

  firstorder.

  - decide i=0; [bruteforce | bruteforce' [i-1; i0]].
  - decide i=0; [bruteforce | bruteforce' [i-1; i0]].
  - decide i0=0; [bruteforce | bruteforce' [i0-1]].
  - decide i0=0; [bruteforce | bruteforce' [i0-1]].
  - decide i=0; [bruteforce | decide i0 = 0]; [bruteforce | bruteforce' [i-1; i0-1]].
  - bruteforce.
  - bruteforce.
Qed.
