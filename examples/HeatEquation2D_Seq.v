Require Import StLib.Main.
Require Import Psatz.

(**
 * Solving the 2D Heat equation using the finite difference method yields
 * the following three-dimensional stencil:
 *)

Parameters T I J : Z.

Module Jacobi2D <: (PROBLEM Z3).
  Local Open Scope aexpr.

  Definition space := 〚0, T〛×〚0, I〛×〚0, J〛.
  Definition target := 〚0, T〛×〚0, I〛×〚0, J〛.
  Definition dep c :=
    match c with
      | (t,i,j) =>
        [(t-1,i,j); (t-1,i-1,j); (t-1,i+1,j);
         (t-1,i,j-1); (t-1,i,j+1)]
    end.
End Jacobi2D.

(** We import the library. *)

Module P := Prog Z3 Jacobi2D.
Import P.

(** This is a naive single-threaded program solving the problem defined
 * above. *)

Definition naive_st :=
  (For "t" From 0 To T Do
     For "i" From 0 To I Do
       For "j" From 0 To J Do
         Fire ("t":aexpr, "i":aexpr, "j":aexpr))%prog.

(** We prove the correctness of the program, in a semi automatic way. *)

Definition v := [] : vars.
Definition C := ∅ : set cell.

Fact naive_st_correct_semi_auto :
  exec v C naive_st (C ∪ shape v naive_st).
Proof.

  symbolic execution.

  unfold C, space; simplify sets with ceval.

  firstorder.

  - decide i=0.
    + right. forward. simpl in *; nia.
    + left. lhs. lhs; forward.
      exists (i - 1); forward. nia.
      exists i0; forward.
      exists i1; forward.

  - decide i=0.
    + right. forward. simpl in *; nia.
    + decide i0=0.
      * right. forward. simpl in *; nia.
      * left. lhs. lhs; forward.
        exists (i - 1); forward. nia.
        exists (i0 - 1); forward. nia. nia.
        exists i1; forward.

  - decide i=0.
    + right. forward. simpl in *; nia.
    + decide i0=I.
      * right. forward. simpl in *; nia.
      * left. lhs. lhs; forward.
        exists (i - 1); forward. nia.
        exists (i0 + 1); forward. nia. nia.
        exists i1; forward.

  - decide i=0.
    + right. forward. simpl in *; nia.
    + decide i1=0.
      * right. forward. simpl in *; nia.
      * left. lhs. lhs; forward.
        exists (i-1); forward. nia.
        exists i0; forward.
        exists (i1 - 1); forward; nia.

  - decide i=0.
    + right. forward. simpl in *; nia.
    + decide i1=J.
      * right. forward. simpl in *; nia.
      * left. lhs. lhs; forward.
        exists (i-1); forward. nia.
        exists i0; forward.
        exists (i1 + 1); forward; nia.
Qed.

Fact naive_st_correct :
  correct naive_st.
Proof.
  split.

  (* Assertions do not fail. *)

  - symbolic execution.

    unfold C, space; simplify sets with ceval.

    repeat (intro || split).

    * decide i=0; [bruteforce | bruteforce' [i-1; i0; i1]].

    * decide i=0; [bruteforce|].
      decide i0=0; [bruteforce | bruteforce' [i-1; i0-1; i1]].

    * decide i=0; [bruteforce|].
      decide i0=I; [bruteforce | bruteforce' [i-1; i0+1; i1]].

    * decide i=0; [bruteforce|].
      decide i1=0; [bruteforce | bruteforce' [i-1; i0; i1-1]].

    * decide i=0; [bruteforce|].
      decide i1=J; [bruteforce | bruteforce' [i-1; i0; i1+1]].

  - unfold target; simpl; simplify sets with ceval.
    forward. subst; forward. simpl; forward.
Qed.
