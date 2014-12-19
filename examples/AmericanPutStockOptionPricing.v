Require Import StLib.Main.
Require Import Psatz.

Parameters T Smax : Z.

Module AmPutOpt <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, T〛×〚0, Smax〛.
  Definition dep c :=
    match c with
      | (t,s) =>
        [(t+1,s); (t+1,s-1); (t+1,s+1)]
    end.
End AmPutOpt.

Module P := Prog Z2 AmPutOpt.
Import P.

Section Naive.

  Definition naive_st :=
    (For "t" From 0 To T Do
       For "s" From 0 To Smax Do
         Fire ((T - "t")%aexpr, "s":aexpr))%prog.

  Definition v := [] : vars.
  Definition C := ∅ : set cell.

  Fact naive_st_correct_semi_auto :
    exec v C naive_st (C ∪ shape v naive_st).
  Proof.

    symbolic execution.

    unfold C, space; simplify sets with ceval.

    repeat (intro || split).

    - decide i=0.
      + right; forward. simpl in *; nia.
      + left. lhs; forward.
        exists (i-1); forward. nia.
        exists i0; forward. nia.

    - decide i=0.
      + right; forward. simpl in *; nia.
      + decide i0=0.
        * right; forward. simpl in *; nia.
        * left. lhs; forward.
          exists (i - 1); forward. nia.
          exists (i0 - 1); forward; nia.

    - decide i=0.
      + right; forward. simpl in *; nia.
      + decide i0=Smax.
        * right; forward. simpl in *; nia.
        * left. lhs; forward.
          exists (i - 1); forward. nia.
          exists (i0 + 1); forward; nia.
  Qed.

  Fact naive_st_correct_auto :
    exec v C naive_st (C ∪ shape v naive_st).
  Proof.

    symbolic execution.

    unfold C, space; simplify sets with ceval.

    repeat (intro || split).

    - decide i=0; [bruteforce | bruteforce' [i-1; i0]].

    - decide i=0; [bruteforce|].
      decide i0=0; [bruteforce | bruteforce' [i-1; i0-1]].

    - decide i=0; [bruteforce|].
      decide i0=Smax; [bruteforce | bruteforce' [i-1; i0+1]].
  Qed.

  Fact naive_st_complete :
    space ⊆ C ∪ shape v naive_st.
  Proof.
    unfold space; simpl; simplify sets with ceval.
    forward. bruteforce' [T-z; z0].
  Qed.

End Naive.

Section Triangles.

  Hypothesis T_Smax : Smax >= T * 2.

  Definition triangles_st :=
    ((For "t" From 0 To T Do
        For "s" From "t" To Smax - "t" Do
          Fire ((T - "t")%aexpr, "s":aexpr));;
     (For "t" From 0 To T Do
        For "s" From 0 To "t" - 1 Do
          Fire ((T - "t")%aexpr, "s":aexpr));;
     (For "t" From 0 To T Do
        For "s" From Smax - "t" + 1 To Smax Do
          Fire ((T - "t")%aexpr, "s":aexpr)))%prog.

  Fact triangles_st_correct_auto :
    exec v C triangles_st (C ∪ shape v triangles_st).
  Proof.

    symbolic execution.

    unfold C, space; simplify sets with ceval.

    Arguments Zplus x y : simpl never.
    Arguments Zminus m n : simpl never.

    repeat (intro || split).

(*    Ltac get_vars acc k :=
      match goal with
        | [ x : Z |- _ ] =>
          match acc with
            | context[x] => fail 1
            | _ => get_vars (x :: acc) k
          end
        | _ => k acc
(*          let l := constr:(gen_expr acc [Zplus; Zminus] 1) in
          let v := fresh in
          pose (v := l); unfold gen_expr, rev' in v; simpl in v;
          let ls := eval unfold v in v in

          bruteforce' ls*)
      end.
    Ltac candidates :=
      get_vars ([] : list Z)
               ltac:(fun ls =>
                       let ls' :=
                           eval simpl in
                       (ls ++ map (fun x => x+1) ls
                           ++ map (fun x => x-1) ls)%list in
                     bruteforce' ls').*)
    - decide i=0; [bruteforce | bruteforce' [i-1; i0]].
    - decide i=0; [bruteforce |].
      decide i0=0; [bruteforce | bruteforce' [i-1; i0-1]].
    - decide i=0; [bruteforce | bruteforce' [i0+1; i-1]].

    - decide i=0; [bruteforce |].
      decide i0=(i-1); [bruteforce' [i-1] | bruteforce' [i-1; i0]].
    - decide i=0; [bruteforce|].
      decide i0=0; [bruteforce | bruteforce' [i-1; i0-1]].
    - decide i=0; [bruteforce|].
      decide i0=(i-1); [bruteforce' [i-1; i]|].
      decide i0=(i-2); [bruteforce' [i-1] | bruteforce' [i-1; i0+1]].

    - decide i=0; [bruteforce|].
      decide i0=(Smax-i+1); [bruteforce' [Smax-i+1; i-1] | bruteforce' [i-1; i0]].
    - decide i=0; [bruteforce |].
      decide i0=(Smax-i+1); [bruteforce' [i-1; Smax-i]|].
      decide i0=(Smax-i+2); [bruteforce' [i-1; Smax-i+1] | bruteforce' [i-1; i0-1]].
    - decide i=0; [bruteforce|].
      decide i0=Smax; [bruteforce | bruteforce' [i-1; i0+1]].

  Qed.

End Triangles.