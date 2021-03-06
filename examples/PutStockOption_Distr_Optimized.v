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

Definition my_comp0 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id"+"t" To N*2*"id" + N*2-"t"-1 Do
       Fire (N - 1 - "t", "x" : aexpr))%code.

Definition my_send :=
  (If "to" =? "id" - 1 Then
    For "t" From 0 To N-1 Do
      Fire (N - 1 - "t", N*2*"id" + "t");;
    For "t" From 1 To N-1 Do
      Fire (N - "t", N*2*"id" + "t")
   Else
     If "to" =? "id" + 1 Then
       For "t" From 0 To N-1 Do
         Fire (N - 1 - "t", N*2*"id" + N*2-"t"-1);;
       For "t" From 1 To N-1 Do
         Fire (N - "t", N*2*"id" + N*2-"t"-1)
     Else
       Nop)%code.

Definition my_comp1_0 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id" - "t" To N*2*"id" + "t" - 1 Do
       Fire (N - 1 - "t":aexpr, "x":aexpr))%code.

Definition my_comp1_1 :=
  (For "t" From 0 To N-1 Do
     For "x" From N*2*"id" + N*2-"t" To N*2*"id" + N*2+"t"-1 Do
       Fire (N - 1 - "t":aexpr, "x":aexpr))%code.

(** Merge all computation steps together. *)
Definition my_comp :=
  (If "T" =? 0 Then
     my_comp0
   Else
     If "T" =? 1 Then
       my_comp1_0;; my_comp1_1
     Else
       Nop)%code.

(** And here is the kernel! *)
Definition my_code :=
  makeKernel my_comp my_send.

(** Let's now prove the correctness of this kernel. *)
Theorem my_code_correct :
  kcorrect my_code (P-1) 1.
Proof.
  to_ctx Ngt0; to_ctx Pgt0.

  synthesize trace; intros.

  (** First goal is the verification conditions for the computation steps,
   * which encapsulate the dependencies. *)
  - decide T=0.

    + simplify sets with ceval; forward.

      (** COMP0, first dependency (south). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists i0; forward; omega.

      (** COMP0, second dependency (south-west). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists (i0-1); forward; omega.

      (** COMP0, last dependency (south-east). *)
      decide i=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs. rhs; forward.
      exists (i-1); forward. omega.
      exists (i0+1); forward; omega.

    + decide T=1.
      simplify sets with ceval; forward.

      (** COMP1, TL, first dependency (south). *)
      assert (HT : N*2*id - i = i0 \/ i0 = N*2*id + i - 1
                   \/ N*2*id - i < i0 < N*2*id + i - 1)
        by omega; destruct HT as [?|[?|?]].

      (* Left edge of TL[id]. *)
      decide id=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id-1); forward; try omega.
      unfold sends_synth; simpl; forward.

      destr_case (id =? id - 1 - 1).
      destr_case (id =? id - 1 + 1).
      forward.
      simplify sets with ceval.
      exists (i-1); forward; try omega.
      lhs; forward; try omega; nia.

      (* Right edge of TL[id]. *)
      left. lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (* Interior of TL[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (** COMP1, TL, second dependency (south-west). *)
      destruct Z_le_gt_dec with i0 (N*2*id - i + 1).

      (* The two left edges of TL[id]. *)
      decide id=0; [right; unfold space; forward; unfold fst, snd in *; omega|].

      left; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id - 1); forward; try omega.
      unfold sends_synth; simpl; forward.

      destr_case (id=?id-1-1); destr_case (id=?id-1+1).
      simplify sets with ceval; forward.
      exists (i - 1); forward; try omega.
      clear H11.
      decide i0=(N*2*id - i).
      rhs; forward.
      exists i; forward; try omega. nia.
      decide i0=(N*2*id - i + 1).
      lhs; forward.
      nia.
      nia.
      exfalso; omega.

      (* The rest of TL[id]. *)
      left. lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists (i0-1); forward; try omega.

      (** COMP1, TL, last dependency (south-east). *)
      destruct Z_le_gt_dec with (N*2*id + i - 2) i0.

      (* The two right edges of TL[id]. *)
      left; lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists (i0+1); forward; omega.

      (* Interior of TL[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists (i0+1); forward; omega.

      (** COMP1, TR, first dependency (south). *)
      assert (HT : N*2*id + N*2 - i = i0 \/ i0 = N*2*id + N*2 + i - 1
                   \/ N*2*id + N*2 - i < i0 < N*2*id + N*2 + i - 1)
        by omega; destruct HT as [?|[?|?]].

      (* Left edge of TR[id]. *)
      left; lhs; lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (* Right edge of TR[id]. *)
      decide id=(P-1); [right; unfold space; forward; unfold fst, snd in *; nia|].

      left; lhs; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id+1); forward; try omega.
      unfold sends_synth; simpl; forward.

      destr_case (id =? id + 1 - 1).
      forward.
      exists (i-1); forward; try omega.
      simplify sets with ceval.
      lhs; forward. nia.
      nia.

      (* Interior of TR[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists i0; forward; omega.

      (** COMP1, TR, second dependency (south-west). *)
      destruct Z_le_gt_dec with i0 (N*2*id + N*2 - i + 1).

      (* Left edge of TR[id]. *)
      left; lhs; lhs; lhs; lhs; forward.
      exists 0; forward.
      unfold computes_synth; simpl; simplify sets with ceval; forward.
      exists (i-1); forward; try omega.
      exists (i0-1); forward; try omega.

      (* Interior of TR[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists (i0-1); forward; try omega.

      (** COMP1, TR, last dependency (south-east). *)
      destruct Z_le_gt_dec with (N*2*id + N*2 + i - 2) i0.

      (* Right edge of TR[id]. *)
      decide id=(P-1); [right; unfold space; forward; unfold fst, snd in *; nia|].

      left; lhs; lhs; lhs; rhs; forward.
      exists 0; forward.
      exists (id+1); forward; try omega.
      unfold sends_synth; simpl; simplify sets with ceval.
      destr_case (id =? id + 1 - 1); forward.
      exists (i-1); forward; try omega.
      clear H10; decide i0=(N*2*id + N*2 + i - 1).

      rhs; forward.
      exists i; forward; try omega. nia.
      lhs; forward; nia.

      (* Interior of TR[id]. *)
      left; lhs; rhs; forward.
      exists (i-1); forward; try omega.
      exists (i0+1); forward; try omega.

      omega.

  (** Second goal is the verification conditions for the communication steps,
   * which are trivial. *)
  - destruct (to =? id - 1); forward.
    destruct (to =? id + 1); forward.

  (** Third goal is "conservation of knowledge": we are not allowed to send
   * a value that we don't know. *)
  - unfold af_synth, computes_synth, sends_synth in *; simpl in *.
    simplify sets with ceval.
    repeat intro; lhs.

    destruct (to =? id - 1); forward.
    (* Left border *)
    exists 0; simpl; forward. (* Time step 0 *)
    exists x0; forward.
    exists (snd x); rewrite H10; simpl; forward'; omega.
    exists 0; simpl; forward. (* Time step 0 *)
    exists (x1 - 1); forward; try omega.
    exists (snd x); rewrite H11; simpl; forward'; try omega.
    repeat rhs; forward; omega.

    destruct (to =? id + 1); simpl; forward.

    (* Right border *)
    exists 0; simpl; forward. (* Time step 0 *)
    exists x0; forward.
    exists (snd x); rewrite H10; simpl; forward'; try omega.
    exists 0; simpl; forward. (* Time step 0 *)
    exists (x1 - 1); forward; try omega.
    exists (snd x); rewrite H11; simpl; forward'; try omega.
    repeat rhs; forward; omega.

  (** Last goal is completeness: we computed all the cells we were supposed
   * to compute. *)
  - unfold target, bf_synth, computes_synth, sends_synth; simpl.
    repeat intro.
    destruct x; forward; unfold fst, snd in *.

    (** We have to prove that [x] belongs to some T[I], TL[I] or TR[I], for
     * some "I". This "I" is obtained by take the quotient of x's abscissa
     * by 2N. *)
    pose (I := z0 / (N*2)).
    assert (HNT : N*2 > 0) by omega.
    to_ctx (Z_div_mod_spec z0 (N*2) HNT).
    exists I; forward.
    unfold I; nia.
    unfold I; nia.

    destruct seg_dec with (N*2*I + (N - 1 - z)) (N*2*I + N*2-(N - 1 - z)-1) z0 as [?|[?|?]];
      lhs; forward.

    (* Case T[I]. *)
    exists 0; simpl; simplify sets with ceval;
    forward; try omega. (* First computation step. *)
    exists (N - 1 - z); forward; try omega.
    exists z0; forward; try omega.

    (* Case TL[I]. *)
    exists 1; simpl; simplify sets with ceval;
    forward; try omega. (* Second computation step. *)
    lhs; forward. (* First sub-step *)
    exists (N - 1 - z); forward; try omega.
    exists z0; forward; try omega.
    unfold I; omega.

    (* Case TR[I] *)
    exists 1; simpl; simplify sets with ceval;
    forward; try omega. (* Second computation step. *)
    rhs; forward. (* Second sub-step *)
    exists (N - 1 - z); forward; try omega.
    exists z0; forward; try omega.
    unfold I; omega.
Qed.