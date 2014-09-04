Require Import StLib.Verification.

(** Example *)

(** We start by defining a stencil and a simple expression
 *  language for our programs *)

Require Import Arith NPeano Omega.
Hint Resolve Nat.mul_div_le Nat.mul_succ_div_gt.

Parameter w h : nat.
Axiom w_nz : w <> 0.
Axiom h_nz : h <> 0.
Parameter xs ys : nat.

Module BL_BR <: Stencil.
  Definition cell := (nat*nat)%type.

  Inductive dep_ : cell -> cell -> Prop :=
    | BL_dep : forall i j, dep_ (i,j)   (1+i,1+j)
    | BR_dep : forall i j, dep_ (1+i,j) (i,1+j).
  Definition dep := dep_.

  Inductive final_ : cell -> Prop :=
    | fin : forall i j, i < w * xs -> j < h * ys -> final_ (i,j).
  Definition final := final_.
End BL_BR.
Import BL_BR.

Module L <: Lg.
  Inductive Var_ : Type -> Type :=
    | X : Var_ nat
    | Y : Var_ nat.
  Definition Var := Var_.

  Inductive Expr_ : Type -> Type :=
    | Const : forall {A}, A -> Expr_ A
    | Emb : forall {A}, Var A -> Expr_ A
    | Cell : Expr_ nat -> Expr_ nat -> Expr_ cell
    | Add : Expr_ nat -> Expr_ nat -> Expr_ nat
    | Sub : Expr_ nat -> Expr_ nat -> Expr_ nat
    | LtE : Expr_ nat -> Expr_ nat -> Expr_ bool.
  Definition Expr := Expr_.

  Definition V {A} := Emb (A:=A).

  Definition state := (nat * nat)%type.

  Definition getX (r : state) := fst r.
  Definition getY (r : state) := snd r.

  Definition upd (A : Type) : state -> Var A -> A -> state :=
    fun e x => 
      match x in Var_ A return A -> state with
        | X => fun vx => (vx,getY e)
        | Y => fun vy => (getX e,vy)
      end.

  Fixpoint eval (A : Type) (r : state) (e : Expr A) :=
    match e in Expr_ A return A with
      | Const _ x => x
      | Emb _ x => match x with
                     | X => getX r
                     | Y => getY r
                   end
      | Cell e1 e2 => (eval _ r e1,eval _ r e2)
      | Add e1 e2 => eval _ r e1 + eval _ r e2
      | Sub e1 e2 => eval _ r e1 - eval _ r e2
      | LtE e1 e2 => NPeano.ltb (eval _ r e1) (eval _ r e2)
    end.

  Definition Lt := LtE.
  Definition Incr := fun v => Add (V v) (Const 1).
End L.

Module Kern := (Kernel BL_BR L).

Section Algo.
  Import L.
  Import Kern.Program.

  (** Here is the program itself*)

  Definition comp t n := 
    iFor X (Const 0) (Const w)
         (iOut (Cell (Add (V X) (Const (w * n))) (Const t))).

  Definition send (t : nat) n1 n2 :=
    if eq_nat_dec n1 (1+n2) then
      iOut (Cell (Const (w * n1)) (Const t))
    else
      if eq_nat_dec n2 (1+n1) then
        iOut (Cell (Const (w * (1+n1) - 1)) (Const t))
      else
        iNop.

  Definition prog := Kern.mkAlgo (h * ys) comp send.

  (** Proof of correctness *)

  Hint Rewrite mult_plus_distr_l : my_arith.

  Ltac ineq :=
    subst;
    try (match goal with
           | [H : 1 + ?x = _ |- _ <= ?x ] =>
             apply plus_le_reg_l with 1; rewrite H
           | [H : 1 + ?x = _ |- ?x <= _ ] =>
             apply plus_le_reg_l with 1; rewrite H
           | [H : 1 + ?x = _ |- ?x < _ ] =>
             apply plus_lt_reg_l with 1; rewrite H
           | [H : 1 + ?x = _ |- _ < ?x ] =>
             apply plus_lt_reg_l with 1; rewrite H
         end);
    try ((try subst); omega) || (autorewrite with my_arith; omega).

  Theorem prog_correct : Kern.correct prog.
  Proof.
    generalize w_nz; intro.
    unfold Kern.correct.
    exists (fun t n c => (w * n <= fst c < w * (1+n) \/
                          S (fst c) = w * n \/ fst c = w * (S n))/\ snd c < t).
    intuition.
    * apply Kern.MakeStep with
      (computed := fun n c => w * n <= fst c < w * (1 + n) /\ snd c = T)
      (sent := fun n n' c => (n = 1 + n' /\ fst c = w * n /\ snd c = T)
                             \/ (n' = 1 + n /\ 1 + fst c = w * n' /\ snd c = T)).
      - intros; simpl.
        apply vc_sound; simpl.
        left; firstorder; [destruct w; auto|].
        exists
          (fun s =>
             getX (fst s) <= w /\
             forall i j,
               get s (i,j) <->
               (w*n <= i < w*(1+n) /\ j < T) \/
               (w*n <= i < w*n + getX (fst s) /\ j = T) \/
               ((S i = w*n \/ i = w*(S n)) /\ j < T)).
        exists (Sub (Const w) (V X)).
        simpl in *; intuition;
        try destruct s'; simpl in *.
        inversion H1.
        apply H4.
        destruct (getX s); simpl in *; intuition.
        injection H7; intro. destruct eq_nat_dec with n0 w.
        intuition.
        left; intuition; subst.
        apply lt_le_trans with (w + w * n).
        apply plus_lt_compat_r. omega.
        pattern w at 1; rewrite <- Nat.mul_1_r.
        rewrite <- mult_plus_distr_l.
        now simpl.
        apply H4.
        destruct eq_nat_dec with (S (getX s)) w.
        right; right; intuition.
        right. simpl. rewrite <- plus_Sn_m.
        rewrite e. 
        pattern w at 1; rewrite <- Nat.mul_1_r.
        rewrite <- mult_plus_distr_l.
        now simpl.
        left; intuition. simpl. rewrite <- plus_Sn_m.
        apply lt_le_trans with (w + w*n).
        apply plus_lt_compat_r.
        assert (getX s < w). admit. omega. (* That's just an arithmetic fact *)
        pattern w at 1; rewrite <- Nat.mul_1_r.
        rewrite <- mult_plus_distr_l.
        now simpl.

        apply ltb_lt in H2; omega.
        destruct H1.
        injection H1; intros; subst; intuition.
        apply H4 in H1; intuition.
        right; apply H4; intuition.
        destruct eq_nat_dec with i (getX s + w*n).
        left; subst; auto.
        right. apply H4; omega.
        right. apply H4; omega.
        right. apply H4; omega.
        apply ltb_lt in H2; omega.
        destruct t0; simpl in *; apply H4.
        assert (w <= getX s). admit. (* Same thing here and for the next admits *)
        left; intuition.
        destruct t0; simpl in *; apply H4.
        right; intuition.
        destruct t0; simpl in *; subst.
        apply H4; omega.
        destruct t0; simpl in *; subst.
        assert (w <= getX s). admit.
        rewrite <- Nat.add_1_r in H7.
        rewrite mult_plus_distr_l in H7; apply H4; omega.
        destruct t0; simpl in *. apply H4 in H1.
        destruct H1; intuition.
        right; intuition.
        assert (w <= getX s). admit.
        rewrite <- Nat.add_1_r. rewrite mult_plus_distr_l; omega.

      - intros. simpl. unfold send.
        destruct (eq_nat_dec n (1 + n')).
        apply vc_sound; simpl.
        firstorder; destruct t0; firstorder.
        injection H1; firstorder.
        destruct (eq_nat_dec n' (1+n)).
        apply vc_sound; simpl.
        intros [? ?]; firstorder.
        simpl in *; subst. left.
        assert(n1 = w * S n - 1) by omega.
        now subst.
        injection H1; simpl; subst; firstorder.
        right; intuition. simpl. admit.
        apply vc_sound; simpl.
        intros [? ?]; intuition.
        inversion H1.

      - firstorder.
        ineq; auto.
        destruct eq_nat_dec with (snd c) T; intuition.
        destruct eq_nat_dec with (snd c) T; intuition.
        destruct n. rewrite Nat.mul_0_r in H1; inversion H1.
        intuition eauto.
        destruct eq_nat_dec with (snd c) T; intuition.
        intuition eauto.

      - intuition.
        right; intuition. rewrite H2; ineq.
        right; intuition; ineq.

    * inversion H0; clear H0; simpl.
      exists (i / w); intuition eauto.
  Qed.
End Algo.
