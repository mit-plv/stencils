Ltac my_case e :=
  let b := fresh "b" in
  remember e as b; destruct b.

(** Abstract notion of stencil *)

Module Type Stencil.
  Parameter cell : Set.
  Parameter dep : cell -> cell -> Prop.
  Parameter final : cell -> Prop.
End Stencil.

(** In the sequel, we formalize a variant of Hoare Logic allowing
 *  to prove the correctness of single-threaded programs with
 *  respect to a given stencil.
 *  The general design is based on code written by Silvain Boulmé,
 *  available in Coq's users' contributions (Hoaretut). *)

(** Expression language for our toy programming language *)

Module Type Lg.
  Parameter Var : Type -> Type.
  Parameter Expr : Type -> Type.
  Parameter V : forall {A}, Var A -> Expr A.

  Parameter state : Type.
  Parameter upd : forall {A}, state -> Var A -> A -> state.
  Parameter eval : forall {A}, state -> Expr A -> A.

  Parameter Lt : Expr nat -> Expr nat -> Expr bool.
  Parameter Incr : Var nat -> Expr nat.
End Lg.

Module mkProgram (Import S : Stencil) (Import L : Lg).

  (** Extended states--take into account both variables and
   *  boolean arrays representing whether a cell's computation
   *  has been fired or not. *)

  Definition array := cell -> Prop.
  Definition ex_state := (state * array)%type.
  Definition prop := ex_state -> Prop.

  Definition put (e : ex_state) (c : cell) :=
    let (s,f) := e in
    (s,fun x => x = c \/ f x).
  
  Definition get (e : ex_state) (c : cell) :=
    snd e c.

  (** Non-terminating imperative programs *)

  Inductive nt : Type :=
    | pNop    : nt
    | pAssert : prop -> nt
    | pSeq    : nt -> nt -> nt
    | pSet    : Var nat -> Expr nat -> nt
    | pOut    : Expr cell -> nt
    | pIf     : Expr bool -> nt -> nt -> nt
    | pWhile  : Expr bool -> nt -> nt.

  (** Operational semantics *)

  Inductive exec : nt -> ex_state -> ex_state -> Prop :=
    | eNop    : forall s, exec pNop s s
    | eAssert : forall s (p : prop), p s  -> exec (pAssert p) s s
    | eSet    : forall s v e,
                  exec (pSet v e) s (upd (fst s) v (eval (fst s) e),snd s)
    | eSeq    : forall s0 s1 s2 p0 p1, exec p0 s0 s1 -> exec p1 s1 s2 ->
                                       exec (pSeq p0 p1) s0 s2
    | eOut    : forall s c, exec (pOut c) s (put s (eval (fst s) c))
    | eIfT    : forall (s0 s1 : ex_state) (e : Expr bool) a b,
                  eval (fst s0) e = true ->
                  exec a s0 s1 ->
                  exec (pIf e a b) s0 s1
    | eIfF    : forall (s0 s1 : ex_state) (e : Expr bool) a b,
                  eval (fst s0) e = false ->
                  exec b s0 s1 ->
                  exec (pIf e a b) s0 s1
    | eWhile  : forall b p s0 s1,
                  exec (pIf b (pSeq p (pWhile b p)) pNop) s0 s1 ->
                  exec (pWhile b p) s0 s1.
  
  Hint Constructors nt exec.

  (** This language is deterministic... *)

  Theorem deterministic :
    forall p s0 s1, exec p s0 s1 -> forall s2, exec p s0 s2 -> s1 = s2.
  Proof.
    intros ? ? ? H; induction H;
    intros ? H'; inversion H'; clear H'; subst; firstorder.
    apply IHexec1 in H3; subst.
    now apply IHexec2.
    rewrite H in H6; discriminate.
    rewrite H in H6; discriminate.
  Qed.

  (** Hoare logic for this simple language *)

  Section VC.
    Require Import Wf_nat.
    Require Import Omega.

    Lemma expr_nat_ind :
      forall P : ex_state -> Expr nat -> Prop,
        (forall n, (forall s e, eval (fst s) e < n -> P s e) ->
                    forall s e, eval (fst s) e = n -> P s e) ->
        forall s e, P s e.
    Proof.
      intros P Hr.
      cut (forall n s e, eval (fst s) e = n -> P s e); eauto.
      intro n; pattern n.
      apply well_founded_ind with lt; eauto; auto with arith.
    Qed.

    Fixpoint vc (p : nt) (post : prop) : prop :=
      match p with
        | pNop => post
        | pAssert q => fun s => q s /\ post s
        | pSeq p1 p2 => vc p1 (vc p2 post)
        | pSet v e => fun s => post (upd (fst s) v (eval (fst s) e),snd s)
        | pOut c => fun s => post (put s (eval (fst s) c))
        | pIf b p1 p2 =>
          fun s =>
            (eval (fst s) b = true  /\ vc p1 post s) \/
            (eval (fst s) b = false /\ vc p2 post s)
        | pWhile b q => 
          fun s =>
            exists i v, i s
            /\ (forall s',
                  i s' -> eval (fst s') b = true ->
                  vc q (fun t => i t /\ eval (fst t) v < eval (fst s') v) s')
            /\ (forall s',
                  i s' -> eval (fst s') b = false -> post s')
      end.

    Theorem vc_sound :
      forall p post s,
        vc p post s -> exists t, exec p s t /\ post t.
    Proof.
      induction p; simpl; try (now firstorder eauto); intros.

      (* Seq *)
      destruct IHp1 with (vc p2 post) s; firstorder.
      destruct IHp2 with post x; firstorder eauto.

      (* While *)
      destruct H as [i [v H]].
      generalize H IHp; clear H IHp.
      pattern s, v; apply expr_nat_ind; clear s v.
      intros; destruct n.
      destruct H1; destruct H2; specialize (H3 s).
      my_case (eval (fst s) e); symmetry in Heqb.
      destruct IHp with (fun s' => i s' /\
                                   eval (fst s') e0 < eval (fst s) e0) s.
      firstorder.
      rewrite H0 in H4. destruct H4; destruct H5; inversion H6.
      firstorder.

      my_case (eval (fst s) e); symmetry in Heqb; [|firstorder].

      destruct IHp with (fun s' => i s' /\
                                   eval (fst s') e0 < eval (fst s) e0) s.
      firstorder.
      destruct H with x e0; firstorder eauto; omega.
    Qed.

  End VC.

  Section Refinement.
    Inductive rSpec : Type :=
      | rBrack  : prop -> prop -> rSpec
      | rSingle : nt -> rSpec
      | rSeq    : rSpec -> rSpec -> rSpec
      | rIf     : Expr bool -> rSpec -> rSpec -> rSpec
      | rWhile  : Expr bool -> rSpec -> rSpec.

    Inductive interp : rSpec -> nt -> Prop :=
      | riBrack :
          forall p (P Q : prop), (forall s, P s -> exists t, exec p s t /\ Q t) ->
                                 interp (rBrack P Q) p
      | riSingle : forall p, interp (rSingle p) p
      | riSeq    : forall p1 p2 s1 s2, interp s1 p1 -> interp s2 p2 ->
                                       interp (rSeq s1 s2) (pSeq p1 p2)
      | riIf     : forall p1 p2 s1 s2 b, interp s1 p1 -> interp s2 p2 ->
                                         interp (rIf b s1 s2) (pIf b p1 p2)
      | riWhile  : forall p s b, interp s p -> interp (rWhile b s) (pWhile b p).

    Definition refines (U V : rSpec) : Prop :=
      forall s, interp U s -> interp V s.
    Notation "a <| b" := (refines a b) (at level 100).

    Hint Constructors rSpec.
    Hint Unfold refines.

    Ltac invert_interp :=
      repeat match goal with
               | H : interp _ _ |- _ => inversion H; try subst; clear H
             end.

    Lemma ref_seq : forall P Q R, rSeq (rBrack P R) (rBrack R Q) <| rBrack P Q.
    Proof.
      repeat intro. invert_interp.
      constructor; intros.
      destruct H4 with s; auto.
      destruct H3 with x; firstorder eauto.
    Qed.

    Lemma ref_if :
      forall P Q b,
        rIf b (rBrack (fun s => P s /\ eval (fst s) b = true)  Q)
              (rBrack (fun s => P s /\ eval (fst s) b = false) Q) <| rBrack P Q.
    Proof.
      repeat intro. invert_interp.
      constructor; intros.
      specialize (H2 s); specialize (H3 s).
      my_case (eval (fst s) b); firstorder eauto.
    Qed.

    Lemma ref_stronger_post :
      forall P Q R : prop, (forall s, R s -> Q s) -> (rBrack P R <| rBrack P Q).
    Proof.
      repeat intro. invert_interp.
      constructor; firstorder.
    Qed.

    Lemma ref_weaker_pre :
      forall P Q R : prop, (forall s, P s -> R s) -> (rBrack R Q <| rBrack P Q).
    Proof.
      repeat intro. invert_interp.
      constructor; firstorder.
    Qed.
  End Refinement.

  (** Now we define a simpler, non-Turing-complete language *)

  Inductive t : Type :=
    | iNop : t
    | iSeq : t -> t -> t
    | iOut : Expr cell -> t
    | iIf  : Expr bool -> t -> t -> t
    | iFor : Var nat -> Expr nat -> Expr nat -> t -> t.

  (** The semantics of this language is given by a compiler to
   *  the previouly defined language. *)

  (** First flavour. 'Safe' operational semantics--fails if a
   *  dependency is not satisfied *)

  Fixpoint safe (p : t) : nt :=
    match p with
      | iNop => pNop
      | iSeq a b => pSeq (safe a) (safe b)
      | iOut c => pSeq (pAssert (fun s => forall d,
                                            dep d (eval (fst s) c) -> get s d))
                       (pOut c)
      | iIf b p1 p2 => pIf b (safe p1) (safe p2)
      | iFor v e1 e2 q =>
        pIf (Lt e1 e2)
            (pSeq (pSet v e1)
                  (pWhile (Lt (V v) e2)
                          (pSeq (safe q)
                                (pSet v (Incr v)))))
            pNop
    end.

  (** Second flavour. 'Unsafe' operational semantics--does not
   *  care about dependencies *)

  Fixpoint unsafe (p : t) : nt :=
    match p with
      | iNop => pNop
      | iSeq a b => pSeq (unsafe a) (unsafe b)
      | iOut c => pOut c
      | iIf b p1 p2 => pIf b (unsafe p1) (unsafe p2)
      | iFor v e1 e2 q =>
        pIf (Lt e1 e2)
            (pSeq (pSet v e1)
                  (pWhile (Lt (V v) e2)
                          (pSeq (unsafe q)
                                (pSet v (Incr v)))))
            pNop
    end.

  Hint Unfold safe unsafe.
End mkProgram.

Module Kernel (Import S : Stencil) (Import L : Lg).
  Module Program := mkProgram S L.

  (* XXX: Perhaps this should be a parameter *)
  Definition node := nat.

  (** This is our notion of distributed programs *)

  Record t := mkAlgo
  {
    nbRuns : nat;
    comp : nat -> node -> Program.t;
    send : nat -> node -> node -> Program.t
  }.

  Definition state := node -> Program.array.
  Definition empty : Program.array := fun _ => False.

  (** Operational semantics of these distributed kernels *)

  Inductive step (T : nat) (p : t) (s1 s2 : state) : Prop :=
    | MakeStep :
        forall (computed : state) (sent : node -> state),
          (forall n c,
           exists s, Program.exec (Program.safe (comp p T n))
                                  (c,s1 n) s /\ forall t, (s1 n t \/ computed n t)
                                                          <-> snd s t) ->
(*           exists c', Program.exec (Program.safe (comp p T n))
                                   (c,s1 n) (c',computed n)) ->*)
          (forall n n' c,
           exists s, Program.exec (Program.unsafe (send p T n n'))
                                  (c,empty) s /\ forall t, sent n n' t <-> snd s t) ->
          (forall n c, (s1 n c \/ computed n c \/ exists n', sent n' n c)
                       <-> s2 n c) ->
          (forall n n' c, sent n n' c -> s1 n c \/ computed n c) ->
          step T p s1 s2.

  (** Correctness of a program with respect to a stencil *)

  Definition correct (p : t) :=
    exists s : nat -> state, 
      (forall T, T < nbRuns p -> step T p (s T) (s (1+T))) /\
      (forall c, final c -> exists n, s (nbRuns p) n c).
End Kernel.





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