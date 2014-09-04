Require Import AbstractStencil.

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

    Ltac my_case e :=
      let b := fresh "b" in
      remember e as b; destruct b.

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