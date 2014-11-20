Require Import Main.Stencils Model.

Require Import Setoid String ZArith.
Local Open Scope Z_scope.

(* ========================================================================== *)
Module Make (Cell : CELL) (Stencil : STENCIL Cell).

  Module Defs := Defs Cell Stencil.
  Export Defs.

  (* ======================================================================== *)
  Module EquivFacts.

    (** This module contains a few results stating the compatibility of all the
     * operations defined above with state equivalence.  They are probably
     * useless to the end user but are involved in a few important proofs
     * below. *)

    Instance Equivalence_equiv : Equivalence State.equiv.
    Proof.
      split; constructor; firstorder;
      now repeat match goal with [ H : _ |- _ ] => rewrite H end.
    Qed.

    Fact State_get_var :
      forall x y v, x ≈ y -> State.get_var x v = State.get_var y v.
    Proof. intros x y v H; now apply H. Qed.

    Fact State_set_var :
      forall x y v n,
        x ≈ y -> State.set_var x v n ≈ State.set_var y v n.
    Proof.
      intros x y v n H.
      split.
      intro w; simpl; destruct (string_dec w v); firstorder.
      firstorder.
    Qed.

    Fact State_set_cell :
      forall x y c,
        x ≈ y -> State.set_cell x c ≈ State.set_cell y c.
    Proof.
      intros x y c H.
      split.
      firstorder.
      intro c'; simpl; destruct (Cell.eq_dec c' c); firstorder.
    Qed.

    Fact Arith_eval :
       forall x y e,
         x ≈ y -> Arith.eval x e = Arith.eval y e.
    Proof.
      induction e; try
                     (simpl; intros;
                      rewrite IHe1 by exact H;
                      rewrite IHe2 by exact H;
                      reflexivity).
      + constructor.
      + firstorder.
    Qed.

    Fact Bool_eval :
      forall (b : Bool.t) (x y : State.t),
        x ≈ y -> Bool.eval x b = Bool.eval y b.
    Proof.
      induction b;
      simpl; intros;
      try (repeat match goal with
                    | [ H : State.equiv ?x ?y |- _ ] =>
                      rewrite (Arith_eval x y _) by assumption
                  end;
           reflexivity)
          || (erewrite IHb1 by exact H;
              erewrite IHb2 by exact H;
              reflexivity).
      now erewrite IHb by exact H.
    Qed.

    Fact Cell_eval :
      forall x y e,
        x ≈ y -> Cell.eval Arith.t (Arith.eval x) e =
                 Cell.eval Arith.t (Arith.eval y) e.
    Proof.
      intros.
      apply Cell.eval_ext.
      intros; now apply Arith_eval.
    Qed.

  End EquivFacts.

  (* ======================================================================== *)
  Module ImpFacts.

    (** This module contains results about the simple imperative
     * programs. *)

    Import EquivFacts.

    (** Assignments have a limited scope.  Programs are effect-free. *)
    Fact effect_free :
      forall s t p,
        p // s ⇓ t -> forall x, State.get_var s x = State.get_var t x.
    Proof.
      intros s t p H; induction H; try firstorder.
      now rewrite <- IHexec2, <- IHexec1.
      simpl; destruct (string_dec x0 x); subst.
      reflexivity.
      rewrite <- IHexec2, <- IHexec1.
      simpl; destruct (string_dec x0 x).
      contradiction.
      reflexivity.
    Qed.

    (** If, starting from two equivalent states, the execution of a program
     * terminates in two states, these states are equivalent as well.  That is,
     * this language is deterministic. *)
    Fact deterministic :
      forall p s1 s2 t1 t2,
        s1 ≈ s2 -> p // s1 ⇓ t1 -> p // s2 ⇓ t2 -> t1 ≈ t2.
    Proof.
      intros p s1 s2 t1 t2 E H.
      generalize dependent s2; generalize dependent t2.
      induction H; intros t2 s2 E H'; inversion H'; subst; try assumption.
      + unfold CEval in *; erewrite Cell_eval by eassumption.
        now apply State_set_cell.
      + apply IHexec with s2.
        assumption.
        now erewrite Bool_eval by eassumption.
      + apply IHexec2 with t0; [|assumption].
        apply IHexec1 with s2; assumption.
      + erewrite Arith_eval in H by eassumption.
        pattern (Arith.eval s a) in H.
        erewrite Arith_eval in H; [|eassumption].
        omega.
      + erewrite Arith_eval in H by eassumption.
        pattern (Arith.eval s b) in H.
        erewrite Arith_eval in H; [|eassumption].
        omega.
      + erewrite State_get_var by eassumption.
        unfold State.update, State.pack.
        rewrite State_set_var; [reflexivity|].
        apply IHexec2 with t0; [|assumption].
        apply IHexec1 with (State.set_var s2 x (Arith.eval s2 a)).
        erewrite Arith_eval by eassumption.
        unfold State.update, State.pack.
        erewrite State_set_var by eassumption.
        reflexivity.
        assumption.
    Qed.

  End ImpFacts.

  (* ======================================================================== *)
  Module Symbolic.

    Fixpoint eval (p : KStep.t) (s : State.t) : State.t :=
      match p with
        | Nop%step_t => s
        | (Fire c)%step_t => State.set_cell s (CEval s c)
        | (If b Then p1 Else p2)%step_t =>
          if Bool.eval s b then eval p1 s else eval p2 s
        | (p1;; p2)%step_t =>
          eval p2 (eval p1 s)
        | (For i From a To b Do q)%step_t =>
          s (* XXX: FIXME *)
      end.

    Definition comp_step (k : Kernel.t) (T : Time.t)
               (s : GState.t) : GState.t :=
      fun id => eval (Kernel.comp k) ((s id)⟨"id" ← id; "T" ← T⟩).

    Definition comm_pat (k : Kernel.t) (T : Time.t) (t : GState.t) :=
      fun id to =>
        eval (Kernel.comm k) State.initial⟨"id" ← id; "to" ← to; "T" ← T⟩.

    Definition comm_step (k : Kernel.t) (T : Time.t)
               (t : GState.t) : GState.t :=
      fun id => State.initial. (* XXX: FIXME *)
  End Symbolic.

  (* ======================================================================== *)
  Module Automation.

    (** Automation for proving correctness of distributed kernels. *)

    (** Syntactic sugar *)
    Tactic Notation "halts" "after" constr(n) "steps" :=
      exists (n : Z).

  End Automation.

  Export Automation.

End Make.
