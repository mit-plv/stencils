Require Import Main.Stencils Main.Sets Model.

Require Import Setoid String ZArith List.
Import ListNotations.
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
  Module WEquivFacts.

    (** Two states are weakly equivalent if they assign the same value to
     * variables. *)
    Definition weak_equiv s t :=
      forall x, State.get_var s x = State.get_var t x.

    (** If two states are weakly equivalents, updating them (in the same way!)
     * yields two weakly equivalent states. *)
    Fact set_var_weq :
      forall s t,
        weak_equiv s t -> forall x v, weak_equiv (s⟨x ← v⟩) (t⟨x ← v⟩).
    Proof.
      unfold weak_equiv, State.get_var; intros s t H x v x'.
      destruct s, t; simpl in *.
      destruct (string_dec x' x); firstorder.
    Qed.

    (** Arithmetic expressions are invariant through any change of weakly
     * equivalent state. *)
    Fact Arith_eval_weq :
      forall s t,
        weak_equiv s t -> forall e, Arith.eval s e = Arith.eval t e.
    Proof.
      intros s t H; induction e; simpl; try now rewrite IHe1, IHe2.
      reflexivity.
      now rewrite H.
    Qed.

    (** The same results holds for boolean expressions. *)
    Fact Bool_eval_weq :
      forall s t,
        weak_equiv s t -> forall e, Bool.eval s e = Bool.eval t e.
    Proof.
      intros s t H; induction e; simpl;
      try now rewrite (Arith_eval_weq s t H t0), (Arith_eval_weq s t H t1).
      reflexivity.
      now rewrite IHe.
      now rewrite IHe1, IHe2.
      now rewrite IHe1, IHe2.
    Qed.

  End WEquivFacts.

  (* ======================================================================== *)
  Module ImpFacts.

    (** This module contains results about the simple imperative
     * programs. *)

    Import EquivFacts.
    Import WEquivFacts.

    (** Assignments have a limited scope.  Programs are effect-free. *)
    Fact effect_free :
      forall s t p,
        p // s ⇓ t -> weak_equiv s t.
    Proof.
      intros s t p H; induction H; try firstorder;
      unfold weak_equiv in *; intros.
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

    Import WEquivFacts.

    (** The correctness of distributed kernels has been defined using traces.
     * In this module, we take advantage of the fact that Stencil code can be
     * written using a simple, non Turing-complete language to automatically
     * synthesize these traces. *)

    Open Scope set_scope.

    Definition reflects (s : State.t) (S : set Cell.t) :=
      forall c, State.get_cell s c = true <-> c ∈ S.

    Fixpoint exec (p : Imp.t) (s : State.t) : set Cell.t :=
      match p with
        | Nop%prog_t => ∅
        | (Flag c)%prog_t => ⎨CEval s c⎬
        | (If b Then p1 Else p2)%prog_t =>
          if Bool.eval s b then exec p1 s else exec p2 s
        | (p1;; p2)%prog_t =>
          exec p1 s ∪ exec p2 s
        | (Assert _)%prog_t => ∅
        | (For x From a To b Do q)%prog_t =>
          ⋃⎨exec q (s⟨x ← k⟩), k ∈〚Arith.eval s a , Arith.eval s b〛⎬
      end.

    Fixpoint VC (p : Imp.t) (s : State.t) (S : set Cell.t) : Prop :=
      match p with
        | Nop%prog_t => True
        | (Flag c)%prog_t => True
        | (If b Then p1 Else p2)%prog_t =>
          if Bool.eval s b then
            VC p1 s S
          else
            VC p2 s S
        | (p1;; p2)%prog_t =>
          VC p1 s S /\
          forall t, weak_equiv s t -> reflects t (S ∪ exec p1 s) ->
                    VC p2 t (S ∪ exec p1 s)
        | (Assert P)%prog_t =>
          reflects s S -> P s
        | (For x From a To b Do q)%prog_t =>
          forall i,
            Arith.eval s a <= i <= Arith.eval s b ->
            VC q (s⟨x ← i⟩) (exec (For x From a To i Do q)%prog_t s)
      end.

  End Symbolic.

  Module SymbFacts.

    Import Symbolic.
    Import WEquivFacts.

    Fact reflects_same :
      forall s S1 S2,
        S1 ≡ S2 -> reflects s S1 -> reflects s S2.
    Proof. firstorder. Qed.

    Ltac clear_sets :=
      unfold reflects, same, is_in, bin_union, empty, singleton,
      seg_union in *.

    Lemma exec_indep :
      forall p,
      forall s t, weak_equiv s t -> exec p s ≡ exec p t.
    Proof.
      induction p; simpl; intros.
      + clear_sets; easy.
      + clear_sets.
        unfold CEval; intros; split; intros;
        erewrite Cell.eval_ext; try eassumption.
        now apply Arith_eval_weq.
        intros; symmetry; now apply Arith_eval_weq.
      + erewrite Bool_eval_weq; try eassumption.
        destruct (Bool.eval t0 t); [now apply IHp1 | now apply IHp2].
      + admit. (* XXX: FIXME, simple fact from set theory. *)
      + firstorder.
      + clear_sets.
        intro c; split; intro H'.
        * destruct H' as [k [Hk1 Hk2]].
          exists k.
          rewrite (Arith_eval_weq s0 t1 H), (Arith_eval_weq s0 t1 H) in Hk1.
          intuition.
          specialize (IHp (s0 ⟨s ← k⟩) (t1 ⟨s ← k⟩)).
          apply IHp.
          now apply set_var_weq.
          assumption.
        * destruct H' as [k [Hk1 Hk2]].
          exists k.
          rewrite (Arith_eval_weq s0 t1 H), (Arith_eval_weq s0 t1 H).
          intuition.
          specialize (IHp (s0 ⟨s ← k⟩) (t1 ⟨s ← k⟩)).
          apply IHp.
          now apply set_var_weq.
          assumption.
    Qed.

(*    Fact VC_weq :
      forall p s t S, VC p s S -> weak_equiv s t -> reflects t S -> VC p t S.
    Proof.
      induction p; simpl; intros; auto.
      + rewrite <- (Bool_eval_weq s t0 H0 t).
        destruct (Bool.eval s t); auto.
        * apply IHp1 with s; auto.
        * apply IHp2 with s; auto.
      + intuition.
        * apply IHp1 with s; auto.
        * apply IHp2 with s; auto.
          admit.
      +
    Admitted.
*)
    Fact VC_correctness :
      forall p s S,
        reflects s S -> VC p s S ->
        exists t, p // s ⇓ t /\ reflects t (S ∪ exec p s).

    Proof.
      induction p; simpl; intros s' S H HVC.
      + (exists s'; split; [constructor|firstorder]).
      + (exists (State.set_cell s' (CEval s' c))); split.
        now constructor.
        destruct s'; unfold reflects, State.set_cell, State.get_cell;
        simpl.
        intro c0; destruct (Cell.eq_dec c0 (CEval (z, b) c)); firstorder.
      + remember (Bool.eval s' t) as b; symmetry in Heqb.
        destruct b.
        * destruct (IHp1 s' S H HVC) as [u Hu].
          exists u; split.
          constructor; now rewrite Heqb.
          apply Hu.
        * destruct (IHp2 s' S H HVC) as [u Hu].
          exists u; split.
          constructor; now rewrite Heqb.
          apply Hu.
      + destruct HVC as [H1 H2].
        destruct (IHp1 s' S H H1) as [t [Ht1 Ht2]].
        specialize (H2 t (ImpFacts.effect_free _ _ _ Ht1) Ht2).
        destruct (IHp2 t (S ∪ exec p1 s') Ht2 H2)
          as [u [Hu1 Hu2]].
        exists u; split.
        econstructor; eassumption.
        eapply reflects_same; [|eassumption].
        admit. (* XXX: FIXME, set theory *)
      + (exists s'; split).
        constructor; auto.
        eapply reflects_same; [|eassumption].
        firstorder.
      +
    Admitted.

(*    Ltac invert_exec :=
      repeat match goal with
        | [ H : Imp.exec _ Imp.NoOp _ |- _ ] =>
          inversion H; clear H; subst
        | [ H : Imp.exec _ (Imp.Flag _) _ |- _ ] =>
          inversion H; clear H; subst
        | [ H : Imp.exec _ (Imp.Cond _ _ _) _ |- _ ] =>
          inversion H; clear H; subst
        | [ H : Imp.exec _ (Imp.Seq _ _) _ |- _ ] =>
          inversion H; clear H; subst
        | [ H : Imp.exec _ (Imp.Assert _) _ |- _ ] =>
          inversion H; clear H; subst
      end.

    Import WEquivFacts.

    Fact exec_reflects :
      forall F p s t,
        (denote p F) // s ⇓ t ->
        forall S, reflects s S -> reflects t (S ∪ exec p s).
    Admitted.

    Fact PO_weq :
      forall p s t, PO p s -> weak_equiv s t -> PO p t.
    Proof.
    Admitted.

    Fact arith_ind :
      forall P,
        (forall s a b, Arith.eval s a > Arith.eval s b -> P s a b) ->
        (forall s a b, Arith.eval s a = Arith.eval s b -> P s a b) ->
        (forall s a b, Arith.eval s a <= Arith.eval s b -> P s a b ->
                       P s (1 + a)%arith_t b) ->
        forall s a b, P s a b.
    Proof.
      intros P Hi He Hind s a b.
      destruct Z_le_gt_dec with (Arith.eval s a) (Arith.eval s b).
      2: now apply Hi.
      assert (X : forall k u v, k >= 0 ->
                                Arith.eval s u + k = Arith.eval s v -> P s u v).
      destruct k.
      intros; apply He; omega.
      admit.
      now destruct 1.

      apply X with (Arith.eval s b - Arith.eval s a); omega.
    Qed.

    Fact PO_correct :
      forall F p s,
        PO (denote p F) s -> exists t, (denote p F) // s ⇓ t.
    Proof.
      intro F; induction p; simpl; intros.
      + (exists s; constructor).
      + (exists (State.set_cell s (CEval s c)); econstructor);
        now constructor.
      + remember (Bool.eval s t) as b; symmetry in Heqb.
        destruct b.
        * destruct (IHp1 s H) as [u Hu].
          exists u; constructor.
          now rewrite Heqb.
        * destruct (IHp2 s H) as [u Hu].
          exists u; constructor.
          now rewrite Heqb.
      + destruct H as [H1 H2].
        destruct (IHp1 s H1) as [t Ht].
        apply (PO_weq _ s t) in H2.
        destruct (IHp2 t H2) as [u Hu].
        exists u.
        econstructor; eassumption.
        eapply ImpFacts.effect_free; eassumption.
      + generalize dependent t0; generalize dependent t;
        generalize dependent s0.
        intros s0 t t0; pattern s0, t, t0; apply arith_ind; intros.
        * (exists s1; constructor; omega).
        * destruct IHp with (s1 ⟨s ← (Arith.eval s1 a)⟩).
          apply H0; omega.
          exists x⟨s ← (State.get_var s1 s)⟩.
          econstructor.
          omega.
          eassumption.
          constructor.
          rewrite <- (Arith_eval_weq (s1 ⟨s ← (Arith.eval s1 a)⟩) x).
          rewrite <- (Arith_eval_weq (s1 ⟨s ← (Arith.eval s1 a)⟩) x).
          (*change (Arith.eval s1 b < 1 + Arith.eval s1 a); omega.
          eapply ImpFacts.effect_free.*)
    Abort.
*)
  End SymbFacts.

End Make.
