Require Import StLib.Core.

Section VonNeumann1D.
  Variables n : nat.
  Variable T : nat.

  Instance VonNeumann1D : Stencil nat1 :=
  {
    space   := 〚0, n-1〛;
    nb_iter := T;
    pattern := [0; 1; 2];
    center  := 1
  }.
End VonNeumann1D.

Section Triangle.
  Variable n : nat.

  Definition compute_triangle :=
    (For i ∈〚0, n-1〛Do
         Compute 〚i, 2 * n - 1 - i〛× ⎨i⎬).

  Eval simpl in (shape compute_triangle).

  Tactic Notation "destruct" "pairs" :=
    repeat match goal with
             | [ x : @prod _ _ |- _ ] => destruct x
           end.

  Tactic Notation "generate" "proof" "obligations" :=
    apply PO_sound; simpl; firstorder.

  Tactic Notation "one" "step" :=
    unfold valid, closure;
    union with 1; unfold iter_next, next;

    match goal with
      | [ |- @is_in _ ?x (@union _ (@image _ _
          (@finite _ (@cons _ ?A (@nil _))) _))] =>
        union with A; firstorder;
        image with x;[|apply same_eq; firstorder]
    end;

    unfold boundary, extension, subset; firstorder;
    destruct pairs; simpl in *; subst;
    sets simpl;

    match goal with
      | [ H : depends _ _ _ |- _ ] => inversion H; clear H
    end.


  Lemma compute_triangle_valid :
    ∅ ⟿ ∅ ∪ shape compute_triangle // VonNeumann1D (2 * n) n.
  Proof.
    generate proof obligations.
    + one step.
    + unfold valid, closure.
      union with 1; unfold iter_next, next.
  Abort.
End Triangle.