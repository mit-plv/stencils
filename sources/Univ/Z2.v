Require Import Main.Stencils.

Require Export ZArith.
Open Scope Z_scope.

Module Z2 <: CELL.

  Definition t := (Z * Z)%type.

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [n1 n2].
    destruct y as [m1 m2].
    destruct Z.eq_dec with n1 m1; destruct Z.eq_dec with n2 m2; subst;
    [left; f_equal| | |]; right; intro H; now injection H.
  Defined.

  Definition add x y := (fst x + fst y, snd x + snd y).
  Definition minus x := (-fst x, -snd x).
  Definition zero := (0,0).

  Fact add_assoc :
    forall u v w, add u (add v w) = add (add u v) w.
  Proof.
    intros; unfold add; simpl.
    f_equal; omega.
  Qed.

  Fact add_comm :
    forall u v, add u v = add v u.
  Proof.
    intros; unfold add.
    f_equal; omega.
  Qed.

  Fact add_minus :
    forall u, add u (minus u) = zero.
  Proof.
    intros; unfold add, minus, zero; simpl.
    f_equal; omega.
  Qed.

  Fact unit_left :
    forall u, add zero u = u.
  Proof.
    intros; unfold add, zero; simpl.
    destruct u; simpl; f_equal; omega.
  Qed.

  Definition expr A := (A * A)%type.

  Definition eval A (ev : A -> Z) e :=
    (ev (fst e), ev (snd e)).

  Fact eval_ext :
    forall A (ev ev' : A -> Z),
      (forall a, ev a = ev' a) -> forall e, eval A ev e = eval A ev' e.
  Proof.
    intros. unfold eval. now repeat rewrite H.
  Qed.
End Z2.