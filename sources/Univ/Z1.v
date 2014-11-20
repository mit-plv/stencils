Require Import Main.Stencils.

Require Export String ZArith.
Open Scope Z_scope.
Open Scope string_scope.

Module Z1 <: CELL.

  Definition t := Z.

  Definition eq_dec := Z.eq_dec.

  Definition add := fun x y => x + y.
  Definition minus := fun x => -x.
  Definition zero := 0.

  Definition add_assoc := Zplus_assoc.
  Definition add_comm := Zplus_comm.
  Definition add_minus := Z.add_opp_diag_r.
  Definition unit_left := Zplus_0_l.

  Definition expr A : Type := A.

  Definition eval A (ev : A -> Z) e :=
    ev e.

  Lemma eval_ext :
    forall A (ev ev' : A -> Z),
      (forall a, ev a = ev' a) -> forall e, eval A ev e = eval A ev' e.
  Proof.
    intros.
    now rewrite H.
  Qed.
End Z1.
