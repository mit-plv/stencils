Require Import StLib.Main.
Require Import Psatz.
Require Import Program.

Parameters T N : Z.

Module ThreePointStencil <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, T〛×〚0, N〛.
  Definition dep c :=
    match c with
      | (t,x) =>
        [(t-1,x); (t-1,x-1); (t-1,x+1)]
    end.
End ThreePointStencil.

Module P := Prog Z2 ThreePointStencil.
Import P.

Definition trapezoid := (Z * Z * Z * Z * Z * Z)%type.

Definition Vol (T : trapezoid) :=
  match T with
    | (t0, t1, x0, v0, x1, v1) =>
      (t1 - t0) * ((x1 - x0) * 2 + (v1 - v0) * (t1 - t0))
  end.

Definition WF (T : trapezoid) :=
  match T with
    | (t0, t1, x0, v0, x1, v1) =>
      t0 < t1 /\
      x0 < x1 /\
      -1 <= v0 <= 1 /\
      -1 <= v1 <= 1 /\
      x0 + (t1 - t0) * v0 <= x1 + (t1 - t0) * v1
  end.

Ltac clear_divs :=
  repeat match goal with
           | [ |- context[?a / ?b] ] =>
             let H := fresh in
             assert (H : b > 0) by omega;
             generalize (Z_mod_lt a b H);
             generalize (Z_div_mod_eq a b H);
             let r := fresh "r" in
             generalize (Zmod a b) as r;
             let q := fresh "q" in
             generalize (Zdiv a b) as q;
             clear H
         end.

Lemma WF_Vol_ge0 :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) -> Vol (t0, t1, x0, v0, x1, v1) >= 0.
Proof. unfold WF, Vol; intros; nia. Qed.

Lemma WF_Vol_gt0 :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) -> Vol (t0, t1, x0, v0, x1, v1) > 0.
Proof. unfold WF, Vol; intros; nia. Qed.

Lemma Spatial_cut_WF_l_general :
  forall (t0 t1 x0 v0 x1 v1 xm v : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    -1 <= v <= 1 ->
    x0 < xm ->
    x0 + (t1 - t0) * v0 <= xm + (t1 - t0) * v ->
    WF (t0, t1, x0, v0, xm, v).
Proof. unfold WF; intuition. Qed.

Lemma Spatial_cut_WF_r_general :
  forall (t0 t1 x0 v0 x1 v1 xm v : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    -1 <= v <= 1 ->
    xm < x1 ->
    xm + (t1 - t0) * v <= x1 + (t1 - t0) * v1 ->
    WF (t0, t1, xm, v, x1, v1).
Proof. unfold WF; intuition. Qed.

Lemma Spatial_cut_WF_l :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    (t1 - t0) * 4 < (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) ->
    let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * (t1 - t0)) / 4 in
    WF (t0, t1, x0, v0, xm, -1).
Proof.
  unfold WF; intros.
  apply Spatial_cut_WF_l_general with x1 v1;
    first [assumption || clear_divs; intros; nia].
Qed.

Lemma Spatial_cut_WF_r :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    (t1 - t0) * 4 < (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) ->
    let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * (t1 - t0)) / 4 in
    WF (t0, t1, xm, -1, x1, v1).
Proof.
  unfold WF; intros.
  apply Spatial_cut_WF_r_general with x0 v0;
    first [assumption || clear_divs; intros; nia].
Qed.

Lemma Time_cut_WF_bot :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t1 - t0 <> 1 ->
    (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) <= (t1 - t0) * 4 ->
    let s := (t1 - t0) / 2 in
    WF (t0, t0 + s, x0, v0, x1, v1).
Proof. unfold WF; intuition; clear_divs; intros; nia. Qed.

Lemma Time_cut_WF_top :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) <= (t1 - t0) * 4 ->
    let s := (t1 - t0) / 2 in
    WF (t0 + s, t1, x0 + v0 * s, v0, x1 + v1 * s, v1).
Proof. unfold WF; intuition; clear_divs; intros; nia. Qed.

Lemma Spatial_cut_Vol_l :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t1 - t0 > 1 ->
    (t1 - t0) * 4 < (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) ->
    let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * (t1 - t0)) / 4 in
    Vol (t0, t1, x0, v0, xm, -1) < Vol (t0, t1, x0, v0, x1, v1).
Proof.
  unfold WF, Vol; intuition.
  clear_divs; intros; nia.
Qed.

Lemma Spatial_cut_Vol_r :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t1 - t0 > 1 ->
    (t1 - t0) * 4 < (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) ->
    let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * (t1 - t0)) / 4 in
    Vol (t0, t1, xm, -1, x1, v1) < Vol (t0, t1, x0, v0, x1, v1).
Proof.
  unfold WF, Vol; intuition.
  clear_divs; intros; nia.
Qed.

Lemma Vol_sub_trapezoid :
  forall (t0 t1 x0 v0 x1 v1 t : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t0 < t < t1 ->
    Vol (t0, t, x0, v0, x1, v1) +
    Vol (t, t1, x0 + v0 * (t - t0), v0, x1 + v1 * (t - t0), v1)
    = Vol (t0, t1, x0, v0, x1, v1).
Proof. unfold WF, Vol; intuition; ring. Qed.

Lemma silly_arith : forall x y t, x + t = y -> t > 0-> x < y.
Proof. intros; omega. Qed.

Lemma Time_cut_Vol_bot :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t1 - t0 > 1 ->
    (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) <= (t1 - t0) * 4 ->
    let s := (t1 - t0) / 2 in
    Vol (t0, t0 + s, x0, v0, x1, v1) < Vol (t0, t1, x0, v0, x1, v1).
Proof.
  unfold WF; intros.
  eapply silly_arith.
  apply Vol_sub_trapezoid.
  assumption.
  clear_divs; intros; nia.
  apply WF_Vol_gt0.
  replace (t0 + (t1 - t0) / 2 - t0) with ((t1 - t0) / 2) by ring.
  now apply Time_cut_WF_top.
Qed.

Lemma silly_arith2 : forall x y t, t + x = y -> t > 0-> x < y.
Proof. intros; omega. Qed.

Lemma Time_cut_Vol_top :
  forall (t0 t1 x0 v0 x1 v1 : Z),
    WF (t0, t1, x0, v0, x1, v1) ->
    t1 - t0 <> 1 ->
    (x1 - x0) * 2 + (v1 - v0) * (t1 - t0) <= (t1 - t0) * 4 ->
    let s := (t1 - t0) / 2 in
    Vol (t0 + s, t1, x0 + v0 * s, v0, x1 + v1 * s, v1)
    < Vol (t0, t1, x0, v0, x1, v1).
Proof.
  unfold WF; intros.
  eapply silly_arith2.
  instantiate (1 := Vol (t0, t0 + (t1 - t0) / 2, x0, v0, x1, v1)).
  remember ((t1 - t0) / 2) as s.
  replace (v0 * s) with (v0 * ((t0 + s) - t0)) by ring.
  replace (v1 * s) with (v1 * ((t0 + s) - t0)) by ring.
  apply Vol_sub_trapezoid.
  assumption.
  subst; clear_divs; intros; nia.
  apply WF_Vol_gt0.
  now apply Time_cut_WF_bot.
Qed.

Ltac clear_reflections :=
  repeat match goal with
           | [ H : (_ =? _) = true |- _ ] =>
             apply Z.eqb_eq in H
           | [ H : (_ =? _) = false |- _ ] =>
             apply Z.eqb_neq in H
           | [ H : (_ <? _) = true |- _ ] =>
             apply Z.ltb_lt in H
           | [ H : (_ <? _) = false |- _ ] =>
             apply Z.ltb_ge in H
         end.

Ltac prove_WF :=
  clear_reflections;
  first [now apply Spatial_cut_WF_l
        |now apply Spatial_cut_WF_r
        |now apply Time_cut_WF_bot
        |now apply Time_cut_WF_top].

Ltac prove_Vol :=
  unfold WF in * |-;
  match goal with
    | [ |- (Z.abs_nat _ < Z.abs_nat _)%nat ] =>
      clear_reflections;
        apply Zabs_nat_lt; split;
        [apply Z.ge_le, WF_Vol_ge0; prove_WF|];
        first [apply Spatial_cut_Vol_l
              |apply Spatial_cut_Vol_r
              |apply Time_cut_Vol_bot
              |apply Time_cut_Vol_top];
        (assumption || omega)
  end.

Arguments Zminus m n : simpl never.
Local Obligation Tactic := program_simpl; try (prove_WF || prove_Vol).

Program Fixpoint Walk1 (Tp : trapezoid | WF Tp) {measure (Z.abs_nat (Vol Tp))} :=
  match Tp with
    | (t0, t1, x0, v0, x1, v1) =>
      let h := t1 - t0 in
      if dec (h =? 1) then
        For "x" From x0 To (x1 - 1) Do
          Fire (t0 : aexpr, "x" : aexpr)
      else
        if dec (h * 4 <? (x1 - x0) * 2 + (v1 - v0) * h) then
          let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * h) / 4 in
          Walk1 (@exist _ _ (t0, t1, x0, v0, xm, -1) _);;
          Walk1 (@exist _ _ (t0, t1, xm, -1, x1, v1) _)
        else
          let s := h / 2 in
          Walk1 (@exist _ _ (t0, t0 + s, x0, v0, x1, v1) _);;
          Walk1 (@exist _ _ (t0 + s, t1, x0 + v0 * s, v0, x1 + v1 * s, v1) _)
  end%prog.

Example WF_ex :
  WF (0,5,0,0,5,0).
Proof. unfold WF; intuition omega. Qed.

Eval compute in psimpl (Walk1 (@exist _ _ (0, 5, 0, 0, 5, 0) WF_ex)).

(*Theorem Walk1_shape :
  forall t0 t1 x0 v0 x1 v1 v
         (H : WF (t0, t1, x0, v0, x1, v1)),
    shape v (Walk1 (@exist _ _ (t0, t1, x0, v0, x1, v1) H)) ≡
          (⋃⎨⎨(x0 + v0 * (t - t0), x0 + v1 * (t - t0))⎬, t ∈〚t0, t1〛⎬).
Proof.
  intros.
  compute.
  unfold Walk1, Fix_sub, Walk1_obligation_9.
  induction (Z.)*)