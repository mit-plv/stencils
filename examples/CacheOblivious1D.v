Require Import StLib.Main.
Require Import Psatz.

Parameters T N : Z.

Module ThreePointStencil <: (PROBLEM Z2).
  Local Open Scope aexpr.

  Definition space := 〚0, T〛×〚0, N〛.
  Definition target := 〚0, T〛×〚0, N〛.
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

Ltac prove_WF :=
  first [ apply Spatial_cut_WF_l
        | apply Spatial_cut_WF_r
        | apply Time_cut_WF_bot
        | apply Time_cut_WF_top]; (assumption || omega).

Ltac prove_Vol :=
  unfold WF in * |-;
  match goal with
    | [ |- (Z.abs_nat _ < Z.abs_nat _)%nat ] =>
      apply Zabs_nat_lt; split;
      [apply Z.ge_le, WF_Vol_ge0; prove_WF|];
      first [ apply Spatial_cut_Vol_l
            | apply Spatial_cut_Vol_r
            | apply Time_cut_Vol_bot
            | apply Time_cut_Vol_top];
      (assumption || omega)
  end.

Definition WF_trapezoid := { Tp : trapezoid | WF Tp }.

Definition Vol_order (Tp Tp' : WF_trapezoid) :=
  (Z.abs_nat (Vol (proj1_sig Tp)) < Z.abs_nat (Vol (proj1_sig Tp')))%nat.

Lemma Vol_order_wf' :
  forall k Tp, (Z.abs_nat (Vol (proj1_sig Tp)) <= k -> Acc Vol_order Tp)%nat.
Proof.
  unfold Vol_order; induction k; intros.
  - inversion H.
    constructor; intros. rewrite H1 in H0.
    inversion H0.
  - constructor; intros. apply IHk; omega.
Defined.

Lemma Vol_order_wf :
  well_founded Vol_order.
Proof. red; intro. eapply Vol_order_wf'; eauto. Defined.

Arguments Zminus m n : simpl never.
Arguments Zmult x y : simpl never.

Definition Walk1 : { Tp : trapezoid | WF Tp } -> prog.
  refine (Fix (R := Vol_order) _ (fun _ => prog) (fun Tp self => _)).
  apply Vol_order_wf.

  destruct Tp as [[[[[[t0 t1] x0] v0] x1] v1] H].
  refine
    (let h := t1 - t0 in
     if (Z_eq_dec h 1) then
       For "x" From x0 To (x1 - 1) Do
         Fire (t0 : aexpr, "x" : aexpr)
     else
       if (Z_lt_ge_dec (h * 4) ((x1 - x0) * 2 + (v1 - v0) * h)) then
         let xm := ((x0 + x1) * 2 + (v0 + v1 + 2) * h) / 4 in
         self (exist _ (t0, t1, x0, v0, xm, -1) _) _;;
         self (exist _ (t0, t1, xm, -1, x1, v1) _) _
       else
         let s := h / 2 in
         self (exist _ (t0, t0 + s, x0, v0, x1, v1) _) _;;
              self (exist _ (t0 + s, t1, x0 + v0 * s, v0, x1 + v1 * s, v1) _) _)%prog;
    simpl; unfold Vol_order, h in *; prove_Vol.
  Grab Existential Variables.
  unfold h in *; prove_WF.
  unfold h in *; prove_WF.
  unfold h in *; prove_WF.
  unfold h in *; prove_WF.
Defined.

Example WF_ex :
  WF (0,5,0,0,5,0).
Proof. unfold WF; intuition omega. Qed.

Eval compute in psimpl (Walk1 (@exist _ _ (0, 5, 0, 0, 5, 0) WF_ex)).

Definition trapezoid_shape (Tp : WF_trapezoid) :=
  match proj1_sig Tp with
    | (t0, t1, x0, v0, x1, v1) =>
      (⋃⎨⎨t⎬×〚x0 + v0 * (t - t0), x1 + v1 * (t - t0)-1〛, t ∈〚t0, t1-1〛⎬)
  end.

Theorem Walk1_shape :
  forall v Tp, shape v (Walk1 Tp) ≡ (trapezoid_shape Tp).
Proof.
  intro v.
  refine
    (well_founded_ind Vol_order_wf
                      (fun Tp => shape v (Walk1 Tp) ≡ trapezoid_shape Tp)
                      _); intros.
  destruct x as [[[[[[t0 t1] x0] v0] x1] v1] Hx].
  unfold Walk1; rewrite Fix_eq; fold Walk1.
  destruct (Z.eq_dec (t1 - t0) 1).

  - unfold trapezoid_shape; simpl.
    simplify sets with ceval.
    forward.
    + exists t0; forward. nia.
      destruct x; injection H2; intros.
      forward; subst; simpl; nia.
    + exists (snd x); forward. nia. destruct x. simpl in *. nia.
      destruct x; simpl in *. forward. nia.

  - destruct (Z_lt_ge_dec ((t1 - t0) * 4)
                          ((x1 - x0) * 2 + (v1 - v0) * (t1 - t0))).
    + simpl.
      repeat (rewrite H);
        [ | unfold Vol_order; prove_Vol | unfold Vol_order; prove_Vol].
      unfold trapezoid_shape; simpl.
      forward; destruct x; subst; simpl in *.

      * (exists z; forward). simpl.
        match goal with [ _ : z0 <= ?a |- _ ] => transitivity a end.
        assumption.
        clear_divs; intros; nia.

      * (exists z; forward). simpl.
        match goal with [ _ : ?a <= z0 |- _ ] => transitivity a end.
        clear_divs; intros; nia.
        assumption.

      * destruct (Z_le_gt_dec z0
                              (((x0 + x1) * 2 + (v0 + v1 + 2) * (t1 - t0)) / 4 +
                               (-1) * (z - t0) - 1)).
        lhs; forward; exists z; forward.
        rhs; forward; exists z; forward; simpl; omega.

    + simpl.
      repeat (rewrite H);
        [ | unfold Vol_order; prove_Vol | unfold Vol_order; prove_Vol].
      unfold trapezoid_shape; simpl.
      forward; destruct x; subst; simpl in *.

      * (exists z; forward). simpl.
        match goal with [ _ : z <= ?a |- _ ] => transitivity a end.
        assumption.
        clear_divs; intros; omega.

      * (exists z; forward).
        match goal with [ _ : ?a <= z |- _ ] => transitivity a end.
        clear_divs; intros; omega.
        assumption.

        simpl.
        match goal with [ _ : ?a <= z0 |- _ ] => transitivity a end.
        clear_divs; intros; nia.
        assumption.

        simpl.
        match goal with [ _ : z0 <= ?a |- _ ] => transitivity a end.
        assumption.
        clear_divs; intros; nia.

      * destruct (Z_le_gt_dec z (t0 + (t1 - t0) / 2 - 1)).
        lhs; forward; exists z; forward.
        rhs; forward. exists z; forward; simpl; nia.

  - intros.
    destruct x as [[[[[[t0' t1'] x0'] v0'] x1'] v1'] H'].
    destruct (Z.eq_dec (t1' - t0') 1); [reflexivity | ].
    destruct (Z_lt_ge_dec ((t1' - t0') * 4)
                          ((x1' - x0') * 2 + (v1' - v0') * (t1' - t0'))).
    repeat rewrite H0; reflexivity.
    repeat rewrite H0; reflexivity.

Qed.