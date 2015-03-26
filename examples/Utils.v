Require Import ZArith.
Local Open Scope Z_scope.

Ltac to_ctx H := generalize H; intro.

(** The following two arithmetic lemma will be used in the proof of
 * correctness. *)
Lemma Z_div_mod_spec :
  forall a b,
    b > 0 ->
    0 <= a - b * (a / b) < b.
Proof.
  intros.
  to_ctx (Z_div_mod_eq a b H);
  to_ctx (Z_mod_lt a b H);
  omega.
Qed.

Lemma seg_dec :
  forall a b n, a <= n <= b \/ n < a \/ n > b.
Proof.
  intros.
  destruct Z_le_gt_dec with a n;
    destruct Z_le_gt_dec with n b;
  firstorder.
Qed.

Ltac destr_case b :=
  let bb := fresh in
  let Hbb := fresh in
  remember b as bb eqn:Hbb;
  symmetry in Hbb; destruct bb;
  (apply Z.eqb_eq in Hbb || apply Z.eqb_neq in Hbb);
  try (exfalso; omega).

Ltac destr_case_lt b :=
  let bb := fresh in
  let Hbb := fresh in
  remember b as bb eqn:Hbb;
  symmetry in Hbb; destruct bb;
  (apply Z.ltb_lt in Hbb || apply Z.ltb_ge in Hbb);
  try (exfalso; omega).

