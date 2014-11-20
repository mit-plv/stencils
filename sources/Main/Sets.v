(* ========================================================================== *
 * Sets                                                                       *
 * ========================================================================== *)

Require Import ZArith.
Local Open Scope Z_scope.

Definition set (A : Type) :=
  A -> Prop.

Delimit Scope set_scope with set.
Local Open Scope set_scope.

Definition is_in {U} (x : U) (A : set U) :=
  A x.
Infix "∈" := is_in (at level 70, no associativity) : set_scope.

Definition same {U} (A B : set U) :=
  forall x, x ∈ A <-> x ∈ B.
Infix "≡" := same (at level 70, no associativity) : set_scope.

Definition empty (U : Type) : set U :=
  fun _ => False.
Notation "∅" := (empty _) : set_scope.

Definition singleton {U : Type} (a : U) : set U :=
  fun x => x = a.
Notation "⎨ a ⎬" := (singleton a) : set_scope.

Definition segment (x y : Z) : set Z :=
  fun n => x <= n <= y.
Notation "〚 x , y 〛" :=
  (segment x y)
    (at level 0, format "'〚' x ','  '/' y '〛'") : set_scope.

Definition bin_union {U} (A B : set U) : set U:=
  fun x => A x \/ B x.
Infix "∪" := bin_union (at level 41, right associativity) : set_scope.

Definition seg_union {U} (a b : Z) (A : Z -> set U) : set U:=
  fun x => exists k, a <= k <= b /\ A k x.
Notation "⋃ ⎨ A , k ∈ 〚 a , b 〛 ⎬" :=
  (seg_union a b (fun k => A))
    (at level 0, k at next level, A at next level)
  : set_scope.

Definition times {U V} (A : set U) (B : set V) : set (U * V) :=
  fun p => (fst p ∈ A /\ snd p ∈ B)%set.
Infix "×" := times (at level 39, right associativity) : set_scope.

Lemma bin_union_assoc :
  forall U (A B C : set U),
    (A ∪ B) ∪ C ≡ A ∪ B ∪ C.
Proof. firstorder. Qed.
