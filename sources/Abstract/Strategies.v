(* ========================================================================= *)
(* Language describing partial, abstract stencil strategies                  *)
(* ========================================================================= *)

Require Import Common.Stencils Common.Sets Common.Monoids Abstract.Semantics.
Local Open Scope set_scope.

Section Strategy.
  Generalizable Variables cell add zero.
  Context `{M : CommMonoid cell add zero}.
  Context `(St : @Stencil _ _ _ M).
  Local Open Scope monoid.

  Definition group := set (cell * time).

  (* XXX: Documentation! *)

  Inductive stg : Type :=
  | Seq : stg -> stg -> stg
  | Loop : (nat -> stg) -> nat -> nat -> stg
  | Par : (nat -> stg) -> nat -> nat -> stg
  | Hole : group -> stg.

  Fixpoint interp (s : stg) : group :=
    match s with
      | Seq s1 s2 => interp s1 ∪ interp s2
      | Loop s a b => (⋃⎨interp (s i), i ∈〚a, b〛⎬)
      | Par s a b => (⋃⎨interp (s i), i ∈〚a, b〛⎬)
      | Hole g => g
    end.

  Fixpoint PO (s : stg) (A : group) : Prop :=
    match s with
      | Seq s1 s2 =>
        PO s1 A /\ PO s2 (A ∪ interp s1)
      | Loop s a b =>
        a <= b /\ PO (s a) A /\
        forall i, a <= i < b -> PO (s (1+i)) (A ∪ interp (Loop s a i))
      | Par s a b =>
        a <= b /\ forall i, a <= i <= b -> PO (s i) A
      | Hole g => valid _ A g
    end.

  Lemma PO_sound :
    forall s A, PO s A -> valid _ A (A ∪ (interp s)).
  Proof.
    induction s; intros; simpl in *.
    + apply sequ with (A ∪ interp s1).
      * firstorder.
      * rewrite <- union_assoc; now apply IHs2.
    + apply loop; [firstorder|firstorder|].
      intros.
      rewrite <- union_segment; [|omega].
      rewrite <- union_assoc.
      firstorder.
    + apply par; firstorder.
    + now apply append.
  Qed.
End Strategy.

Delimit Scope stg_scope with stg.

Notation "'Spawn' 'Node' i ∈〚 a , b 〛 'With' s" :=
  (Par (fun i => s) a b) (at level 0, s at next level) : stg_scope.
Notation "'Compute' A" :=
  (Hole A) (at level 70) : stg_scope.
Notation "'For' i ∈〚 a , b 〛 'Do' s" :=
  (Loop (fun i => s) a b) (at level 0, s at next level) : stg_scope.
Notation "s1 ;; s2" :=
  (Seq s1 s2) (at level 0) : stg_scope.