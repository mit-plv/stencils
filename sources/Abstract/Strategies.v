(* ========================================================================= *)
(* Language describing partial, abstract stencil strategies                  *)
(* ========================================================================= *)

Require Import Common.Stencils Common.Sets Common.Monoids Abstract.Semantics.
Require Import List.
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

  Fixpoint shape (s : stg) : group :=
    match s with
      | Seq s1 s2 => shape s1 ∪ shape s2
      | Loop s a b => (⋃⎨shape (s i), i ∈〚a, b〛⎬)
      | Par s a b => (⋃⎨shape (s p), p ∈〚a, b〛⎬)
      | Hole g => g
    end.

  Fixpoint PO (s : stg) (A : group) : Prop :=
    match s with
      | Seq s1 s2 =>
        PO s1 A /\ PO s2 (A ∪ shape s1)
      | Loop s a b =>
        a <= b /\ PO (s a) A /\
        forall i, a <= i < b -> PO (s (1+i)) (A ∪ shape (Loop s a i))
      | Par s a b =>
        a <= b /\ forall p, a <= p <= b -> PO (s p) A
      | Hole g => valid _ A (A ∪ g)
    end.

  Lemma PO_sound :
    forall s A, PO s A -> valid _ A (A ∪ (shape s)).
  Proof.
    induction s; intros; simpl in *.
    + apply sequ with (A ∪ shape s1).
      * firstorder.
      * rewrite <- union_assoc; now apply IHs2.
    + apply loop; [firstorder|firstorder|].
      intros.
      rewrite <- union_segment; [|omega].
      rewrite <- union_assoc.
      firstorder.
    + apply par; firstorder.
    + assumption.
  Qed.

  (** Now we turn to refinement of abstract strategies. *)

  Inductive refines : stg -> stg -> Prop :=
  | refines_seq :
      forall s1 s2 s1' s2',
        refines s1 s1' -> refines s2 s2' -> refines (Seq s1 s2) (Seq s1' s2')
  | refines_loop :
      forall s1 s2 a b, (forall i, a <= i <= b -> refines (s1 i) (s2 i)) ->
                        refines (Loop s1 a b) (Loop s2 a b)
  | refines_par :
      forall s1 s2 a b, (forall p, a <= p <= b -> refines (s1 p) (s2 p)) ->
                        refines (Par s1 a b) (Par s2 a b)
  | refines_hole :
      forall s g, shape s = g -> refines s (Hole g).

  Inductive computational : stg -> Prop :=
  | comp_seq :
      forall s1 s2,
        computational s1 -> computational s2 -> computational (Seq s1 s2)
  | comp_loop :
      forall s a b,
        (forall i, a <= i <= b -> computational (s i)) ->
        computational (Loop s a b)
  | comp_par :
      forall s a b,
        (forall p, a <= p <= b -> computational (s p)) ->
        computational (Par s a b)
  | comp_hole :
      forall g, singleton g -> computational (Hole g).
End Strategy.

(** Again, fancy notations *)

Delimit Scope stg_scope with stg.

Notation "'Spawn' 'Node' p ∈〚 a , b 〛 'With' s" :=
  (Par (fun p => s) a b) (at level 0, s at next level) : stg_scope.
Notation "'Compute' A" :=
  (Hole A) (at level 70) : stg_scope.
Notation "'For' i ∈〚 a , b 〛 'Do' s" :=
  (Loop (fun i => s) a b) (at level 0, s at next level) : stg_scope.
Notation "s1 ;; s2" :=
  (Seq s1 s2) (at level 0) : stg_scope.

(** This is the basic automation we provide for now to prove the correctness of
 * strategies.*)

(** XXX: Documentation! *)

Tactic Notation "generate" "proof" "obligations" :=
  apply PO_sound; simpl; firstorder.

Tactic Notation "easy" "union" "image" :=
  match goal with
    | [ |- (@union _ (@image _ _
               (@finite _ (@cons _ ?A (@nil _))) _)) ?x ] =>
      union with A; firstorder;
      image with x
  end.

Ltac forward' tac :=
  repeat first
         [progress unfold is_in, union, extension, image, bin_union,
          segment, times, finite, fst, snd in * |- |
          progress unfold valid, closure, sp,
          next, boundary, subset in |- * |
          progress unfold add_proj in * |
          intro | progress simpl | progress subst |
          match goal with
            | [ H : exists _, _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : In _ _ |- _ ] => destruct H
            | [ H : depends _ _ _ |- _ ] => inversion H; clear H
            | [ x : @prod _ _ |- _ ] => destruct x
            | [ |- _ = _ ] => apply same_eq
          end |
          progress (sets red; sets simpl) |
          left; now (forward' tac) |
          right; now (forward' tac) |
          now firstorder |
          now tac].

Ltac forward := forward' fail.
