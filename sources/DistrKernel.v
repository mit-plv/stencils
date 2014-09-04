Require Import AbstractStencil HoareLogic.

Module Kernel (Import S : Stencil) (Import L : Lg).
  Module Program := mkProgram S L.

  (* XXX: Perhaps this should be a parameter *)
  Definition node := nat.

  (** This is our notion of distributed programs *)

  Record t := mkAlgo
  {
    nbRuns : nat;
    comp : nat -> node -> Program.t;
    send : nat -> node -> node -> Program.t
  }.

  Definition state := node -> Program.array.
  Definition empty : Program.array := fun _ => False.

  (** Operational semantics of these distributed kernels *)

  Inductive step (T : nat) (p : t) (s1 s2 : state) : Prop :=
    | MakeStep :
        forall (computed : state) (sent : node -> state),
          (forall n c,
           exists s, Program.exec (Program.safe (comp p T n))
                                  (c,s1 n) s /\ forall t, (s1 n t \/ computed n t)
                                                          <-> snd s t) ->
(*           exists c', Program.exec (Program.safe (comp p T n))
                                   (c,s1 n) (c',computed n)) ->*)
          (forall n n' c,
           exists s, Program.exec (Program.unsafe (send p T n n'))
                                  (c,empty) s /\ forall t, sent n n' t <-> snd s t) ->
          (forall n c, (s1 n c \/ computed n c \/ exists n', sent n' n c)
                       <-> s2 n c) ->
          (forall n n' c, sent n n' c -> s1 n c \/ computed n c) ->
          step T p s1 s2.

  (** Correctness of a program with respect to a stencil *)

  Definition correct (p : t) :=
    exists s : nat -> state, 
      (forall T, T < nbRuns p -> step T p (s T) (s (1+T))) /\
      (forall c, final c -> exists n, s (nbRuns p) n c).
End Kernel.