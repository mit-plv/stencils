(* From StLib. *)
Require Export Programs.

Module Kern  (D : DOMAIN) (Pb : PROBLEM D).

  Module P := Prog D Pb.
  Export P.

  (** [code] denotes the type of elementary (computation or communication)
   * steps in a distributed kernel. *)
  Inductive code : Type :=
  | kNop : code
  | kFire : cexpr -> code
  | kIf : bexpr -> code -> code -> code
  | kSeq : code -> code -> code
  | kFor : string -> aexpr -> aexpr -> code -> code.

  (** Notations for elementary steps. *)

  Delimit Scope code_scope with code.

  Notation "'Nop'" :=
    kNop : code_scope.
  Notation "'Fire' c" :=
    (kFire c%aexpr) (at level 80) : code_scope.
  Notation "'If' b 'Then' p1 'Else' p2" :=
    (kIf b%bexpr p1 p2) (at level 80, right associativity) : code_scope.
  Notation "p1 ;; p2" :=
    (kSeq p1 p2) (at level 80, right associativity) : code_scope.
  Notation "'For' i 'From' a 'To' b 'Do' p" :=
    (kFor i a%aexpr b%aexpr p)
      (at level 80, right associativity) : code_scope.

  (** [denote] compiles programs of type [code] into programs of type
   * [prog].  This translation is trivial, except for the compilation of the
   * [Fire] command.  [denote] is parameterized with this compilation step.
   *
   * This allows to give two different denotational semantics to programs of
   * type [code]: One for communication steps, where we check that
   * dependencies are satisfied.  And one for computation steps, where we don't.
   * In particular, we will have to check that the pieces of information we
   * send are part of the current knowledge of the thread, but this is captured
   * later on, when we give the semantics of distributed programs. *)
  Fixpoint denote (p : code) F : prog :=
    match p with
      | Nop%code =>
        Nop%prog
      | (Fire c)%code =>
        F c
      | (If b Then p1 Else p2)%code =>
        (If b Then (denote p1 F) Else (denote p2 F))%prog
      | (p1;; p2)%code =>
        (denote p1 F;; denote p2 F)%prog
      | (For i From a To b Do q)%code =>
        (For i From a To b Do denote q F)%prog
    end.

  Module Comp.
    (** Computation steps.  Here, [Fire c] is compiled as an assertion stating
     * that all the dependencies of [c] are satisfied, followed by a [Flag c]
     * command. *)
    Definition F c := P.Fire c.
    Definition denote (p : code) : prog :=
      denote p F.
  End Comp.

  Module Comm.
    (** Communication steps.  This time, [Fire c] is equivalent to [Flag c]. *)
    Definition F c := Flag c.
    Definition denote (p : code) : prog :=
      denote p F.
  End Comm.

  Definition thread := Z.
  Definition time := nat.

  (** [kern] is the type of distributed programs.  A distributed program
   * is defined by two programs, representing respectively computation steps
   * and communication steps.
   *
   * During computation steps, the program can access two distinguished
   * variables, ["id"] and ["T"].  The former contains the thread's ID while
   * the latter represents the current time step.
   *
   * Similarly, during communication steps, the program can access ["id"] and
   * ["T"], but also ["to"], which contains the ID of the thread to which
   * information will be sent.  E.g., if [T=2], [id=1] and [to=3], this is
   * time step [2], the program is being executed by thread [1] and sending
   * data to thread [3].
   *)
  Record kern :=
    makeKernel
      {
        comp : code;
        comm : code
      }.

  Record trace :=
    makeTrace
      {
        beforeComp : nat -> thread -> array;
        sends      : nat -> thread -> thread -> array;
        afterComp  : nat -> thread -> array
      }.

  Definition kexec (k : kern) (tr : trace)
             (idMax : thread) (TMax : time) : Prop :=
    (* Initially, nothing is computed. *)
    (forall id, 0 <= id <= idMax -> beforeComp tr 0 id ≡ ∅)
    /\

    (* We go from [beforeComp tr T id] to [afterComp tr T id] through a
     * computation step. *)
    (forall id T,
       0 <= id <= idMax -> (T <= TMax)%nat ->
       exec [("id", id); ("T", Z.of_nat T)]
            (beforeComp tr T id)
            (Comp.denote (comp k))
            (afterComp tr T id))
    /\

    (* [sends tr T id to] represents what is sent by thread [id] to thread
     * [to] at step [T]. *)
    (forall id to T,
       0 <= id <= idMax -> 0 <= to <= idMax -> (T <= TMax)%nat ->
       exec [("id", id); ("to", to); ("T", Z.of_nat T)]
            ∅
            (Comm.denote (comm k))
            (sends tr T id to))
    /\

    (* A thread cannot send a value it does not know. *)
    (forall id to T,
       0 <= id <= idMax -> 0 <= to <= idMax -> (T <= TMax)%nat ->
       sends tr T id to ⊆ afterComp tr T id)
    /\

    (* Conservation of knowledge: What a thread knows at time [T+1] comes
     * from what it knew after computation step at time [T] and what other
     * threads sent to it. *)
    (forall id T,
       0 <= id <= idMax -> (T <= TMax)%nat ->
       beforeComp tr (1+T) id ⊆
                  afterComp tr T id
                  ∪ ⋃⎨sends tr T from id, from ∈〚0, idMax〛⎬).

  Definition kcorrect (k : kern) (idMax : thread) (TMax : time) :=
    exists tr, kexec k tr idMax TMax.

End Kern.
