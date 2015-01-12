(* From StLib. *)
Require Export Programs.

Module Kern (D : DOMAIN) (Pb : PROBLEM D).

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
  Definition time := Z.

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

  (** We now turn to semantics and correctness of distributed programs. *)
  Record trace :=
    makeTrace
      {
        beforeComp : time -> thread -> array;
        afterComp  : time -> thread -> array;
        sends      : time -> thread -> thread -> array
      }.

  Definition kexec (k : kern) (tr : trace)
             (idMax : thread) (TMax : time) : Prop :=
    (* Initially, nothing is computed. *)
    (forall id, 0 <= id <= idMax -> beforeComp tr 0 id ≡ ∅)
    /\

    (* We go from [beforeComp tr T id] to [afterComp tr T id] through a
     * computation step. *)
    (forall id T,
       0 <= id <= idMax -> 0 <= T <= TMax ->
       exec [("id", id); ("T", T)]
            (beforeComp tr T id)
            (Comp.denote (comp k))
            (afterComp tr T id))
    /\

    (* [sends tr T id to] represents what is sent by thread [id] to thread
     * [to] at step [T]. *)
    (forall id to T,
       0 <= id <= idMax -> 0 <= to <= idMax -> 0 <= T <= TMax ->
       exec [("id", id); ("to", to); ("T", T)]
            ∅
            (Comm.denote (comm k))
            (sends tr T id to))
    /\

    (* A thread cannot send a value it does not know. *)
    (forall id to T,
       0 <= id <= idMax -> 0 <= to <= idMax -> 0 <= T <= TMax ->
       sends tr T id to ⊆ afterComp tr T id)
    /\

    (* Conservation of knowledge: What a thread knows at time [T+1] comes
     * from what it knew after computation step at time [T] and what other
     * threads sent to it. *)
    (forall id T,
       0 <= id <= idMax -> 0 <= T <= TMax ->
       beforeComp tr (T+1) id ⊆
                  afterComp tr T id
                  ∪ ⋃⎨sends tr T from id, from ∈〚0, idMax〛⎬)
    /\

    (* Completeness *)
    (target ⊆ ⋃⎨beforeComp tr (TMax+1) id, id ∈〚0, idMax〛⎬).

  Definition kcorrect (k : kern) (idMax : thread) (TMax : time) :=
    exists tr, kexec k tr idMax TMax.

  (** Trace synthesizer *)

  Definition sends_synth (k : kern) (idMax : thread) :=
    fun T id to =>
      shape [("id", id); ("to", to); ("T", T)]
            (Comm.denote (comm k)).

  Definition computes_synth (k : kern) (idMax : thread) :=
    fun T id =>
      shape [("id", id); ("T", T)]
            (Comp.denote (comp k)).

  Definition bf_synth (k : kern) (idMax : thread) :=
    fun T id =>
      (⋃⎨computes_synth k idMax T' id, T' ∈〚0, T-1〛⎬)
        ∪ (⋃⎨⋃⎨sends_synth k idMax T' from id, from ∈〚0, idMax〛⎬,
             T' ∈〚0, T-1〛⎬).

  Definition af_synth (k : kern) (idMax : thread) :=
    fun T id =>
      (⋃⎨computes_synth k idMax T' id, T' ∈〚0, T〛⎬)
        ∪ (⋃⎨⋃⎨sends_synth k idMax T' from id, from ∈〚0, idMax〛⎬,
             T' ∈〚0, T-1〛⎬).

  Definition trace_synth (k : kern) (idMax : thread) :=
    makeTrace (bf_synth k idMax)
              (af_synth k idMax)
              (sends_synth k idMax).

  (** Main correctness result. *)
  Theorem trace_synth_correct :
    forall k idMax TMax,
      (forall T id,
         0 <= id <= idMax -> 0 <= T <= TMax ->
         vc [("id", id); ("T", T)]
            (⋃⎨computes_synth k idMax T' id, T' ∈〚0, T - 1〛⎬
             ∪ ⋃⎨⋃⎨sends_synth k idMax T' from id, from ∈〚0, idMax〛⎬,
                 T' ∈〚0, T - 1〛⎬)
            (Comp.denote (comp k))) ->
      (forall T id to,
         0 <= id <= idMax -> 0 <= to <= idMax ->
         0 <= T <= TMax ->
         vc [("id", id); ("to", to); ("T", T)] ∅ (Comm.denote (comm k))) ->
      (forall T id to,
         0 <= id <= idMax -> 0 <= to <= idMax ->
         0 <= T <= TMax ->
         sends_synth k idMax T id to ⊆ af_synth k idMax T id) ->
      target ⊆ ⋃⎨bf_synth k idMax (TMax + 1) id, id ∈〚0, idMax〛⎬ ->
      kexec k (trace_synth k idMax) idMax TMax.
  Proof.
    unfold kexec, trace_synth, beforeComp, afterComp; intuition.

    + unfold bf_synth.
      forward; omega.

    + unfold bf_synth, af_synth.
      eapply exec_equiv_r.
      apply vc_sexec_correct. apply H; omega.
      unfold computes_synth.
      setoid_rewrite param_union_bin at 4; [|assumption].
      apply bin_union_snd_third.

    + simpl; unfold sends_synth.
      eapply exec_equiv_r.
      apply vc_sexec_correct. apply H0; omega.
      apply bin_union_empty_l.

    + simpl.
      apply H1; omega.

    + simpl. unfold bf_synth, af_synth.
      replace (T + 1 - 1) with T by ring.
      setoid_rewrite param_union_bin at 2; [|assumption].
      apply equiv_incl.
      setoid_rewrite bin_union_assoc; reflexivity.
  Qed.

  (** Handy tactic applying the main correctness result. *)
  Tactic Notation "synthesize" "trace" :=
    eexists; eapply trace_synth_correct; simpl.

End Kern.
