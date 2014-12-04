Require Import Main.Stencils Main.Sets.
Require Import String ZArith List.
Local Open Scope Z_scope.

(* ========================================================================== *)
Module Defs (Cell : CELL) (Stencil : STENCIL Cell).

  Module CellNotations := CellNotations Cell.
  Import CellNotations.

  (* ======================================================================== *)
  Module State.

    (** Variables are indexed by [string].  A [State.t] assigns an integer value
     * to each variable and a boolean to each cell. *)
    Definition t := ((string -> Z) * (Cell.t -> bool))%type.

    (** [State.initial] is an "empty" state.  It assigns [0] to every variable
     * and [false] to every cell. *)
    Definition initial : t :=
      (fun _ => 0, fun _ => false).

    (** [State.get_var s x] returns the value of variable [x] in state [s].
     * [State.set_var s x n] returns the state [s], updated so that the new
     * value of [x] is [n]. *)
    Definition get_var (s : t) : string -> Z := fst s.
    Definition set_var (s : t) (v : string) (n : Z) : t :=
      (fun v' => if string_dec v' v then n else fst s v', snd s).

    (** [State.get_cell s c] returns the boolean associated with cell [c] in
     * state [s].  [State.set_cell s c] gives the state [s], updated so that
     * the boolean associated with cell [c] is [true]. *)
    Definition get_cell (s : t) (c : Cell.t) : bool := snd s c.
    Definition set_cell (s : t) (c : Cell.t) : t :=
      (fst s, fun c' => if Cell.eq_dec c' c then true else snd s c').

    (** Two states are declared equivalent ([State.equiv s1 s2]) whenever
     * they assign the same value to any given variable and the same boolean to
     * any given cell. *)
    Definition equiv (s1 s2 : t) : Prop :=
      (forall v, fst s1 v = fst s2 v) /\ (forall c, snd s1 c = snd s2 c).

    (** The next two definitions are used internally to have nicer notations. *)
    Definition pack x v : string * Z := (x,v).
    Definition update p s := State.set_var s (fst p) (snd p).

    (** Merging two [State.t]s.  Variable assignments are the ones of the
     * second state. *)
    Definition union (s1 s2 : State.t) : State.t :=
      (fst s2, fun c => snd s1 c || snd s2 c)%bool.

  End State.

  Module StateNotations.

    (** Equivalence between states. *)
    Infix "≈" := State.equiv (at level 70, no associativity) : state_scope.

    (** Updating a state by setting one or several variables. *)
    Notation "x ← v" := (State.pack x v) (at level 10) : state_scope.
    Notation "s ⟨ x ; .. ; y ⟩" :=
      (State.update x .. (State.update y s) ..) (at level 0) : state_scope.

    Open Scope state_scope.

  End StateNotations.

  Export StateNotations.

  (* ======================================================================== *)
  Module Arith.

    (** Arithmetic expressions, involving integer constants, variables, sums,
     * products, differences, divisions and remainders. *)
    Inductive t : Set :=
    | Cst : Z -> t
    | Var : string -> t
    | Add : t -> t -> t
    | Sub : t -> t -> t
    | Mul : t -> t -> t
    | Div : t -> t -> t
    | Mod : t -> t -> t.

    (** [Arith.eval s e] returns the value of arithmetic expression [e] in
     * state [s]. *)
    Fixpoint eval (s : State.t) (e : t) : Z :=
      match e with
        | Cst c => c
        | Var v => State.get_var s v
        | Add e1 e2 => eval s e1 + eval s e2
        | Sub e1 e2 => eval s e1 - eval s e2
        | Mul e1 e2 => eval s e1 * eval s e2
        | Div e1 e2 => eval s e1 / eval s e2
        | Mod e1 e2 => (eval s e1) mod (eval s e2)
      end.

  End Arith.

  Module ArithNotations.

    (** Notations and coercions for arithmetic expressions. *)

    Delimit Scope arith_t_scope with arith_t.

    Coercion Arith.Cst : Z >-> Arith.t.
    Coercion Arith.Var : string >-> Arith.t.

    Notation "e1 + e2" :=
      (Arith.Add e1%arith_t e2%arith_t) : arith_t_scope.
    Notation "e1 - e2" :=
      (Arith.Sub e1%arith_t e2%arith_t) : arith_t_scope.
    Notation "e1 * e2" :=
      (Arith.Mul e1%arith_t e2%arith_t) : arith_t_scope.
    Notation "e1 / e2" :=
      (Arith.Div e1%arith_t e2%arith_t) : arith_t_scope.
    Notation "e1 'mod' e2" :=
      (Arith.Mod e1%arith_t e2%arith_t) : arith_t_scope.

  End ArithNotations.

  Export ArithNotations.

  (* ======================================================================== *)
  Module Bool.

    (** Boolean expressions, involving boolean constants, comparison of two
     * arithmetic expressions, boolean AND, OR and NOT. *)
    Inductive t : Set :=
    | Cst : bool -> t
    | Eq : Arith.t -> Arith.t -> t
    | Lt : Arith.t -> Arith.t -> t
    | Le : Arith.t -> Arith.t -> t
    | Gt : Arith.t -> Arith.t -> t
    | Ge : Arith.t -> Arith.t -> t
    | Neg : t -> t
    | And : t -> t -> t
    | Or : t -> t -> t.

    (** [Bool.eval s e] returns the value of boolean expression [e] in state
     * [s]. *)
    Fixpoint eval (s : State.t) (e : t) : bool :=
      match e with
        | Cst b => b
        | Eq e1 e2 => Z.eqb (Arith.eval s e1) (Arith.eval s e2)
        | Lt e1 e2 => Z.ltb (Arith.eval s e1) (Arith.eval s e2)
        | Le e1 e2 => Z.leb (Arith.eval s e1) (Arith.eval s e2)
        | Gt e1 e2 => Z.gtb (Arith.eval s e1) (Arith.eval s e2)
        | Ge e1 e2 => Z.geb (Arith.eval s e1) (Arith.eval s e2)
        | Neg e' => negb (eval s e')
        | And e1 e2 => andb (eval s e1) (eval s e2)
        | Or e1 e2 => orb (eval s e1) (eval s e2)
      end.

  End Bool.

  Module BoolNotations.

    (** Notations and coercions for boolean expressions. *)
    (* XXX: Fix precedence levels. *)

    Delimit Scope bool_t_scope with bool_t.

    Coercion Bool.Cst : bool >-> Bool.t.

    Notation "e1 =? e2" :=
      (Bool.Eq e1%arith_t e2%arith_t) : bool_t_scope.
    Notation "e1 <? e2" :=
      (Bool.Lt e1%arith_t e2%arith_t) : bool_t_scope.
    Notation "e1 <=? e2" :=
      (Bool.Le e1%arith_t e2%arith_t) : bool_t_scope.
    Notation "e1 >? e2" :=
      (Bool.Gt e1%arith_t e2%arith_t) : bool_t_scope.
    Notation "e1 >=? e2" :=
      (Bool.Ge e1%arith_t e2%arith_t) : bool_t_scope.
    Notation "! b" :=
      (Bool.Neg b%bool_t) (at level 35) : bool_t_scope.
    Notation "b1 && b2" :=
      (Bool.And b1%bool_t b2%bool_t) : bool_t_scope.
    Notation "b1 || b2" :=
      (Bool.Or b1%bool_t b2%bool_t) : bool_t_scope.

  End BoolNotations.

  Export BoolNotations.

  (** Just two handy shortcuts for cell expressions and their evaluator. *)
  Definition CExpr := Cell.expr (Arith.t).
  Definition CEval (s : State.t) (c : CExpr) :=
    Cell.eval Arith.t (Arith.eval s) c.

  (* ======================================================================== *)
  Module Imp.

    (** [Imp.t] denotes the type of simple imperative programs with cell
     * assignments, conditionals, sequential combinator, for loops and
     * assertions. *)
    Inductive t : Type :=
    | NoOp : t
    | Flag : CExpr -> t
    | Cond : Bool.t -> t -> t -> t
    | Seq : t -> t -> t
    | Assert : (State.t -> Prop) -> t
    | Loop : string -> Arith.t -> Arith.t -> t -> t.

    (** We now turn to the operational semantics of this language.
     * [Imp.exec s p t] holds if and only if program [p], executed from state
     * [s], terminates in state [t].
     *
     * The language has been designed so that programs are effect-free: The
     * only way to change the value of a variable is through a for loop, which
     * limits the scope of the assignment.
     *
     * Notice also that these programs are not Turing-complete.  We shall
     * actually prove that all these programs terminate or fail because of some
     * unsatisfied assertion. *)
    Inductive exec : State.t -> t -> State.t -> Prop :=
    | exec_NoOp :
        forall s, exec s NoOp s
    | exec_Flag :
        forall s c,
          exec s (Flag c) (State.set_cell s (CEval s c))
    | exec_Cond :
        forall s t b p1 p2,
          exec s (if Bool.eval s b then p1 else p2) t -> exec s (Cond b p1 p2) t
    | exec_Seq :
        forall s t u p1 p2,
          exec s p1 t -> exec t p2 u -> exec s (Seq p1 p2) u
    | exec_Assert :
        forall s (P : State.t -> Prop),
          P s -> exec s (Assert P) s
    | exec_Loop_f :
        forall s x a b p,
          Arith.eval s b < Arith.eval s a -> exec s (Loop x a b p) s
    | exec_Loop_t :
        forall s t u x a b p,
          Arith.eval s a <= Arith.eval s b ->
          exec (s⟨x ← (Arith.eval s a)⟩) p t ->
          exec t (Loop x (Arith.Add (Arith.Cst 1) a) b p) u ->
          exec s (Loop x a b p) u⟨x ← (State.get_var s x)⟩.

  End Imp.

  Module ImpNotations.

    (** Notations for imperative programs. *)

    Delimit Scope prog_t_scope with prog_t.

    Notation "'Nop'" :=
      Imp.NoOp : prog_t_scope.
    Notation "'Flag' c" :=
      (Imp.Flag c) (at level 80) : prog_t_scope.
    Notation "'If' b 'Then' p1 'Else' p2" :=
      (Imp.Cond b%bool_t p1 p2) (at level 80, right associativity) : prog_t_scope.
    Notation "p1 ;; p2" :=
      (Imp.Seq p1 p2) (at level 80, right associativity) : prog_t_scope.
    Notation "'Assert' P" :=
      (Imp.Assert P) (at level 80) : prog_t_scope.
    Notation "'For' i 'From' a 'To' b 'Do' p" :=
      (Imp.Loop i a%arith_t b%arith_t p)
        (at level 80, right associativity) : prog_t_scope.

    Notation "p // s ⇓ t" :=
      (Imp.exec s p t) (at level 40, t at next level) : state_scope.

  End ImpNotations.

  Export ImpNotations.

  (* ======================================================================== *)
  Module KStep.

    (** [KStep.t] denotes the type of elementary (computation or communication)
     * steps in a distributed kernel. *)
    Inductive t : Type :=
    | NoOp : t
    | Fire : CExpr -> t
    | Cond : Bool.t -> t -> t -> t
    | Seq : t -> t -> t
    | Loop : string -> Arith.t -> Arith.t -> t -> t.

  End KStep.

  Module KStepNotations.

    (** Notations for elementary steps. *)

    Delimit Scope step_t_scope with step_t.

    Notation "'Nop'" :=
      KStep.NoOp : step_t_scope.
    Notation "'Fire' c" :=
      (KStep.Fire c%arith_t) (at level 80) : step_t_scope.
    Notation "'If' b 'Then' p1 'Else' p2" :=
      (KStep.Cond b%bool_t p1 p2) (at level 80, right associativity) : step_t_scope.
    Notation "p1 ;; p2" :=
      (KStep.Seq p1 p2) (at level 80, right associativity) : step_t_scope.
    Notation "'For' i 'From' a 'To' b 'Do' p" :=
      (KStep.Loop i a%arith_t b%arith_t p)
        (at level 80, right associativity) : step_t_scope.

  End KStepNotations.

  Export KStepNotations.

  (** [denote] compiles programs of type [KStep.t] into programs of type
   * [Imp.t].  This translation is trivial, except for the compilation of the
   * [Fire] command.  [denote] is parameterized with this compilation step.
   *
   * This allows to give two different denotational semantics to programs of
   * type [KStep.t]: One for communication steps, where we check that
   * dependencies are satisfied.  And one for computation steps, where we don't.
   * In particular, we will have to check that the pieces of information we
   * send are part of the current knowledge of the thread, but this is captured
   * later on, when we give the semantics of distributed programs. *)
  Fixpoint denote (p : KStep.t) F : Imp.t :=
    match p with
      | Nop%step_t =>
        Nop%prog_t
      | (Fire c)%step_t =>
        (Assert (F c);; Flag c)%prog_t
      | (If b Then p1 Else p2)%step_t =>
        (If b Then (denote p1 F) Else (denote p2 F))%prog_t
      | (p1;; p2)%step_t =>
        (denote p1 F;; denote p2 F)%prog_t
      | (For i From a To b Do q)%step_t =>
        (For i From a To b Do denote q F)%prog_t
    end.

  Module Comp.

    (** Computation steps.  Here, [Fire c] is compiled as an assertion stating
     * that all the dependencies of [c] are satisfied.  This is followed by a
     * [Flag c] command in [denote]. *)
    Local Open Scope set_scope.
    Definition F (c : CExpr) : State.t -> Prop :=
      fun s =>
        let cv := CEval s c in
        forall k,
          In k Stencil.pattern ->
          (cv + k - Stencil.center)%grp ∈ Stencil.space ->
          State.get_cell s (cv + k - Stencil.center)%grp = true.

    (** [Comp.denote p] gives the denotational semantics of program [p] as a
     * computation step. *)
    Definition denote := fun p => denote p F.

  End Comp.

  Module Comm.

    (** Communication steps.  This time, [Fire c] is equivalent to
     * [Flag c]. *)
    Definition F (c : CExpr) : State.t -> Prop :=
      fun s => True.

    (** [Comm.denote p] gives the denotational semantics of program [p] as a
     * communication step. *)
    Definition denote := fun p => denote p F.

  End Comm.

  (** [Thread.t] and [Time.t] represent respectively thread IDs and time
   * steps. *)
  Module Thread.
    Definition t := nat.
    Definition to_Z (id : t) : Z :=
      Z.of_nat id.
  End Thread.
  Coercion Thread.to_Z : Thread.t >-> Z.

  Module Time.
    Definition t := nat.
    Definition to_Z (T : t) : Z :=
      Z.of_nat T.
    Definition incr (T : t) : t :=
      (1+T)%nat.
  End Time.
  Coercion Time.to_Z : Time.t >-> Z.

  (** Global states of a distributed program are represented by type
   * [GState.t], which contains a [State.t] for every thread. *)
  Module GState.
    Definition t := Thread.t -> State.t.
  End GState.

  (* ======================================================================== *)
  Module Kernel.

    (** [Kernel.t] is the type of distributed programs.  A distributed program
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
    Record t :=
      make
        {
          comp : KStep.t;
          comm : KStep.t
        }.

    (** Operational semantics for computation steps.  We compile the computation
     * program using [Comp.denote].  We run in for every thread [id] from state
     * [s id], after correctly setting the variables ["id"] and ["T"] and end up
     * in state [t id]. *)
    Definition comp_step (p : t) (T : Time.t) (idMax : Thread.t)
               (s t : GState.t) : Prop :=
      forall id : Thread.t,
        id <= idMax ->
        (Comp.denote (comp p)) // ((s id)⟨"id" ← id; "T" ← T⟩) ⇓ (t id).

    (** Operational semantics for communication steps. *)
    (* XXX: Documentation. *)
    Definition repr_comm (p : t) (T : Time.t) (idMax : Thread.t)
               (u : Thread.t -> Thread.t -> State.t): Prop :=
      forall src to : Thread.t,
        src <= idMax ->
        to <= idMax ->
        (Comm.denote (comm p))
          // (State.initial⟨"id" ← src; "T" ← T; "to" ← to⟩) ⇓ (u src to).

    Definition merge_step (p : t) (T : Time.t) (idMax : Thread.t)
               (s t : GState.t)
               (u : Thread.t -> Thread.t -> State.t) : Prop :=
      forall (id : Thread.t) (c : Cell.t),
        id <= idMax ->
        State.get_cell (t id) c = true ->
        State.get_cell (s id) c = true \/
        exists src : Thread.t,
          src <= idMax /\ State.get_cell (u src id) c = true.

    Definition sends_known_vals (p : t) (T : Time.t) (idMax : Thread.t)
               (t : GState.t)
               (u : Thread.t -> Thread.t -> State.t) : Prop :=
      forall (id id' : Thread.t) (c : Cell.t),
        id <= idMax ->
        State.get_cell (u id id') c = true -> State.get_cell (t id) c = true.

    (** [step p Tmax s t u] holds if and only if for all time steps [T]
     * satisfying [0 <= T <= Tmax]:
     *
     *  - Executing computation step [T] from state [s T] yields state [t T].
     *  - [u T id id' c] holds if and only if thread [id] sends the content of
     *    cell [c] at thread [id'], at time [T].
     *  - Executing communication step [T] from state [t T] yields state
     *    [s (1+T)].
     *  - [u T id id' c] hold only when [t id c] does. That is, no thread sends
     *    information it does not know. *)
    Definition step (p : t) (Tmax : Time.t) (idMax : Thread.t)
               (s t : Time.t -> GState.t)
               (u : Time.t -> Thread.t -> Thread.t -> State.t) :=
      forall T : Time.t,
        0 <= T <= Tmax ->
           comp_step p T idMax (s T) (t T)
        /\ repr_comm p T idMax (u T)
        /\ merge_step p T idMax (t T) (s (Time.incr T)) (u T)
        /\ sends_known_vals p T idMax (t T) (u T).

    (* XXX: Documentation. *)
    Definition trace_correct (p : t) (Tmax : Time.t) (idMax : Thread.t)
               s t u :=
        step p Tmax idMax s t u
        /\ (forall id : Thread.t,
              id <= idMax -> s 0%nat id = State.initial)
        /\ forall c,
             Stencil.space c ->
             exists id : Thread.t,
               id <= idMax /\ State.get_cell (s (Time.incr Tmax) id) c = true.

    Definition correct (p : t) (Tmax : Time.t) (idMax : Thread.t) :=
      exists s t u, trace_correct p Tmax idMax s t u.

  End Kernel.

End Defs.