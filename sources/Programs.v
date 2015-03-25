(* From the standard library. *)
Require Export ZArith String List.
Export ListNotations.
Open Scope Z_scope.
Open Scope string.

(* From StLib. *)
Require Export Expressions Sets SetsFacts Problems Automation.
Open Scope set_scope.

Module Prog (D : DOMAIN) (Pb : PROBLEM D).

  Export D.
  Export Pb.

  (** * Programs and their operational semantics. *)

  Inductive prog : Type :=
  | Nop: prog
  | Flag : cexpr -> prog
  | If : bexpr -> prog -> prog -> prog
  | Seq : prog -> prog -> prog
  | Assert : cexpr -> prog
  | For : string -> aexpr -> aexpr -> prog -> prog.

  Definition array := set cell.

  Inductive exec : vars -> array -> prog -> array -> Prop :=
  | eNop : forall v C,
             exec v C Nop C
  | eFlag : forall v C c,
              exec v C (Flag c) (C ∪ ⎨ceval v c⎬)
  | eIf : forall v C1 C2 B p1 p2,
            exec v C1 (if beval v B then p1 else p2) C2 ->
            exec v C1 (If B p1 p2) C2
  | eSeq : forall v C1 C2 C3 p1 p2,
             exec v C1 p1 C2 -> exec v C2 p2 C3 ->
             exec v C1 (Seq p1 p2) C3
  | eAssert : forall v (C : array) c,
                ceval v c ∈ C \/ ~ceval v c ∈ space -> exec v C (Assert c) C
  | eFor : forall v C x a b p S,
             (forall i, aeval v a <= i <= aeval v b ->
                        exec ((x,i) :: v) (C ∪ ⋃⎨S k, k ∈〚aeval v a, i-1〛⎬)
                             p (C ∪ ⋃⎨S k, k ∈〚aeval v a, i〛⎬)) ->
             exec v C (For x a b p) (C ∪ ⋃⎨S k, k ∈〚aeval v a, aeval v b〛⎬)
  | eEquiv : forall v C1 C1' C2 C2' p,
               C1 ≡ C1' -> C2 ≡ C2' -> exec v C1 p C2 -> exec v C1' p C2'.

  (** * Symbolic execution of programs and verification condition generator. *)

  Fixpoint shape (v : vars) (p : prog) : array :=
    match p with
      | Nop => ∅
      | Flag c => ⎨ceval v c⎬
      | If B p1 p2 => if beval v B then shape v p1 else shape v p2
      | Seq p1 p2 => shape v p1 ∪ shape v p2
      | Assert c => ∅
      | For x a b q =>
        ⋃⎨shape ((x,i) :: v) q, i ∈〚aeval v a, aeval v b〛⎬
    end.

  Fixpoint assertless (p : prog) : Prop :=
    match p with
      | Nop => True
      | Flag c => True
      | If B p1 p2 => assertless p1 /\ assertless p2
      | Seq p1 p2 => assertless p1 /\ assertless p2
      | Assert c => False
      | For x a b q => assertless q
    end.

  Fixpoint vc (v : vars) (C : array) (p : prog) : Prop :=
    match p with
      | Nop => True
      | Flag c => True
      | If B p1 p2 => if beval v B then vc v C p1 else vc v C p2
      | Seq p1 p2 => vc v C p1 /\ vc v (C ∪ shape v p1) p2
      | Assert c => (ceval v c) ∈ C \/ ~ceval v c ∈ space
      | For x a b q =>
        forall i, aeval v a <= i <= aeval v b ->
                  vc ((x,i) :: v) (C ∪ shape v (For x a (Int (i-1)) q)) q
    end.

  (** * A few properties of programs. *)

  Lemma exec_extensive :
    forall p v C1 C2,
      exec v C1 p C2 -> forall x, x ∈ C1 -> x ∈ C2.
  Proof.
    intros p v C1 C2 H; induction H; forward'; firstorder.
  Qed.

  Lemma exec_bin_union_r :
    forall p v C1 C2,
      exec v C1 p C2 -> exec v C1 p (C1 ∪ C2).
  Proof.
    intros.
    apply eEquiv with C1 C2; [firstorder| |assumption].
    generalize (exec_extensive _ _ _ _ H); forward'; firstorder.
  Qed.

  Lemma exec_equiv_r :
    forall v C p C1 C2,
      exec v C p C1 -> C1 ≡ C2 -> exec v C p C2.
  Proof. intros; eapply eEquiv; [reflexivity| |]; eassumption. Qed.

  (** The following result [prog_total] is commented out because it is not
   * used in the framework. It is a proof that assertion-free programs
   * terminate, which implies that the Halting Problem corresponding to
   * our DSL is decidable. In particular, it proves that this language is
   * not Turing-complete. *)
  (*
  Lemma bin_union_left_reg :
    forall U (A B C : set U), B ≡ C -> A ∪ B ≡ A ∪ C. 
  Proof.
    forward'.
  Qed.

  Lemma prog_total :
    forall p, assertless p -> forall v C, exec v C p (C ∪ shape v p).
  Proof.
    induction p; simpl; intros.
    apply exec_equiv_r with C.
    constructor.
    forward. lhs; forward.
    constructor.
    destruct H as [H1 H2]; specialize (IHp1 H1); specialize (IHp2 H2).
    constructor.
    destruct (beval v b).
    now apply IHp1.
    now apply IHp2.
    econstructor.
    destruct H as [H1 H2].
    now apply IHp1.
    apply exec_equiv_r with ((C ∪ shape v p1) ∪ shape v p2).
    now apply IHp2.
    forward'.
    inversion H.
    constructor; intros.
    apply exec_equiv_r
    with ((C ∪ ⋃ ⎨ (shape ((s, k) :: v) p),
           k ∈  〚 aeval v a, i-1 〛⎬) ∪ shape ((s,i) :: v) p).
    apply IHp.
    assumption.
    rewrite bin_union_assoc.
    apply bin_union_left_reg.
    symmetry. apply param_union_bin.
    apply H0.
  Qed.
*)

  (** Main correctness result.
   *
   * Correctness of both the symbolic execution function and the verification
   * condition generator. *)

  Theorem vc_sexec_correct :
    forall p v C,
      vc v C p -> exec v C p (C ∪ (shape v p)).
  Proof.
    induction p; simpl; intros.
    + eapply exec_equiv_r; [constructor|];
      now autorewrite with set_setoid.
    + eapply exec_equiv_r; [constructor|reflexivity].
    + constructor. destruct (beval v b); [now apply IHp1 | now apply IHp2].
    + econstructor.
      now apply IHp1.
      eapply exec_equiv_r.
      now apply IHp2.
      now setoid_rewrite bin_union_assoc.
    + eapply exec_equiv_r. now constructor.
      now autorewrite with set_setoid.
    + constructor.
      intros i Hi.
      eapply exec_equiv_r.
      2: setoid_rewrite param_union_bin; [reflexivity | omega].
      eapply exec_equiv_r.
      2: setoid_rewrite <- bin_union_assoc; reflexivity.
      apply IHp.
      now apply H.
  Qed.

  Definition correct p :=
    exec [] ∅ p (∅ ∪ shape [] p) /\ shape [] p ⊆ target.

  (** Handy tactic applying the main correctness result. *)
  Tactic Notation "symbolic" "execution" :=
    apply vc_sexec_correct; simpl.

  (** [Fire c] is meant to be used when one wants to compute cell [c].  It
   * automatically check dependencies. *)
  Definition Fire c :=
    fold_right Seq (Flag c) (map (fun d => Assert d) (dep c)).

  (** * Program simplification.
   *
   * For now, it only evaluates constants. *)

  Fixpoint psimpl (p : prog) :=
    match p with
      | Nop => Nop
      | Flag c => Flag c
      | If B p1 p2 =>
        match bsimpl B with
          | Bool b => if b then psimpl p1 else psimpl p1
          | v => If v p1 p2
        end
      | Seq p1 p2 => Seq (psimpl p1) (psimpl p2)
      | Assert c => Assert (csimpl c)
      | For x a b q =>
        For x (asimpl a) (asimpl b) (psimpl q)
    end.

  (** XXX: Prove the correctness of program simplification.*)
  (*  Fact psimpl_correct :
    forall p v C D, exec v C p D -> exec v C (psimpl p) D.
  Proof.
    induction p; intros; simpl; auto.
    inv H.
    specialize (IHp1 v C D
   *)

  (** * Notations for programs *)

  Delimit Scope prog_scope with prog.

  Notation "'Nop'" :=
    Nop : prog_scope.
  Notation "'If' b 'Then' p1 'Else' p2" :=
    (If b%bexpr p1 p2) (at level 80, right associativity) : prog_scope.
  Notation "p1 ;; p2" :=
    (Seq p1 p2) (at level 80, right associativity) : prog_scope.
  Notation "'For' i 'From' a 'To' b 'Do' p" :=
    (For i a%aexpr b%aexpr p)
      (at level 80, right associativity) : prog_scope.

End Prog.