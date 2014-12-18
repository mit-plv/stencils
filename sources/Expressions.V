Require Import ZArith String List.
Import ListNotations.
Local Open Scope Z_scope.

(** Arithmetic and boolean expressions *)

Inductive aexpr : Set :=
| Int : Z -> aexpr
| Var : string -> aexpr
| Add : aexpr -> aexpr -> aexpr
| Sub : aexpr -> aexpr -> aexpr
| Mul : aexpr -> aexpr -> aexpr
| Div : aexpr -> aexpr -> aexpr
| Mod : aexpr -> aexpr -> aexpr.

Inductive bexpr : Set :=
| Bool : bool -> bexpr
| Neg  : bexpr -> bexpr
| Eq   : aexpr -> aexpr -> bexpr
| Lt   : aexpr -> aexpr -> bexpr
| Le   : aexpr -> aexpr -> bexpr
| Gt   : aexpr -> aexpr -> bexpr
| Ge   : aexpr -> aexpr -> bexpr
| And  : bexpr -> bexpr -> bexpr
| Or   : bexpr -> bexpr -> bexpr.

(** Environments and expression evaluation *)

Definition vars := list (string * Z).

Fixpoint lookup (v : vars) (x : string) : Z :=
  match v with
    | (y,k) :: vs => if string_dec y x then k else lookup vs x
    | _ => 0
  end.

Fixpoint aeval (v : vars) (e : aexpr) : Z :=
  match e with
    | Int c => c
    | Var x => lookup v x
    | Add e1 e2 => aeval v e1 + aeval v e2
    | Sub e1 e2 => aeval v e1 - aeval v e2
    | Mul e1 e2 => aeval v e1 * aeval v e2
    | Div e1 e2 => aeval v e1 / aeval v e2
    | Mod e1 e2 => aeval v e1 mod aeval v e2
  end.

Fixpoint beval (v : vars) (e : bexpr) : bool :=
  match e with
    | Bool b => b
    | Neg e' => negb (beval v e')
    | Eq e1 e2 => Z.eqb (aeval v e1) (aeval v e2)
    | Lt e1 e2 => Z.ltb (aeval v e1) (aeval v e2)
    | Le e1 e2 => Z.leb (aeval v e1) (aeval v e2)
    | Gt e1 e2 => Z.gtb (aeval v e1) (aeval v e2)
    | Ge e1 e2 => Z.geb (aeval v e1) (aeval v e2)
    | And e1 e2 => andb (beval v e1) (beval v e2)
    | Or e1 e2  => orb  (beval v e1) (beval v e2)
  end.

(** Simple optimization: A partial evaluator for expressions *)

Fixpoint asimpl (e : aexpr) : aexpr :=
  match e with
    | Int c => Int c
    | Var x => Var x
    | Add e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Int (c1 + c2)
        | (v1, v2) => Add v1 v2
      end
    | Sub e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Int (c1 - c2)
        | (v1, v2) => Sub v1 v2
      end
    | Mul e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Int (c1 * c2)
        | (v1, v2) => Mul v1 v2
      end
    | Div e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Int (c1 / c2)
        | (v1, v2) => Div v1 v2
      end
    | Mod e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Int (c1 mod c2)
        | (v1, v2) => Mod v1 v2
      end
  end.

Fixpoint bsimpl (e : bexpr) : bexpr :=
  match e with
    | Bool b => Bool b
    | Neg e' =>
      match bsimpl e' with
        | Bool b => Bool (negb b)
        | v => Neg v
      end
    | Eq e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Bool (Z.eqb c1 c2)
        | (v1, v2) => Eq v1 v2
      end
    | Lt e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Bool (Z.ltb c1 c2)
        | (v1, v2) => Lt v1 v2
      end
    | Le e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Bool (Z.leb c1 c2)
        | (v1, v2) => Le v1 v2
      end
    | Gt e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Bool (Z.gtb c1 c2)
        | (v1, v2) => Gt v1 v2
      end
    | Ge e1 e2 =>
      match (asimpl e1, asimpl e2) with
        | (Int c1, Int c2) => Bool (Z.geb c1 c2)
        | (v1, v2) => Ge v1 v2
      end
    | And e1 e2 =>
      match (bsimpl e1, bsimpl e2) with
        | (Bool b1, Bool b2) => Bool (andb b1 b2)
        | (v1, v2) => And v1 v2
      end
    | Or e1 e2  =>
      match (bsimpl e1, bsimpl e2) with
        | (Bool b1, Bool b2) => Bool (orb b1 b2)
        | (v1, v2) => Or v1 v2
      end
  end.

Fact asimpl_correct :
  forall e v, aeval v e = aeval v (asimpl e).
Proof.
  induction e; intros; try reflexivity;
  specialize (IHe1 v); specialize (IHe2 v); simpl;
  destruct (asimpl e1), (asimpl e2);
  now rewrite IHe1, IHe2.
Qed.

Fact bsimpl_correct :
  forall e v, beval v e = beval v (bsimpl e).
Proof.
  induction e; intros; try reflexivity;
  try (simpl;
       generalize (asimpl_correct a v); intro Ha;
       generalize (asimpl_correct a0 v); intro Ha0;
       destruct (asimpl a), (asimpl a0);
       now rewrite Ha, Ha0);
  try (specialize (IHe1 v); specialize (IHe2 v); simpl;
       destruct (bsimpl e1), (bsimpl e2);
       now rewrite IHe1, IHe2).
  specialize (IHe v); simpl.
  destruct (bsimpl e); now rewrite IHe.
Qed.

(** Notations for arithmetic expressions *)

Delimit Scope aexpr_scope with aexpr.

Coercion Int : Z >-> aexpr.
Coercion Var : string >-> aexpr.

Notation "e1 + e2" :=
  (Add e1%aexpr e2%aexpr) : aexpr_scope.
Notation "e1 - e2" :=
  (Sub e1%aexpr e2%aexpr) : aexpr_scope.
Notation "e1 * e2" :=
  (Mul e1%aexpr e2%aexpr) : aexpr_scope.
Notation "e1 / e2" :=
  (Div e1%aexpr e2%aexpr) : aexpr_scope.
Notation "e1 'mod' e2" :=
  (Mod e1%aexpr e2%aexpr) : aexpr_scope.

(** Notations for boolean expressions *)
(* XXX: Fix precedence levels. *)

Delimit Scope bexpr_scope with bexpr.

Coercion Bool : bool >-> bexpr.

Notation "e1 =? e2" :=
  (Eq e1%aexpr e2%aexpr) : bexpr_scope.
Notation "e1 <? e2" :=
  (Lt e1%aexpr e2%aexpr) : bexpr_scope.
Notation "e1 <=? e2" :=
  (Le e1%aexpr e2%aexpr) : bexpr_scope.
Notation "e1 >? e2" :=
  (Gt e1%aexpr e2%aexpr) : bexpr_scope.
Notation "e1 >=? e2" :=
  (Ge e1%aexpr e2%aexpr) : bexpr_scope.
Notation "! b" :=
  (Neg b%bexpr) (at level 35) : bexpr_scope.
Notation "b1 && b2" :=
  (And b1%bexpr b2%bexpr) : bexpr_scope.
Notation "b1 || b2" :=
  (Or b1%bexpr b2%bexpr) : bexpr_scope.
