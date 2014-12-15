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
