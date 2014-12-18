Require Import Expressions Sets.

Module Type DOMAIN.

  Parameter cell : Type.
  Parameter cexpr : Type.
  Parameter ceval : vars -> cexpr -> cell.
  Parameter csimpl : cexpr -> cexpr.

End DOMAIN.

Module Type PROBLEM (D : DOMAIN).

  Export D.

  Parameter space : set cell.
  Parameter dep : cexpr -> list cexpr.

End PROBLEM.
