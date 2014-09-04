(**
 * * Abstract notion of stencil
 *
 * Every [cell] is to contain a value, which possibly depends on the one of
 * other cells.  This is the meaning of the [dep] predicate. [dep c1 c2] holds
 * if and only if [c2]'s value depends on [c1]'s.  If there is no [c1] such that
 * the latter assertion holds, we assume that [c2]'s value can be computed
 * without any further knowledge.  Finally, [final c] indicates that we want the
 * algorithm to compute [c]'s value.  It is important since [cell] potentially
 * has infinitely many inhabitants.
 *)

Module Type Stencil.
  Parameter cell : Set.
  Parameter dep : cell -> cell -> Prop.
  Parameter final : cell -> Prop.
End Stencil.