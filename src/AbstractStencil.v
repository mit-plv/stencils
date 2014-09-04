(** Abstract notion of stencil *)

Module Type Stencil.
  Parameter cell : Set.
  Parameter dep : cell -> cell -> Prop.
  Parameter final : cell -> Prop.
End Stencil.