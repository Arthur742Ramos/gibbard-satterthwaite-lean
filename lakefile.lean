import Lake
open Lake DSL

package «gibbard_satterthwaite» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

@[default_target]
lean_lib Arrow where
  roots := #[
    `Arrow.Basic,
    `Arrow.FieldExpansion,
    `Arrow.GroupContraction,
    `Arrow.ArrowTheorem]

@[default_target]
lean_lib GibbardSatterthwaite where
  roots := #[
    `GS.Basic,
    `GS.Reduction,
    `GS.SWF]

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
