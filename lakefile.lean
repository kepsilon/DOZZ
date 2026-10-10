import Lake
open Lake DSL

package «DOZZ» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

@[default_target]
lean_lib «DOZZ» where
  globs := #[.andSubmodules `DOZZ]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

lean_lib «GaussianFields» where
  globs := #[.andSubmodules `GaussianFields]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

/-- Lean options of the comparator libraries (those of the `DOZZ` library). -/
def comparatorLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- Comparator configuration `comparators/DOZZ`: Mathlib-only statements, each with an intentional
`sorry` placeholder as its proof. -/
@[default_target]
lean_lib «DOZZChallenge» where
  roots := #[`comparators.DOZZ.Challenge]
  leanOptions := comparatorLeanOptions

/-- The `comparators/DOZZ` statements proved from the library. -/
@[default_target]
lean_lib «DOZZSolution» where
  roots := #[`comparators.DOZZ.Solution]
  leanOptions := comparatorLeanOptions

/-- Comparator configuration `comparators/Reflection`: Mathlib-only statements, each with an
intentional `sorry` placeholder as its proof. -/
@[default_target]
lean_lib «ReflectionChallenge» where
  roots := #[`comparators.Reflection.Challenge]
  leanOptions := comparatorLeanOptions

/-- The `comparators/Reflection` statements proved from the library. -/
@[default_target]
lean_lib «ReflectionSolution» where
  roots := #[`comparators.Reflection.Solution]
  leanOptions := comparatorLeanOptions
