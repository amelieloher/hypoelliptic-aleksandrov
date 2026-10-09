import Lake

open Lake DSL

package «hypoelliptic_aleksandrov» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

-- Hörmander's hypoellipticity theorem, from the formalization `hoermander-rothschild-stein`
-- (only its module `Hormander.Interface` and its dependencies are imported).
require hormander from git
  "https://github.com/amelieloher/hoermander-rothschild-stein.git" @ "d1462014b4ca69cf04b250582ea45021aa07b546"


private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- Ambient spaces, measure theory and Sobolev spaces used by the library. -/
lean_lib «PDEFoundation» where
  globs := #[.submodules `PDEFoundation]
  leanOptions := projectLeanOptions

@[default_target]
lean_lib «HypoellipticAleksandrov» where
  globs := #[.andSubmodules `HypoellipticAleksandrov]
  leanOptions := projectLeanOptions

/-- Comparator configuration `AleksandrovComparators/FullCoefficient`: Mathlib-only statements, one intentional
`sorry` per theorem. -/
@[default_target]
lean_lib «FullCoefficientChallenge» where
  roots := #[`AleksandrovComparators.FullCoefficient.Challenge]
  leanOptions := projectLeanOptions

/-- The `AleksandrovComparators/FullCoefficient` statements proved from the library. -/
@[default_target]
lean_lib «FullCoefficientSolution» where
  roots := #[`AleksandrovComparators.FullCoefficient.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `AleksandrovComparators/KineticAleksandrov`: Mathlib-only statements, one intentional
`sorry` per theorem. -/
@[default_target]
lean_lib «KineticAleksandrovChallenge» where
  roots := #[`AleksandrovComparators.KineticAleksandrov.Challenge]
  leanOptions := projectLeanOptions

/-- The `AleksandrovComparators/KineticAleksandrov` statements proved from the library. -/
@[default_target]
lean_lib «KineticAleksandrovSolution» where
  roots := #[`AleksandrovComparators.KineticAleksandrov.Solution]
  leanOptions := projectLeanOptions
