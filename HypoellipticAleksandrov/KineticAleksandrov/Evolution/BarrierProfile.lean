module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The collar profile `w(d)` as a function of the squared distance

For `κ > 0` and `r₀`, the profile `w(t) = (1 - exp (-κ t)) / κ` composed with the distance
`d = r₀ - √s` to the boundary, as a function of the squared distance `s = |y - m|²` from
the centre.  For `s > 0` the first two derivatives in `s` are
`W' = -exp (-κ d) / (2 √s)` and `W'' = -exp (-κ d) (κ - 1/√s) / (4 s)`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Filter Set
open scoped Topology

/-- The collar profile `w(r₀ - √s)` with `w(t) = (1 - exp (-κ t)) / κ`. -/
def collarProfile (κ r₀ s : ℝ) : ℝ :=
  (1 - Real.exp (-κ * (r₀ - Real.sqrt s))) / κ

/-- First derivative of the collar profile in the squared distance. -/
theorem hasDerivAt_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (collarProfile κ r₀) (-(Real.exp (-κ * (r₀ - Real.sqrt s)) /
      (2 * Real.sqrt s))) s := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have h2 : HasDerivAt (fun s => -κ * (r₀ - Real.sqrt s))
      (-κ * (-(1 / (2 * Real.sqrt s)))) s := (h1.const_sub r₀).const_mul (-κ)
  have h3 := h2.exp
  have h4 := ((hasDerivAt_const s (1 : ℝ)).sub h3).div_const κ
  refine h4.congr_deriv ?_
  field_simp
  ring

/-- The first derivative of the collar profile. -/
theorem deriv_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (collarProfile κ r₀) s =
      -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (2 * Real.sqrt s)) :=
  (hasDerivAt_collarProfile hκ r₀ hs).deriv

/-- Second derivative of the collar profile in the squared distance. -/
theorem hasDerivAt_collarProfile_deriv {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv (collarProfile κ r₀))
      (-(Real.exp (-κ * (r₀ - Real.sqrt s)) / (4 * s)) * (κ - 1 / Real.sqrt s)) s := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have h2 : HasDerivAt (fun s => -κ * (r₀ - Real.sqrt s))
      (-κ * (-(1 / (2 * Real.sqrt s)))) s := (h1.const_sub r₀).const_mul (-κ)
  have h3 := h2.exp
  have h4 : HasDerivAt (fun s => 2 * Real.sqrt s) (2 * (1 / (2 * Real.sqrt s))) s :=
    h1.const_mul 2
  have h5 := (h3.div h4 (by positivity)).neg
  have heq : deriv (collarProfile κ r₀) =ᶠ[𝓝 s]
      fun s => -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (2 * Real.sqrt s)) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact deriv_collarProfile hκ r₀ ht
  refine (h5.congr_of_eventuallyEq heq).congr_deriv ?_
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  generalize Real.sqrt s = ρ at *
  subst hs2
  field_simp
  ring

/-- The collar profile is `C²` away from the centre. -/
theorem contDiffAt_collarProfile (κ r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ 2 (collarProfile κ r₀) s := by
  have h1 : ContDiffAt ℝ 2 Real.sqrt s := contDiffAt_id.sqrt hs.ne'
  unfold collarProfile
  have h2 : ContDiffAt ℝ 2 (fun s => -κ * (r₀ - Real.sqrt s)) s :=
    contDiffAt_const.mul (contDiffAt_const.sub h1)
  exact (contDiffAt_const.sub h2.exp).div_const κ

/-- The second derivative of the collar profile. -/
theorem deriv_deriv_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (deriv (collarProfile κ r₀)) s =
      -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (4 * s)) * (κ - 1 / Real.sqrt s) :=
  (hasDerivAt_collarProfile_deriv hκ r₀ hs).deriv

end HypoellipticAleksandrov.KineticAleksandrov
