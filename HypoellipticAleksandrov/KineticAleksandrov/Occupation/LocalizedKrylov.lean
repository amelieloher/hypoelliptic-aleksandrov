module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-!
# Localized source estimate for the companion paper, Proposition 4.2

Admissibility and the localized bound of the companion paper, Proposition 4.2.

Setting: `0 ≤ F ∈ C_c^∞((0,1) × ℝ^d)`, smooth symmetric `B` with `λ ≤ B ≤ Λ`, `α ∈ [0,1)`,
`v_*`, `R > 0` with `R² = max {1, 4 d Λ}`, and `V` a classical solution of
`∂_r V + B : D_v² V = -F` on `(α, 1) × B_R(v_*)` with zero terminal and lateral values.

The reflected and rescaled solution and coefficient are defined here. Interior
admissibility and the localized bound are provided by the interior-estimate modules.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}

/-- The reflected and rescaled solution `u(t, y) = V(1 - R² t, v_* + R y)`. -/
def localizedScaled (R : ℝ) (vStar : PDE.Vec d) (V : TimeVelocity d → ℝ) :
    TimeVelocity d → ℝ :=
  fun z => V (reflectScale R vStar z)

/-- The reflected and rescaled coefficient `a(t, y) = B(1 - R² t, v_* + R y)`. -/
def localizedCoefficient (R : ℝ) (vStar : PDE.Vec d) (B : CoefficientField d) :
    TimeVelocity d → PDE.Mat d :=
  fun z => coefficientAt B (reflectScale R vStar z)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
