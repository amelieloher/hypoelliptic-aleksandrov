module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import Mathlib.Tactic

/-! # Literal source parameters for propagation blocks -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Uniform damping budget on blocks no longer than `T1`. -/
def XiStar (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 * Lam * (128 * (d : ℝ) / lam) + 2 * H ^ 2 * T1 / (3 * lam)

/-- Source Gaussian level, fixed before coefficients, paths, and solutions. -/
def barrierL (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 * Real.sqrt (XiStar d lam Lam H T1)

/-- Source block radius multiplier. -/
def barrierW (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 + 3 / 2 * barrierL d lam Lam H T1 * Real.sqrt lam + 2 * H * Real.sqrt T1

/-- Velocity tube containment coefficient. -/
def velocityTubeConstant (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  let W := barrierW d lam Lam H T1
  W + H * W ^ 2 * Real.sqrt T1

/-- Position tube containment coefficient. -/
def positionTubeConstant (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  let W := barrierW d lam Lam H T1
  W ^ 3 + H * W ^ 4 * Real.sqrt T1 / 2

/-- The source minimum of time, velocity, and position step restrictions. -/
def stepSize (d : ℕ) (lam Lam H T0 T1 kx kv : ℝ) : ℝ :=
  min (T0 / (barrierW d lam Lam H T1) ^ 2)
    (min ((kv / (2 * velocityTubeConstant d lam Lam H T1)) ^ 2)
      ((kx / (2 * positionTubeConstant d lam Lam H T1)) ^ (2 / 3 : ℝ)))

/-- Source positive Gaussian gap at the block endpoint. -/
def barrierCb (L : ℝ) : ℝ := Real.exp (-3 / 4 * L ^ 2) - Real.exp (-L ^ 2)

/-- Source amplitude loss at one overlap step. -/
def barrierGamma (L : ℝ) : ℝ := barrierCb L * Real.exp (-L ^ 2 / 512)

/-- The source step is at most its time restriction. -/
theorem stepSize_le_time (d : ℕ) (lam Lam H T0 T1 kx kv : ℝ) :
    stepSize d lam Lam H T0 T1 kx kv ≤ T0 / (barrierW d lam Lam H T1) ^ 2 :=
  min_le_left _ _

/-- The source step is at most its velocity restriction. -/
theorem stepSize_le_velocity (d : ℕ) (lam Lam H T0 T1 kx kv : ℝ) :
    stepSize d lam Lam H T0 T1 kx kv ≤
      (kv / (2 * velocityTubeConstant d lam Lam H T1)) ^ 2 :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- The source step is at most its position restriction. -/
theorem stepSize_le_position (d : ℕ) (lam Lam H T0 T1 kx kv : ℝ) :
    stepSize d lam Lam H T0 T1 kx kv ≤
      (kx / (2 * positionTubeConstant d lam Lam H T1)) ^ (2 / 3 : ℝ) :=
  (min_le_right _ _).trans (min_le_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
