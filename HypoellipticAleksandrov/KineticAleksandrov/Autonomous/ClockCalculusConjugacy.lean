module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusLines
import Mathlib.Tactic.FieldSimp

/-! # Exact operator conjugacy for the position clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

private theorem directional_smul (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ)
    (k : ℝ) : directional f (k • d) q = k * directional f d q := by
  simp only [directional, map_smul, smul_eq_mul]

private theorem second_directional_smul (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ)
    (k : ℝ) (hf : ContDiffAt ℝ 2 f q) :
    directional (directional f (k • d)) (k • d) q =
      k ^ 2 * directional (directional f d) d q := by
  have hd : DifferentiableAt ℝ (directional f d) q :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have heq : directional f (k • d) = fun q => k * directional f d q :=
    funext (fun q => directional_smul f d q k)
  rw [heq, directional_smul]
  change k * (fderiv ℝ (fun q => k * directional f d q) q) d = _
  rw [fderiv_const_mul hd k]
  simp only [smul_apply, smul_eq_mul, directional]
  ring

/-- The normalized forward operator in clock field order `(sigma,z,y)`. -/
def Clock.normalizedOperator (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point)
    (h : Point → ℝ) (q : Point) : ℝ :=
  kineticTimeDerivative h q +
    c.diffusion a e q.time (q.velocity 0) * kineticVelocityHessian h q 0 0 +
      c.drift (q.velocity 0) * kineticPositionGradient h q 0

/-- Exact pointwise conjugacy; C-two at the image suffices for this internal chain-rule lemma. -/
theorem Clock.conjugacy_at (c : Clock) (a : ℝ → ℝ → ℝ) (e p : Point)
    (h : Point → ℝ) (hp : p.velocity 0 ∈ c.active)
    (hh : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates (c.map e p))) :
    forwardScalarOperator a (h ∘ c.map e) p =
      |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
        c.normalizedOperator a e h (c.map e p) := by
  have ht := c.pullback_derivatives e p h hh
  have hn := kinetic_derivatives_directional h (c.map e p) hh
  rw [forwardScalarOperator, Clock.normalizedOperator, ht.1, ht.2.1, ht.2.2,
    hn.1, hn.2.1, hn.2.2]
  have hx : directional (h ∘ scalarPoint) c.positionDirection
      (scalarCoordinates (c.map e p)) =
      (1 / (c.vbar * c.r ^ 2)) *
        directional (h ∘ scalarPoint) (coordinateDirection 0)
          (scalarCoordinates (c.map e p)) +
      (1 / c.r ^ 3) * directional (h ∘ scalarPoint) (coordinateDirection 1)
        (scalarCoordinates (c.map e p)) := by
    simp only [Clock.positionDirection, directional, map_add, map_smul, smul_eq_mul]
  rw [hx, Clock.timeDirection, directional_smul, Clock.velocityDirection,
    second_directional_smul _ _ _ _ hh]
  have hpos : e.position 0 + c.vbar * c.r ^ 2 * (c.map e p).time = p.position 0 := by
    have he := congrArg (fun q : Point => q.position 0) (c.inverse_map e p)
    exact he
  have hvel : c.vbar + c.r * (c.map e p).velocity 0 = p.velocity 0 := by
    have he := congrArg (fun q : Point => q.velocity 0) (c.inverse_map e p)
    exact he
  simp only [Clock.diffusion, Clock.drift, hpos, hvel]
  have hr := ne_of_gt c.positive
  have hv := c.nonzero
  have hpne : p.velocity 0 ≠ 0 := by
    have hb := (c.active_abs_bounds hp).1
    have hbpos := abs_pos.mpr c.nonzero
    apply abs_pos.mp
    linarith only [hb, hbpos]
  have hs := c.active_distance hp
  rcases lt_or_gt_of_ne c.nonzero with hc | hc
  · have hpneg : p.velocity 0 < 0 := by
      rw [abs_of_neg hc] at hs
      have hh' := (abs_lt.mp hs).2
      linarith only [hh', hc]
    rw [abs_of_neg hc, abs_of_neg hpneg]
    simp only [Clock.map]
    field_simp [hr, hv, hpne]
    ring
  · have hppos : 0 < p.velocity 0 := by
      rw [abs_of_pos hc] at hs
      have hh' := (abs_lt.mp hs).1
      linarith only [hh', hc]
    rw [abs_of_pos hc, abs_of_pos hppos]
    simp only [Clock.map]
    field_simp [hr, hv, hpne]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
