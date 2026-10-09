module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Admissible
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Mollifier
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Line derivatives of admissible test functions

An admissible `φ`, viewed as a function `Φ(x) = φ(x.1, x.2)` of `x = (τ, y)`, has line
derivatives in the time, velocity and position directions, equal to `∂_τ φ`, `∂_{v_i} φ`,
`∂_{z_i} φ`, and the velocity partials have line derivatives `∂_{v_i} ∂_{v_j} φ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ}

open MeasureTheory in
/-- Lebesgue measure on phase space is an additive Haar measure. -/
instance volume_isAddHaarMeasure_ambient (d : ℕ) :
    (volume : Measure (EvolutionAmbientState d)).IsAddHaarMeasure := by
  exact Measure.prod.instIsAddHaarMeasure volume volume

open MeasureTheory in
/-- Lebesgue measure on time-phase space is an additive Haar measure. -/
instance volume_isAddHaarMeasure_phaseTime (d : ℕ) :
    (volume : Measure (ℝ × EvolutionAmbientState d)).IsAddHaarMeasure := by
  exact Measure.prod.instIsAddHaarMeasure volume volume

/-- The line derivative of a differentiable function is its Fréchet derivative. -/
theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ} {y : E}
    (hG : DifferentiableAt ℝ G y) (w : E) :
    HasDerivAt (fun s : ℝ => G (y + s • w)) (fderiv ℝ G y w) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => y + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have h2 : HasFDerivAt G (fderiv ℝ G y) (y + (0 : ℝ) • w) := by
    simpa using hG.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) h1

/-- The test function as a function of `(τ, y)`. -/
def testValue (φ : ℝ → EvolutionAmbientState d → ℝ) (x : ℝ × EvolutionAmbientState d) : ℝ :=
  φ x.1 x.2

/-- `∂_τ φ` as a function of `(τ, y)`. -/
def testTime (φ : ℝ → EvolutionAmbientState d → ℝ) (x : ℝ × EvolutionAmbientState d) : ℝ :=
  deriv (fun τ => φ τ x.2) x.1

/-- `∂_{v_i} φ` as a function of `(τ, y)`. -/
def testVelocity (φ : ℝ → EvolutionAmbientState d → ℝ) (i : Fin d)
    (x : ℝ × EvolutionAmbientState d) : ℝ :=
  velocityPartial i (φ x.1) x.2

/-- `∂_{z_i} φ` as a function of `(τ, y)`. -/
def testPosition (φ : ℝ → EvolutionAmbientState d → ℝ) (i : Fin d)
    (x : ℝ × EvolutionAmbientState d) : ℝ :=
  positionPartial i (φ x.1) x.2

/-- `∂_{v_i} ∂_{v_j} φ` as a function of `(τ, y)`. -/
def testHessian (φ : ℝ → EvolutionAmbientState d → ℝ) (i j : Fin d)
    (x : ℝ × EvolutionAmbientState d) : ℝ :=
  velocityPartial i (velocityPartial j (φ x.1)) x.2

variable {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}

theorem differentiable_velocityPartial_slice (hφ : IsAdmissibleTest T φ) (τ : ℝ) (j : Fin d) :
    Differentiable ℝ (velocityPartial j (φ τ)) := by
  have h : ContDiff ℝ 1 (fun y => fderiv ℝ (φ τ) y (Pi.single j 1, 0)) :=
    ((hφ.contDiff_space τ).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h.differentiable (by norm_num)

theorem hasDerivAt_line_time (hφ : IsAdmissibleTest T φ) (x : ℝ × EvolutionAmbientState d) :
    HasDerivAt (fun s : ℝ => testValue φ (x + s • ((1 : ℝ), (0 : EvolutionAmbientState d))))
      (testTime φ x) 0 := by
  have h := ((hφ.contDiff_time x.2).differentiable (by norm_num) x.1).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => φ (x.1 + s) x.2) (deriv (fun τ => φ τ x.2) x.1) 0 := by
    exact HasDerivAt.comp_const_add x.1 0 (by rw [add_zero]; exact h)
  simpa [testValue, testTime] using h2

theorem hasDerivAt_line_velocity (hφ : IsAdmissibleTest T φ) (i : Fin d)
    (x : ℝ × EvolutionAmbientState d) :
    HasDerivAt (fun s : ℝ => testValue φ
      (x + s • ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))))
      (testVelocity φ i x) 0 := by
  have h := hasDerivAt_line (((hφ.contDiff_space x.1).differentiable (by norm_num)) x.2)
    ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d))
  simpa [testValue, testVelocity, velocityPartial] using h

theorem hasDerivAt_line_position (hφ : IsAdmissibleTest T φ) (i : Fin d)
    (x : ℝ × EvolutionAmbientState d) :
    HasDerivAt (fun s : ℝ => testValue φ
      (x + s • ((0 : ℝ), ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d)))))
      (testPosition φ i x) 0 := by
  have h := hasDerivAt_line (((hφ.contDiff_space x.1).differentiable (by norm_num)) x.2)
    ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d))
  simpa [testValue, testPosition, positionPartial] using h

theorem hasDerivAt_line_hessian (hφ : IsAdmissibleTest T φ) (i j : Fin d)
    (x : ℝ × EvolutionAmbientState d) :
    HasDerivAt (fun s : ℝ => testVelocity φ j
      (x + s • ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))))
      (testHessian φ i j x) 0 := by
  have h := hasDerivAt_line (differentiable_velocityPartial_slice hφ x.1 j x.2)
    ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d))
  simpa [testVelocity, testHessian, velocityPartial] using h

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
