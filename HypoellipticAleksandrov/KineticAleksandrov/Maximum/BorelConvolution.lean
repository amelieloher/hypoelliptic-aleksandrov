module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelRepresentative
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Smooth time--velocity coefficients with unchanged Loewner bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter Set ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.Elementwise Convolution Topology

attribute [local instance] borelMatrixContinuousENorm

private instance {d : ℕ} : CompleteSpace (PDE.Mat d) :=
  inferInstanceAs (CompleteSpace (Fin d → Fin d → ℝ))

/-- Normalised convolution acts only in the time and velocity variables. -/
def borelSmoothCoefficient {d : ℕ} (φ : ContDiffBump (0 : ℝ × PDE.Vec d))
    (A : CoefficientField d) : CoefficientField d := fun t v =>
  (φ.normed volume ⋆[lsmul ℝ ℝ,volume] coefficientAt A) (t,v)

/-- Convolution preserves the exact source bounds while making the coefficient smooth. -/
theorem borelSmoothCoefficient_spec {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (φ : ContDiffBump (0 : ℝ × PDE.Vec d)) :
    IsSmoothCoefficient (borelSmoothCoefficient φ A) ∧
    IsSymmetricCoefficient (borelSmoothCoefficient φ A) ∧
    HasLowerEllipticity lam (borelSmoothCoefficient φ A) ∧
    HasUpperEllipticity Lam (borelSmoothCoefficient φ A) := by
  let : TopologicalSpace (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : ContinuousENorm (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toSeminormedAddCommGroup.toSeminormedAddGroup.toContinuousENorm
  have : (volume : Measure (ℝ × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have : IsOrderedModule ℝ (PDE.Mat d) :=
    IsOrderedModule.of_smul_nonneg fun a ha M hM =>
      Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp hM).smul ha)
  have : ClosedIciTopology (PDE.Mat d) := ⟨fun M =>
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)⟩
  have hloc := borel_coefficient_locallyIntegrable hlam hLam A hBorel hlo hhi
  have hbounds (z : ℝ × PDE.Vec d) :
      lam • (1 : PDE.Mat d) ≤ coefficientAt (borelSmoothCoefficient φ A) z ∧
      coefficientAt (borelSmoothCoefficient φ A) z ≤ Lam • (1 : PDE.Mat d) := by
    have hgi := φ.hasCompactSupport_normed.convolutionExists_left
      (μ := volume) (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc z
    have hli := (φ.integrable_normed (μ := volume)).smul_const (lam • (1 : PDE.Mat d))
    have hui := (φ.integrable_normed (μ := volume)).smul_const (Lam • (1 : PDE.Mat d))
    have hl := integral_mono (E := PDE.Mat d) hli hgi fun y =>
      smul_le_smul_of_nonneg_left (hlo (z - y).1 (z - y).2) (φ.nonneg_normed y)
    have hh := integral_mono (E := PDE.Mat d) hgi hui fun y =>
      smul_le_smul_of_nonneg_left (hhi (z - y).1 (z - y).2) (φ.nonneg_normed y)
    simpa only [integral_smul_const,φ.integral_normed,one_smul,
      coefficientAt,borelSmoothCoefficient,convolution,lsmul_apply] using And.intro hl hh
  refine ⟨?_,?_,fun t v => (hbounds (t,v)).1,fun t v => (hbounds (t,v)).2⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hloc
  · intro t v
    exact Matrix.isHermitian_iff_isSymm.mp
      (HypoellipticAleksandrov.posDef_of_loewner_lower hlam (hbounds (t,v)).1).isHermitian

/-- The shrinking bumps have a fixed ratio of outer and inner radii. -/
def borelCoefficientBump (d j : ℕ) : ContDiffBump (0 : ℝ × PDE.Vec d) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2,1 / ((j : ℝ) + 1),by positivity,
    half_lt_self (by positivity)⟩

/-- Smooth, uniformly elliptic approximation exists with a.e. time--velocity convergence. -/
theorem borel_coefficient_approximation {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A) (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    ∃ C : ℕ → CoefficientField d,
      (∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
        HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j)) ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
        Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)) := by
  have : (volume : Measure (ℝ × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let B := borelEllipticRepresentative lam Lam A
  obtain ⟨hB,_,hBl,hBu,hBA⟩ :=
    borelEllipticRepresentative_spec lam Lam hlam hLam A hBorel hsymm hlo hhi
  let C := fun j => borelSmoothCoefficient (borelCoefficientBump d j) B
  refine ⟨C,fun j => borelSmoothCoefficient_spec hlam hLam B hB hBl hBu _,?_⟩
  have hr : Tendsto (fun j => (borelCoefficientBump d j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ j in atTop,
      (borelCoefficientBump d j).rOut ≤ 2 * (borelCoefficientBump d j).rIn := by
    filter_upwards with j
    dsimp only [borelCoefficientBump]
    linarith
  have hc := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio
    (borel_coefficient_locallyIntegrable hlam hLam B hB hBl hBu)
  filter_upwards [hc,hBA] with z hz heq
  rw [heq] at hz
  convert! hz using 1

end HypoellipticAleksandrov.KineticAleksandrov
