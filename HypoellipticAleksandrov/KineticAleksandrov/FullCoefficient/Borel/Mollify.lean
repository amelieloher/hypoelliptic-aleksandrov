module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Borel.Representative
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelRepresentative
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollification of full coefficients in all three variables

The passage from smooth to Borel coefficients. A Borel symmetric coefficient
`B(t,x,v)` with `λ I ≤ B ≤ Λ I` everywhere is convolved with a normalised bump on
`ℝ × (ℝ^d × ℝ^d)`. The result is smooth, symmetric, satisfies the same everywhere bounds, and
converges to `B` almost everywhere along shrinking bumps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory MeasureTheory.Measure Filter Set ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.Elementwise Convolution Topology ContDiff

attribute [local instance] HypoellipticAleksandrov.KineticAleksandrov.borelMatrixContinuousENorm

private instance {d : ℕ} : CompleteSpace (PDE.Mat d) :=
  inferInstanceAs (CompleteSpace (Fin d → Fin d → ℝ))

private instance vecAddHaar (d : ℕ) : (volume : Measure (PDE.Vec d)).IsAddHaarMeasure :=
  inferInstanceAs ((volume : Measure (Fin d → ℝ)).IsAddHaarMeasure)

private instance pairAddHaar (d : ℕ) :
    (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (PDE.Vec d)) (volume : Measure (PDE.Vec d))

private instance phaseAddHaar (d : ℕ) :
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ)
    (volume : Measure (PDE.Vec d × PDE.Vec d))

private instance phaseRegular (d : ℕ) :
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

private instance phaseNegInvariant (d : ℕ) :
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

/-- Normalised convolution acts in the time, position and velocity variables. -/
def fullSmoothCoefficient {d : ℕ} (φ : ContDiffBump (0 : ℝ × (PDE.Vec d × PDE.Vec d)))
    (A : FullKineticCoefficient d) : FullKineticCoefficient d := fun t x v =>
  (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fullCoefficientProd A) (t, (x, v))

/-- Everywhere bounded Borel coefficients are locally integrable in product coordinates. -/
theorem fullCoefficientProd_locallyIntegrable {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : FullKineticCoefficient d)
    (hBorel : Measurable (fullCoefficientProd A))
    (hlo : ∀ t x v, lam • (1 : PDE.Mat d) ≤ A t x v)
    (hhi : ∀ t x v, A t x v ≤ Lam • (1 : PDE.Mat d)) :
    LocallyIntegrable (fullCoefficientProd A) volume := by
  let : ContinuousENorm (PDE.Mat d) :=
    inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))
  let : TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have hLam0 : 0 ≤ Lam := hlam.le.trans hLam
  apply (locallyIntegrable_const Lam).mono hBorel.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg hLam0, Matrix.norm_le_iff hLam0]
  intro i j
  exact HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hlo z.1 z.2.1 z.2.2)
    (hhi z.1 z.2.1 z.2.2) i j

/-- Convolution preserves the exact bounds while making the coefficient smooth. -/
theorem fullSmoothCoefficient_spec {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : FullKineticCoefficient d)
    (hBorel : Measurable (fullCoefficientProd A))
    (hlo : ∀ t x v, lam • (1 : PDE.Mat d) ≤ A t x v)
    (hhi : ∀ t x v, A t x v ≤ Lam • (1 : PDE.Mat d))
    (φ : ContDiffBump (0 : ℝ × (PDE.Vec d × PDE.Vec d))) :
    IsSmoothFullKineticCoefficient (fullSmoothCoefficient φ A) ∧
    IsSymmetricFullKineticCoefficient (fullSmoothCoefficient φ A) ∧
    HasEverywhereLoewnerBounds lam Lam (fullSmoothCoefficient φ A) := by
  let : TopologicalSpace (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : ContinuousENorm (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toSeminormedAddCommGroup.toSeminormedAddGroup.toContinuousENorm
  have : IsOrderedModule ℝ (PDE.Mat d) :=
    IsOrderedModule.of_smul_nonneg fun a ha M hM =>
      Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp hM).smul ha)
  have : ClosedIciTopology (PDE.Mat d) := ⟨fun M =>
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)⟩
  have hloc := fullCoefficientProd_locallyIntegrable hlam hLam A hBorel hlo hhi
  have hbounds (z : ℝ × (PDE.Vec d × PDE.Vec d)) :
      lam • (1 : PDE.Mat d) ≤ fullCoefficientProd (fullSmoothCoefficient φ A) z ∧
      fullCoefficientProd (fullSmoothCoefficient φ A) z ≤ Lam • (1 : PDE.Mat d) := by
    have hgi := φ.hasCompactSupport_normed.convolutionExists_left
      (μ := volume) (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc z
    have hli := (φ.integrable_normed (μ := volume)).smul_const (lam • (1 : PDE.Mat d))
    have hui := (φ.integrable_normed (μ := volume)).smul_const (Lam • (1 : PDE.Mat d))
    have hl := integral_mono (E := PDE.Mat d) hli hgi fun y =>
      smul_le_smul_of_nonneg_left (hlo (z - y).1 (z - y).2.1 (z - y).2.2)
        (φ.nonneg_normed y)
    have hh := integral_mono (E := PDE.Mat d) hgi hui fun y =>
      smul_le_smul_of_nonneg_left (hhi (z - y).1 (z - y).2.1 (z - y).2.2)
        (φ.nonneg_normed y)
    simpa only [integral_smul_const, φ.integral_normed, one_smul, fullCoefficientProd,
      fullSmoothCoefficient, convolution, lsmul_apply] using And.intro hl hh
  refine ⟨?_, ?_, fun t x v => hbounds (t, (x, v))⟩
  · have hc : ContDiff ℝ ∞ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fullCoefficientProd A) :=
      φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        φ.contDiff_normed hloc
    intro i j
    have hij : ContDiff ℝ ∞ (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fullCoefficientProd A) z i j) :=
      contDiff_pi.mp (contDiff_pi.mp hc i) j
    exact hij
  · intro t x v
    exact Matrix.isHermitian_iff_isSymm.mp
      (HypoellipticAleksandrov.posDef_of_loewner_lower hlam (hbounds (t, (x, v))).1).isHermitian

/-- The shrinking bumps have a fixed ratio of outer and inner radii. -/
def fullCoefficientBump (d j : ℕ) : ContDiffBump (0 : ℝ × (PDE.Vec d × PDE.Vec d)) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
    half_lt_self (by positivity)⟩

/-- Smooth, uniformly elliptic approximation with almost everywhere convergence on phase space. -/
theorem full_coefficient_approximation {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : FullKineticCoefficient d)
    (hBorel : Measurable (fullKineticCoefficientAt A))
    (hsymm : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm)
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) :
    ∃ C : ℕ → FullKineticCoefficient d,
      (∀ j, IsSmoothFullKineticCoefficient (C j) ∧ IsSymmetricFullKineticCoefficient (C j) ∧
        HasEverywhereLoewnerBounds lam Lam (C j)) ∧
      ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
        Tendsto (fun j => fullKineticCoefficientAt (C j) P) atTop
          (𝓝 (fullKineticCoefficientAt A P)) := by
  let B := fullEllipticRepresentative lam Lam A
  obtain ⟨hB, _, hBb, hBA⟩ :=
    fullEllipticRepresentative_spec lam Lam hLam A hBorel hsymm hlo hhi
  have hBprod : Measurable (fullCoefficientProd B) := by
    have h : fullCoefficientProd B =
        fullKineticCoefficientAt B ∘ (KineticPoint.equivProd d).symm := rfl
    rw [h]
    exact hB.comp (KineticPoint.measurable_equivProd_symm d)
  let C := fun j => fullSmoothCoefficient (fullCoefficientBump d j) B
  refine ⟨C, fun j => fullSmoothCoefficient_spec hlam hLam B hBprod
    (fun t x v => (hBb ⟨t, x, v⟩).1) (fun t x v => (hBb ⟨t, x, v⟩).2) _, ?_⟩
  have hr : Tendsto (fun j => (fullCoefficientBump d j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ j in atTop,
      (fullCoefficientBump d j).rOut ≤ 2 * (fullCoefficientBump d j).rIn := by
    filter_upwards with j
    dsimp only [fullCoefficientBump]
    linarith
  have hc := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio
    (fullCoefficientProd_locallyIntegrable hlam hLam B hBprod
      (fun t x v => (hBb ⟨t, x, v⟩).1) (fun t x v => (hBb ⟨t, x, v⟩).2))
  have hc' := (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hc
  filter_upwards [hc', hBA] with P hz heq
  have hz' : Tendsto (fun j => fullKineticCoefficientAt (C j) P) atTop
      (𝓝 (fullKineticCoefficientAt B P)) := hz
  rw [heq] at hz'
  exact hz'

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
