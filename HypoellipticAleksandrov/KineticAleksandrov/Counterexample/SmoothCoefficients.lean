module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyNativeMeasure
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization

/-!
# Spatial smoothing preserves the same Loewner interval

Matrix convolution uses the native product volume and the normalized positive kernel.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory ContinuousLinearMap
open Filter
open scoped MatrixOrder Convolution Matrix.Norms.Elementwise Topology

/-- Use the existing entrywise measurable structure locally. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

/-- The entrywise measurable structure is Borel. -/
local instance matrixBorelSpace (d : ℕ) : BorelSpace (PDE.Mat d) := by
  change BorelSpace (Fin d → Fin d → ℝ)
  infer_instance

/-- The finite entrywise product topology is second countable. -/
local instance matrixSecondCountable (d : ℕ) : SecondCountableTopology (PDE.Mat d) := by
  change SecondCountableTopology (Fin d → Fin d → ℝ)
  infer_instance

/-- The entrywise topology has its existing finite product metric. -/
local instance matrixPseudoMetrizable (d : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
  infer_instance

/-- The existing entrywise norm is continuous. -/
local instance matrixContinuousENorm (d : ℕ) : ContinuousENorm (PDE.Mat d) := by
  change ContinuousENorm (Fin d → Fin d → ℝ)
  infer_instance

/-- Loewner upper intervals are closed in the entrywise topology. -/
local instance matrixClosedIci (d : ℕ) : ClosedIciTopology (PDE.Mat d) where
  isClosed_Ici A := by
    change IsClosed {B : PDE.Mat d | A ≤ B}
    simp only [Matrix.le_iff]
    exact Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)

private theorem matrix_orderedModule (d : ℕ) : IsOrderedModule ℝ (PDE.Mat d) := by
  apply IsOrderedModule.of_smul_nonneg
  intro a ha B hB
  rw [Matrix.le_iff] at hB ⊢
  simpa only [sub_zero] using (show B.PosSemidef by simpa only [sub_zero] using hB).smul ha

/-- Spatial convolution of an autonomous matrix field. -/
def mollifiedMatrix {d : ℕ} (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) :
    (PDE.Vec d × PDE.Vec d) → PDE.Mat d :=
  phi.normed volume ⋆[lsmul ℝ ℝ, volume] A

/-- Entrywise smoothness follows from smoothing a locally integrable matrix field. -/
theorem mollifiedMatrix_contDiff {d : ℕ}
    (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (hA : LocallyIntegrable A volume) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedMatrix phi A) :=
  (phi.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (lsmul ℝ ℝ)
    phi.contDiff_normed hA

/-- Positive normalized convolution preserves the exact lower and upper ellipticity
constants; local integrability is the genuine analytic hypothesis for this general lemma. -/
theorem smooth_coefficients_same_bounds_of_locallyIntegrable {d : ℕ}
    (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (hA : LocallyIntegrable A volume)
    (lam Lam : ℝ)
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d))
    (q : PDE.Vec d × PDE.Vec d) :
    lam • (1 : PDE.Mat d) ≤ mollifiedMatrix phi A q ∧
      mollifiedMatrix phi A q ≤ Lam • (1 : PDE.Mat d) := by
  have : IsOrderedModule ℝ (PDE.Mat d) := matrix_orderedModule d
  have hi := (phi.hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
    (phi.contDiff_normed (n := 0)).continuous hA q
  have hc (c : ℝ) : Integrable (fun y => phi.normed volume y •
      (c • (1 : PDE.Mat d))) volume := phi.integrable_normed.smul_const _
  have he (c : ℝ) : (∫ y, phi.normed volume y • (c • (1 : PDE.Mat d))) =
      c • (1 : PDE.Mat d) := by
    rw [integral_smul_const, phi.integral_normed, one_smul]
  change lam • (1 : PDE.Mat d) ≤ ∫ y, phi.normed volume y • A (q - y) ∧
    (∫ y, phi.normed volume y • A (q - y)) ≤ Lam • (1 : PDE.Mat d)
  constructor
  · rw [← he lam]
    exact @integral_mono _ (PDE.Mat d) _ _ _ volume Matrix.instPartialOrder
      Matrix.instIsOrderedAddMonoid (matrix_orderedModule d) (matrixClosedIci d)
      _ _ (hc lam) hi (fun y =>
        smul_le_smul_of_nonneg_left (hbound (q - y)).1 (phi.nonneg_normed y))
  · rw [← he Lam]
    exact @integral_mono _ (PDE.Mat d) _ _ _ volume Matrix.instPartialOrder
      Matrix.instIsOrderedAddMonoid (matrix_orderedModule d) (matrixClosedIci d)
      _ _ hi (hc Lam) (fun y =>
        smul_le_smul_of_nonneg_left (hbound (q - y)).2 (phi.nonneg_normed y))


/-- A Borel matrix field in a fixed scalar Loewner interval is locally integrable
on the native spatial carrier, with no continuity assumption. -/
theorem locallyIntegrable_matrix_of_ellipticity {d : ℕ}
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun y => A y i k))
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d)) :
    LocallyIntegrable A volume := by
  have hm : Measurable A := measurable_pi_iff.mpr
    (fun i => measurable_pi_iff.mpr (hA i))
  have hC : 0 ≤ 3 * (|lam| + |Lam|) := by positivity
  intro q
  obtain ⟨D, hD, hDf⟩ :=
    (volume : Measure (PDE.Vec d × PDE.Vec d)).finiteAt_nhds q
  refine ⟨D, hD, IntegrableOn.of_bound hDf hm.aestronglyMeasurable
    (3 * (|lam| + |Lam|)) ?_⟩
  filter_upwards [] with y
  apply (Matrix.norm_le_iff hC).2
  intro i k
  rw [Real.norm_eq_abs]
  exact HypoellipticAleksandrov.Parabolic.coefficient_entry_abs_le_of_ellipticity
    (hbound y).1 (hbound y).2 i k

/-- Measurable elliptic coefficients can be smoothed without changing either bound. -/
theorem smooth_coefficients_same_bounds {d : ℕ}
    (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun y => A y i k))
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedMatrix phi A) ∧
      ∀ q, lam • (1 : PDE.Mat d) ≤ mollifiedMatrix phi A q ∧
        mollifiedMatrix phi A q ≤ Lam • (1 : PDE.Mat d) := by
  have hi := locallyIntegrable_matrix_of_ellipticity A lam Lam hA hbound
  exact ⟨mollifiedMatrix_contDiff phi A hi,
    smooth_coefficients_same_bounds_of_locallyIntegrable phi A hi lam Lam hbound⟩

/-- The concrete smoothed matrix sequence tends to the original measurable elliptic
matrix almost everywhere in native spatial volume. -/
theorem ae_tendsto_mollifiedMatrix {d : ℕ}
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun y => A y i k))
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d)) :
    ∀ᵐ q ∂volume,
      Tendsto (fun n => mollifiedMatrix (standardMollifierSequence n) A q)
        atTop (𝓝 (A q)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    standardMollifierSequence_rOut_tendsto
    (Filter.Eventually.of_forall standardMollifierSequence_radius_ratio)
    (locallyIntegrable_matrix_of_ellipticity A lam Lam hA hbound)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
