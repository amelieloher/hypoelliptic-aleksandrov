module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Borel.Mollify
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelMatrixError
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect

/-!
# The fixed compact inner-cylinder coefficient error for full coefficients

The passage from smooth to Borel coefficients. Keep `u` fixed and set
`e_j = |(A_j - A) : D_v² u|`. On a compact set the error is dominated by a constant times the
Frobenius norm of the continuous Hessian, and tends to zero almost everywhere, hence tends to
zero in every finite `L^p` of that compact set.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Filter Set
open scoped MatrixOrder Matrix.Norms.Elementwise Topology

/-- A smooth full coefficient is continuous in kinetic coordinates. -/
theorem continuous_fullKineticCoefficientAt_of_smooth {d : ℕ} {C : FullKineticCoefficient d}
    (h : IsSmoothFullKineticCoefficient C) : Continuous (fullKineticCoefficientAt C) :=
  continuous_pi fun i => continuous_pi fun j =>
    (h i j).continuous.comp (KineticPoint.homeomorphProd d).continuous

/-- The coefficient defect is the absolute literal Hessian contraction. -/
def fullCoefficientError {d : ℕ} (C A : FullKineticCoefficient d)
    (H : KineticPoint d → PDE.Mat d) (P : KineticPoint d) : ℝ :=
  |matrixContraction (fullKineticCoefficientAt C P - fullKineticCoefficientAt A P) (H P)|

/-- On each fixed compact set the classical coefficient error vanishes in `L^p`. -/
theorem full_inner_error {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : FullKineticCoefficient d) (hBorel : Measurable (fullKineticCoefficientAt A))
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    (C : ℕ → FullKineticCoefficient d)
    (hC : ∀ j, IsSmoothFullKineticCoefficient (C j) ∧ IsSymmetricFullKineticCoefficient (C j) ∧
      HasEverywhereLoewnerBounds lam Lam (C j))
    (hc : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      Tendsto (fun j => fullKineticCoefficientAt (C j) P) atTop
        (𝓝 (fullKineticCoefficientAt A P)))
    (K : Set (KineticPoint d)) (hK : IsCompact K)
    (H : KineticPoint d → PDE.Mat d) (hH : ContinuousOn H K) {p : ℝ} (hp : 0 < p) :
    (∀ j, MemLp (fullCoefficientError (C j) A H) (ENNReal.ofReal p) (volume.restrict K)) ∧
    Tendsto (fun j => (eLpNorm (fullCoefficientError (C j) A H)
      (ENNReal.ofReal p) (volume.restrict K)).toReal) atTop (𝓝 0) := by
  let : IsFiniteMeasureOnCompacts (volume : Measure (KineticPoint d)) :=
    Measure.IsFiniteMeasureOnCompacts.map
      (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))
      (KineticPoint.homeomorphProd d).symm
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  let : TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : BorelSpace (PDE.Mat d) :=
    inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hAm : AEStronglyMeasurable (fullKineticCoefficientAt A) (volume.restrict K) :=
    hBorel.aestronglyMeasurable.restrict
  have hHm : AEStronglyMeasurable H (volume.restrict K) :=
    hH.aestronglyMeasurable hK.measurableSet
  have hcontr : Continuous (fun z : PDE.Mat d × PDE.Mat d => matrixContraction z.1 z.2) :=
    continuousOn_univ.mp (continuousOn_matrixContraction
      continuous_fst.continuousOn continuous_snd.continuousOn)
  have hm j : AEStronglyMeasurable (fullCoefficientError (C j) A H) (volume.restrict K) := by
    have hCm : AEStronglyMeasurable (fullKineticCoefficientAt (C j)) (volume.restrict K) :=
      (continuous_fullKineticCoefficientAt_of_smooth (hC j).1).aestronglyMeasurable
    have he i k : Continuous (fun M : PDE.Mat d => M i k) :=
      (continuous_apply k).comp (continuous_apply i)
    have hsum : AEStronglyMeasurable (fun P =>
        matrixContraction (fullKineticCoefficientAt (C j) P - fullKineticCoefficientAt A P)
          (H P)) (volume.restrict K) := by
      unfold matrixContraction
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (((he i k).comp_aestronglyMeasurable hCm).sub
            ((he i k).comp_aestronglyMeasurable hAm)).mul
            ((he i k).comp_aestronglyMeasurable hHm)
    exact (continuous_abs : Continuous (abs : ℝ → ℝ)).comp_aestronglyMeasurable hsum
  have hbounds j : ∀ᵐ P ∂(volume.restrict K), fullCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * borelFrobeniusNorm (H P) := by
    filter_upwards [ae_restrict_of_ae hlo, ae_restrict_of_ae hhi] with P hl hh
    exact borel_coefficient_error_bound hlam hLam hl hh
      ((hC j).2.2 P.time P.position P.velocity).1 ((hC j).2.2 P.time P.position P.velocity).2
      (H P)
  have hFN : ContinuousOn (fun P => borelFrobeniusNorm (H P)) K := by
    have ht := Real.continuous_sqrt.comp_continuousOn (continuousOn_matrixContraction hH hH)
    convert ht using 1
    funext P
    simp only [borelFrobeniusNorm_eq, matrixContraction, pow_two, Function.comp_def]
  obtain ⟨B, hB⟩ := hK.bddAbove_image hFN
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hHM P (hP : P ∈ K) : borelFrobeniusNorm (H P) ≤ M :=
    (hB (mem_image_of_mem _ hP)).trans (le_max_left _ _)
  have hLam0 : 0 ≤ Lam := hlam.le.trans hLam
  have hbound j : ∀ᵐ P ∂(volume.restrict K), fullCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * M := by
    filter_upwards [hbounds j, ae_restrict_mem hK.measurableSet] with P hb hP
    exact hb.trans (mul_le_mul_of_nonneg_left (hHM P hP) (by positivity))
  have heconv : ∀ᵐ P ∂(volume.restrict K),
      Tendsto (fun j => fullCoefficientError (C j) A H P) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hc] with P hP
    have ht := hcontr.continuousAt.tendsto.comp
      ((hP.sub_const (fullKineticCoefficientAt A P)).prodMk_nhds
        (tendsto_const_nhds (x := H P)))
    have ht' := ht.abs
    simpa only [sub_self, matrixContraction, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, abs_zero, Function.comp_def, fullCoefficientError] using ht'
  refine ⟨?_, borel_bounded_error_norm_tendsto (volume.restrict K) hp (by positivity)
    (fun j => fullCoefficientError (C j) A H) hm ?_ hbound heconv⟩
  · intro j
    apply (memLp_const (2 * Real.sqrt d * Lam * M)).of_le (hm j)
    filter_upwards [hbound j] with P hP
    simpa only [fullCoefficientError, Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt d * Lam * M)] using hP
  · exact fun j => Filter.Eventually.of_forall fun P => abs_nonneg _

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
