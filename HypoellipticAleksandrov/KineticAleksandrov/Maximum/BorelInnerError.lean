module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelConvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelMatrixError
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelPhaseMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # The fixed compact inner-cylinder coefficient error -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter Set
open scoped MatrixOrder Matrix.Norms.Elementwise Topology

/-- The coefficient defect is the absolute literal Hessian contraction. -/
def borelCoefficientError {d : ℕ} (C A : CoefficientField d)
    (H : KineticPoint d → PDE.Mat d) (P : KineticPoint d) : ℝ :=
  |matrixContraction (C P.time P.velocity - A P.time P.velocity) (H P)|

/-- On each fixed compact set the classical coefficient error vanishes in Lp. -/
theorem borel_inner_error {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (C : ℕ → CoefficientField d)
    (hC : ∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
      HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j))
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)))
    (K : Set (KineticPoint d)) (hK : IsCompact K)
    (H : KineticPoint d → PDE.Mat d) (hH : ContinuousOn H K) {p : ℝ} (hp : 0 < p) :
    (∀ j, ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * borelFrobeniusNorm (H P)) ∧
    (∀ j, MemLp (borelCoefficientError (C j) A H) (ENNReal.ofReal p)
      (volume.restrict K)) ∧
    Tendsto (fun j => (eLpNorm (borelCoefficientError (C j) A H)
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
  change Measurable (coefficientAt A) at hBorel
  have hproj : Measurable (fun P : KineticPoint d => (P.time,P.velocity)) :=
    ((continuous_time (d := d)).prodMk (continuous_velocity (d := d))).measurable
  have hAm : AEStronglyMeasurable
      (fun P : KineticPoint d => A P.time P.velocity) (volume.restrict K) :=
    (hBorel.comp hproj).aestronglyMeasurable.restrict
  have hHm : AEStronglyMeasurable H (volume.restrict K) := hH.aestronglyMeasurable hK.measurableSet
  have hcontr : Continuous (fun z : PDE.Mat d × PDE.Mat d =>
      matrixContraction z.1 z.2) :=
    continuousOn_univ.mp (continuousOn_matrixContraction
      continuous_fst.continuousOn continuous_snd.continuousOn)
  have hm j : AEStronglyMeasurable (borelCoefficientError (C j) A H)
      (volume.restrict K) := by
    have hCs : Continuous (coefficientAt (C j)) := by
      exact (hC j).1.continuous
    have hCm : AEStronglyMeasurable
        (fun P : KineticPoint d => C j P.time P.velocity) (volume.restrict K) :=
      (hCs.measurable.comp hproj).aestronglyMeasurable.restrict
    have he i k : Continuous (fun M : PDE.Mat d => M i k) :=
      (continuous_apply k).comp (continuous_apply i)
    have hsum : AEStronglyMeasurable (fun P =>
        matrixContraction (C j P.time P.velocity - A P.time P.velocity) (H P))
        (volume.restrict K) := by
      unfold matrixContraction
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (((he i k).comp_aestronglyMeasurable hCm).sub
            ((he i k).comp_aestronglyMeasurable hAm)).mul
            ((he i k).comp_aestronglyMeasurable hHm)
    exact (continuous_abs : Continuous (abs : ℝ → ℝ)).comp_aestronglyMeasurable hsum
  have hbounds j : ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * borelFrobeniusNorm (H P) := by
    filter_upwards [ae_restrict_of_ae (borel_timeVelocity_ae_lift hlo),
      ae_restrict_of_ae (borel_timeVelocity_ae_lift hhi)] with P hl hh
    exact borel_coefficient_error_bound hlam hLam hl hh
      ((hC j).2.2.1 P.time P.velocity) ((hC j).2.2.2 P.time P.velocity) (H P)
  have hFN : ContinuousOn (fun P => borelFrobeniusNorm (H P)) K := by
    have ht := Real.continuous_sqrt.comp_continuousOn (continuousOn_matrixContraction hH hH)
    convert ht using 1
    funext P
    simp only [borelFrobeniusNorm_eq,matrixContraction,pow_two,Function.comp_def]
  obtain ⟨B,hB⟩ := hK.bddAbove_image hFN
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hHM P (hP : P ∈ K) : borelFrobeniusNorm (H P) ≤ M :=
    (hB (mem_image_of_mem _ hP)).trans (le_max_left _ _)
  have hLam0 : 0 ≤ Lam := hlam.le.trans hLam
  have hbound j : ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * M := by
    filter_upwards [hbounds j,ae_restrict_mem hK.measurableSet] with P hb hP
    exact hb.trans (mul_le_mul_of_nonneg_left (hHM P hP) (by positivity))
  have heconv : ∀ᵐ P ∂(volume.restrict K),
      Tendsto (fun j => borelCoefficientError (C j) A H P) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (borel_timeVelocity_ae_lift hc)] with P hP
    have ht := hcontr.continuousAt.tendsto.comp
      ((hP.sub_const (A P.time P.velocity)).prodMk_nhds
        (tendsto_const_nhds (x := H P)))
    have ht' := ht.abs
    simpa only [coefficientAt,sub_self,matrixContraction,Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,abs_zero,Function.comp_def,borelCoefficientError] using ht'
  refine ⟨hbounds,?_,borel_bounded_error_norm_tendsto (volume.restrict K) hp (by positivity)
    (fun j => borelCoefficientError (C j) A H) hm ?_ hbound heconv⟩
  · intro j
    apply (memLp_const (2 * Real.sqrt d * Lam * M)).of_le (hm j)
    filter_upwards [hbound j] with P hP
    simpa only [borelCoefficientError,Real.norm_eq_abs,abs_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt d * Lam * M)] using hP
  · exact fun j => Filter.Eventually.of_forall fun P => abs_nonneg _

end HypoellipticAleksandrov.KineticAleksandrov
