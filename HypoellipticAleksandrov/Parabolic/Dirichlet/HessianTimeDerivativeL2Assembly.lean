module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Local L² assembly of the Hessian-derived time derivative

This module proves local square-integrability of the literal reverse-time
equation carrier assembled from a Hessian, gradient, value, and source.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem memLp_mul_of_continuousOn_of_bound
    {d : ℕ} {S : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ} {M : ℝ}
    (hS : MeasurableSet S) (hf : ContinuousOn f S)
    (hbound : ∀ z ∈ S, |f z| ≤ M)
    (hg : ParabolicMemLpOn S (2 : ℝ≥0∞) g) :
    ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z => f z * g z) := by
  refine MemLp.of_le_mul (c := M) hg ?_ ?_
  · exact (hf.aestronglyMeasurable hS).mul hg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hS] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound z hz) (abs_nonneg _)

/-- The literal coefficient--Hessian, drift--gradient, zeroth-order, and source
combination in the reverse-time equation is locally square-integrable. -/
theorem hessianTimeDerivative_memLp
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (r₀ r₁ τ₁ τ₂ : ℝ)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀))
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (U : TimeVelocity d → ℝ)
    (hU : ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) U)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
      (2 : ℝ≥0∞) (G j))
    (H : TimeVelocity d → PDE.Mat d)
    (hH : ∀ j i, ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
      (2 : ℝ≥0∞) (fun z => H z j i)) :
    ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞)
      (fun z =>
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
        (∑ j : Fin d,
          reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
        reverseTimeScalarCoefficient r₁ F z.1 z.2) := by
  let Qin : Set (TimeVelocity d) := Set.Ioo τ₁ τ₂ ×ˢ O
  have hQin : MeasurableSet Qin := measurableSet_Ioo.prod hO.measurableSet
  let rev : TimeVelocity d → TimeVelocity d := fun z => (r₁ - z.1, z.2)
  have hrev : Continuous rev :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hrevMaps : MapsTo rev Qin (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro z hz
    have ht := htime hz.1
    refine ⟨?_, subset_closure (hOΩ hz.2)⟩
    constructor <;> linarith [ht.1, ht.2]
  rcases haSmooth with ⟨VA, _hVAopen, hKVA, hVA⟩
  rcases hbSmooth with ⟨VB, _hVBopen, hKVB, hVB⟩
  rcases hcSmooth with ⟨VC, _hVCopen, hKVC, hVC⟩
  rcases hFSmooth with ⟨VF, _hVFopen, hKVF, hVF⟩
  have hcontA : ContinuousOn (fun z : TimeVelocity d => a (r₁ - z.1) z.2) Qin :=
    (hVA.continuousOn.mono hKVA).comp hrev.continuousOn hrevMaps
  have hcontB : ContinuousOn (fun z : TimeVelocity d => b (r₁ - z.1) z.2) Qin :=
    (hVB.continuousOn.mono hKVB).comp hrev.continuousOn hrevMaps
  have hcontC : ContinuousOn (fun z : TimeVelocity d => c (r₁ - z.1) z.2) Qin :=
    (hVC.continuousOn.mono hKVC).comp hrev.continuousOn hrevMaps
  have hcontF : ContinuousOn (fun z : TimeVelocity d => F (r₁ - z.1) z.2) Qin :=
    (hVF.continuousOn.mono hKVF).comp hrev.continuousOn hrevMaps
  obtain ⟨MC, hMC⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hVC.continuousOn.mono hKVC)
  obtain ⟨MF, hMF⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hVF.continuousOn.mono hKVF)
  have hAH (i j : Fin d) : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
    obtain ⟨MA, hMA⟩ :=
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
        ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn (hVA.continuousOn.mono hKVA)))
    apply memLp_mul_of_continuousOn_of_bound (M := MA) hQin
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hcontA)) _ (hH j i)
    intro z hz
    change |a (r₁ - z.1) z.2 i j| ≤ MA
    have h := hMA _ (hrevMaps hz)
    change |a (r₁ - z.1) z.2 i j| ≤ MA at h
    exact h
  have hBG (j : Fin d) : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) := by
    obtain ⟨MB, hMB⟩ :=
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
        ((continuous_apply j).comp_continuousOn (hVB.continuousOn.mono hKVB))
    apply memLp_mul_of_continuousOn_of_bound (M := MB) hQin
      ((continuous_apply j).comp_continuousOn hcontB) _ (hG j)
    intro z hz
    change |b (r₁ - z.1) z.2 j| ≤ MB
    simpa only [Real.norm_eq_abs, Function.comp_def, rev] using hMB _ (hrevMaps hz)
  have hCU : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z) := by
    apply memLp_mul_of_continuousOn_of_bound (M := MC) hQin hcontC _ hU
    intro z hz
    exact hMC _ (hrevMaps hz)
  have hQinBounded : Bornology.IsBounded Qin := by
    exact (Metric.isBounded_Ioo τ₁ τ₂).prod (hΩbounded.subset hOΩ)
  letI : IsFiniteMeasure (timeVelocityVolumeOn Qin) :=
    isFiniteMeasure_restrict.mpr hQinBounded.measure_lt_top.ne
  have hF : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => reverseTimeScalarCoefficient r₁ F z.1 z.2) := by
    refine MemLp.of_bound (hcontF.aestronglyMeasurable hQin) MF ?_
    filter_upwards [ae_restrict_mem hQin] with z hz
    exact hMF _ (hrevMaps hz)
  have hsumAH : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
    exact memLp_finset_sum Finset.univ fun i _ =>
      memLp_finset_sum Finset.univ fun j _ => hAH i j
  have hsumBG : ParabolicMemLpOn Qin (2 : ℝ≥0∞)
      (fun z => ∑ j : Fin d,
        reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) := by
    exact memLp_finset_sum Finset.univ fun j _ => hBG j
  exact ((hsumAH.add hsumBG).add hCU).sub hF

end HypoellipticAleksandrov.Parabolic.Dirichlet
