module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-!
# Integrability of reverse-time separated raw terms

This module isolates the analytic integrability of the five raw families used
in the reverse-time separated product distribution identity.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem reverseTimeCompactCylinder_mapsTo
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) :
    reverseTimeMap r₁ '' (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rintro _ ⟨z, hz, rfl⟩
  rcases z with ⟨τ, y⟩
  rcases hz with ⟨hτ, hy⟩
  simp only [reverseTimeMap_apply]
  exact ⟨⟨by linarith [hτ.2], by linarith [hτ.1]⟩, hy⟩

private theorem reverseTime_openCylinder_volume_lt_top
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (hΩbounded : Bornology.IsBounded Ω) :
    volume (reverseTimeOpenInterval T ×ˢ Ω : Set (TimeVelocity d)) < ⊤ := by
  exact ((Metric.isBounded_Ioo 0 T).prod hΩbounded).measure_lt_top

private theorem integrable_mul_of_memLp_two_of_continuousOn_reverseTime
    {d : ℕ} {S K : Set (TimeVelocity d)} (hSmeas : MeasurableSet S)
    (hSK : S ⊆ K) (hKcompact : IsCompact K) (hSfinite : volume S < ⊤)
    (W q : TimeVelocity d → ℝ)
    (hW : MemLp W 2 (timeVelocityVolumeOn S)) (hq : ContinuousOn q K) :
    Integrable (fun z => W z * q z) (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := by
    change IsFiniteMeasure (volume.restrict S)
    infer_instance
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  refine (hW.integrable (by norm_num)).mul_bdd
    ((hq.mono hSK).aestronglyMeasurable hSmeas) (c := C) ?_
  filter_upwards [ae_restrict_mem hSmeas] with z hz
  exact hC z (hSK hz)

private theorem integrable_of_continuousOn_reverseTime
    {d : ℕ} {S K : Set (TimeVelocity d)} (hSmeas : MeasurableSet S)
    (hSK : S ⊆ K) (hKcompact : IsCompact K) (hSfinite : volume S < ⊤)
    (q : TimeVelocity d → ℝ) (hq : ContinuousOn q K) :
    Integrable q (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := by
    change IsFiniteMeasure (volume.restrict S)
    infer_instance
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  have hqLp : MemLp q (2 : ℝ≥0∞) (timeVelocityVolumeOn S) :=
    MemLp.of_bound ((hq.mono hSK).aestronglyMeasurable hSmeas) C (by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact hC z (hSK hz))
  exact hqLp.integrable (by norm_num)

private theorem continuousOn_of_smoothOnNeighborhood
    {d : ℕ} {K : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f K) : ContinuousOn f K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  exact hV.continuousOn.mono hKV

/-- The five families in the reverse-time separated raw expression are integrable. -/
theorem raw_reverseTime_separated_product_families_integrable
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
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
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    (∀ i j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    (∀ j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
  let S : Set (TimeVelocity d) := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
  let K : Set (TimeVelocity d) := Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω
  have hSmeas : MeasurableSet S := by
    have htime : IsOpen (reverseTimeOpenInterval (r₁ - r₀)) := by
      simpa only [reverseTimeOpenInterval] using isOpen_Ioo
    exact (htime.prod hΩ).measurableSet
  have hSK : S ⊆ K := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact ⟨⟨le_of_lt hτ.1, le_of_lt hτ.2⟩, subset_closure hy⟩
  have hKcompact : IsCompact K := isCompact_Icc.prod hΩbounded.isCompact_closure
  have hSfinite : volume S < ⊤ :=
    reverseTime_openCylinder_volume_lt_top hΩbounded
  have hmap := reverseTimeCompactCylinder_mapsTo (d := d) (Ω := Ω) r₀ r₁
  have hpsi : Continuous (fun z : TimeVelocity d => psi z.2 * eta z.1) :=
    (psi.contDiff.continuous.comp continuous_snd).mul
      (eta.contDiff.continuous.comp continuous_fst)
  have hmassMultiplier : Continuous (fun z : TimeVelocity d => eta.deriv z.1 * psi z.2) :=
    (eta.contDiff.continuous_deriv (by simp)).comp continuous_fst |>.mul
      (psi.contDiff.continuous.comp continuous_snd)
  have hmass := integrable_mul_of_memLp_two_of_continuousOn_reverseTime
    hSmeas hSK hKcompact hSfinite U _ hU hmassMultiplier.continuousOn
  have hprincipal : ∀ i j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1) (timeVelocityVolumeOn S) := by
    intro i j
    have hsmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap
      (IsSmoothOnNeighborhood.coefficientEntry a haSmooth i j)
    have hcoeff : ContinuousOn (fun z : TimeVelocity d =>
        reverseTimeCoefficient r₁ a z.1 z.2 i j) K := by
      simpa only [Function.comp_def, reverseTimeMap_apply,
        reverseTimeCoefficient_apply] using continuousOn_of_smoothOnNeighborhood hsmooth
    have hpartial : Continuous (fun z : TimeVelocity d =>
        psi.partialDeriv i z.2 * eta z.1) :=
      ((psi.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const |>.comp
        continuous_snd).mul (eta.contDiff.continuous.comp continuous_fst)
    have h := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
      hKcompact hSfinite (G j) (fun z =>
        reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (psi.partialDeriv i z.2 * eta z.1)) (hG j)
        (hcoeff.mul hpartial.continuousOn)
    refine h.congr (ae_of_all _ fun z => ?_)
    ring
  have hdrift : ∀ j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * G j z *
        psi z.2 * eta z.1) (timeVelocityVolumeOn S) := by
    intro j
    have hsmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap
      (IsSmoothOnNeighborhood.divergenceDriftEntry a b haSmooth hbSmooth j)
    have hcoeff : ContinuousOn (fun z : TimeVelocity d =>
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) K := by
      simpa only [Function.comp_def, reverseTimeMap_apply,
        reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
        reverseTimeVectorCoefficient_apply, Pi.sub_apply] using
          continuousOn_of_smoothOnNeighborhood hsmooth
    have h := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
      hKcompact hSfinite (G j) (fun z =>
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * (psi z.2 * eta z.1))
        (hG j) (hcoeff.mul hpsi.continuousOn)
    refine h.congr (ae_of_all _ fun z => ?_)
    ring
  have hscalarSmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap hcSmooth
  have hscalarCoeff : ContinuousOn (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2) K := by
    simpa only [Function.comp_def, reverseTimeMap_apply,
      reverseTimeScalarCoefficient_apply] using
        continuousOn_of_smoothOnNeighborhood hscalarSmooth
  have hscalar := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
    hKcompact hSfinite U (fun z =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * (psi z.2 * eta z.1)) hU
      (hscalarCoeff.mul hpsi.continuousOn)
  have hsourceSmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap hFSmooth
  have hsourceCoeff : ContinuousOn (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2) K := by
    simpa only [Function.comp_def, reverseTimeMap_apply,
      reverseTimeScalarCoefficient_apply] using
        continuousOn_of_smoothOnNeighborhood hsourceSmooth
  have hsource := integrable_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite
    (fun z => reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1)
    ((hsourceCoeff.mul (psi.contDiff.continuous.comp continuous_snd).continuousOn).mul
      (eta.contDiff.continuous.comp continuous_fst).continuousOn)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, mul_assoc] using hmass
  · intro i j; simpa only [S] using hprincipal i j
  · intro j; simpa only [S] using hdrift j
  · refine hscalar.congr (ae_of_all _ fun z => ?_)
    ring
  · simpa only [S] using hsource

/-- Integrability of the five families implies integrability of the literal raw sum. -/
theorem integrable_full_reverseTime_separated_product_of_raw_families
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (U : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω)
    (hmass : Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hprincipal : ∀ i j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hdrift : ∀ j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hscalar : Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hsource : Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) :
    Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 *
          psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
  have hprincipalSum : Integrable (fun z : TimeVelocity d =>
      ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    apply integrable_finset_sum Finset.univ
    intro i _
    apply integrable_finset_sum Finset.univ
    intro j _
    exact hprincipal i j
  have hdriftSum : Integrable (fun z : TimeVelocity d =>
      ∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
          G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    apply integrable_finset_sum Finset.univ
    intro j _
    exact hdrift j
  have hprincipal' : Integrable (fun z : TimeVelocity d =>
      (∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2) * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    refine hprincipalSum.congr (ae_of_all _ fun z => ?_)
    simp only [Finset.sum_mul]
  have hdrift' : Integrable (fun z : TimeVelocity d =>
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
          G j z * psi z.2) * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    refine hdriftSum.congr (ae_of_all _ fun z => ?_)
    simp only [Finset.sum_mul]
  exact (((hmass.sub hprincipal').sub hdrift').add hscalar).sub hsource

end HypoellipticAleksandrov.Parabolic.Dirichlet
