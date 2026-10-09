module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeLocalTestLift
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionMonotone
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local reverse-time separated product distribution

This module localizes the global reverse-time raw identity using the unchanged-function time
and spatial test lifts and the supports of the tests and their derivatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A supplied reverse-time variational energy solution and explicit global product
representatives satisfy every local separated product distribution identity. -/
theorem reverseTime_separated_product_distribution_of_reverseTimeVariationalEnergy
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (τ₁ τ₂ : ℝ)
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
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (U : TimeVelocity d → ℝ)
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (eta : OriginalTimeScalarTest τ₁ τ₂)
    (psi : PDE.WeakTestFunction O) :
    let raw : TimeVelocity d → ℝ := fun z =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1
    Integrable raw
        (timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) ∧
      (∫ z, raw z
        ∂timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) = 0 := by
  dsimp only
  let raw : TimeVelocity d → ℝ := fun z =>
    U z * eta.deriv z.1 * psi z.2 -
      (∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2) * eta z.1 -
      (∑ j : Fin d, reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2) * eta z.1 +
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z * psi z.2 * eta z.1 -
      reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1
  let etaGlobal := reverseTimeScalarTestOfLocal htime eta
  let psiGlobal := psi.mono hOΩ
  have hglobal :=
    reverseTime_global_separated_product_distribution_of_reverseTimeVariationalEnergy
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth initial
      u g hdu hu U hU hUslice G hG hGslice etaGlobal psiGlobal
  have hglobal' :
      Integrable raw
          (timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
        (∫ z, raw z
          ∂timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) = 0 := by
    simpa only [raw, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
      reverseTimeScalarTestOfLocal_deriv, PDE.WeakTestFunction.mono_apply,
      PDE.WeakTestFunction.mono_partialDeriv] using hglobal
  let localSet : Set (TimeVelocity d) := Set.Ioo τ₁ τ₂ ×ˢ O
  let globalSet : Set (TimeVelocity d) := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
  have hlocalGlobal : localSet ⊆ globalSet := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact ⟨htime hτ, hOΩ hy⟩
  have hglobalOpen : IsOpen globalSet := by
    exact (isOpen_Ioo.prod hΩ)
  have hglobalMeas : MeasurableSet globalSet := hglobalOpen.measurableSet
  have hlocalMeas : MeasurableSet localSet := (isOpen_Ioo.prod hO).measurableSet
  have hetaDerivSupport : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
    rw [OriginalTimeScalarTest.deriv, tsupport]
    exact closure_minimal support_deriv_subset (isClosed_tsupport _)
  have hzero : ∀ z ∈ globalSet \ localSet, raw z = 0 := by
    rintro ⟨τ, y⟩ ⟨hglobalMem, hnotLocal⟩
    by_cases hτ : τ ∈ Set.Ioo τ₁ τ₂
    · have hy : y ∉ O := by
        intro hy
        exact hnotLocal ⟨hτ, hy⟩
      have hpsiT : y ∉ tsupport (psi : PDE.Vec d → ℝ) := fun h => hy (psi.tsupport_subset h)
      have hpsi : psi y = 0 := image_eq_zero_of_notMem_tsupport hpsiT
      have hdpsi (i : Fin d) : psi.partialDeriv i y = 0 := by
        unfold PDE.WeakTestFunction.partialDeriv
        rw [fderiv_of_notMem_tsupport ℝ hpsiT]
        rfl
      simp only [raw, hpsi, hdpsi, mul_zero, zero_mul, Finset.sum_const_zero,
        sub_zero, add_zero]
    · have hetaT : τ ∉ tsupport (eta : ℝ → ℝ) := fun h => hτ (eta.tsupport_subset h)
      have heta : eta τ = 0 := image_eq_zero_of_notMem_tsupport hetaT
      have hdetaT : τ ∉ tsupport eta.deriv := fun h => hetaT (hetaDerivSupport h)
      have hdeta : eta.deriv τ = 0 := image_eq_zero_of_notMem_tsupport hdetaT
      simp only [raw, heta, hdeta, mul_zero, zero_mul, sub_zero, add_zero]
  have hmeasure : timeVelocityVolumeOn localSet ≤ timeVelocityVolumeOn globalSet := by
    dsimp only [timeVelocityVolumeOn]
    exact Measure.restrict_mono hlocalGlobal le_rfl
  have hlocalInt : Integrable raw (timeVelocityVolumeOn localSet) :=
    hglobal'.1.mono_measure hmeasure
  refine ⟨?_, ?_⟩
  · simpa only [raw, localSet] using hlocalInt
  · have hintEq :
        (∫ z in globalSet, raw z ∂(volume : Measure (TimeVelocity d))) =
          ∫ z in localSet, raw z ∂(volume : Measure (TimeVelocity d)) :=
      setIntegral_eq_of_subset_of_forall_diff_eq_zero hglobalMeas hlocalGlobal hzero
    have hglobalZero :
        (∫ z in globalSet, raw z ∂(volume : Measure (TimeVelocity d))) = 0 := by
      simpa only [timeVelocityVolumeOn] using hglobal'.2
    have hlocalZero :
        (∫ z in localSet, raw z ∂(volume : Measure (TimeVelocity d))) = 0 := by
      rw [← hintEq, hglobalZero]
    simpa only [raw, localSet, timeVelocityVolumeOn] using hlocalZero

end HypoellipticAleksandrov.Parabolic.Dirichlet
