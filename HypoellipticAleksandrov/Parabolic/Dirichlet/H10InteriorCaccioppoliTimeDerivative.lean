module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliHessian
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialWeakDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianTimeDerivativeL2Assembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientCancellation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedTestsDetermineWeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2WeakDerivative

/-!
# Interior Hessian and time-derivative recovery from the Caccioppoli estimate

This module assembles the interior Hessian representatives and the literal
reverse-time equation into an interior weak time derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace IsReverseTimeVariationalEnergySolution

/-- The interior Caccioppoli estimate supplies ordered weak spatial Hessian
representatives, with uniform `L²` control of every matrix entry. -/
theorem exists_gradientCoord_representatives_hessian_timeDerivative_uniform_interior_caccioppoli
    {d : ℕ} {Ω inner O : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (hd : 0 < d)
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOnonempty : O.Nonempty) (hOinner : O ⊆ inner)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    ∃ (δ : ℝ) (hδ : 0 < δ)
        (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω),
      ∀ (τ₀ τ₁ τ₂ τ₃ : ℝ)
        (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
        (hτ₁τ₂ : τ₁ < τ₂) (hτ₂τ₃ : τ₂ < τ₃)
        (hτ₃ : τ₃ < r₁ - r₀),
      ∀ (lam Lam M : ℝ) (hlam : 0 < lam)
        (hlamLam : lam ≤ Lam) (hM : 0 ≤ M),
        ∃ C_cac : ℝ, 0 ≤ C_cac ∧
          ∀ (a : CoefficientField d)
            (b : ℝ → PDE.Vec d → PDE.Vec d)
            (c F : ℝ → PDE.Vec d → ℝ),
          ∀ (haSmooth : IsSmoothOnNeighborhood
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
            (hLower : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
            (hUpper : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
            (hcNonpos : ∀ z : TimeVelocity d,
                z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                  c z.1 z.2 ≤ 0)
            (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialMatrixFDerivFrobeniusNorm
                  (fun w : TimeVelocity d =>
                    reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
            (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                PDE.vecEuclideanNorm
                  (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
            (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialVectorFDerivFrobeniusNorm
                  (fun w : TimeVelocity d =>
                    reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
            (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
            (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w : TimeVelocity d =>
                    -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
            (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                spatialScalarFDerivEuclideanNorm
                  (fun w : TimeVelocity d =>
                    -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
          ∀ (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
            (u : ReverseTimeL2V hΩ (r₁ - r₀))
            (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
            (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
              (sub_pos.mpr h₀₁) u g)
            (hu : IsReverseTimeVariationalEnergySolution
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
            ∃ G : Fin d → TimeVelocity d → ℝ,
              (∀ j, MemLp (G j) (2 : ℝ≥0∞)
                (timeVelocityVolumeOn
                  (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
              ∃ H : TimeVelocity d → PDE.Mat d,
                ∃ hHmem : ∀ j k : Fin d,
                    ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                      (2 : ℝ≥0∞) (fun z => H z j k),
                  (∀ j k : Fin d,
                    HasWeakVelocityPartialDerivOn
                      (Set.Ioo τ₁ τ₂ ×ˢ O) k (G j)
                      (fun z => H z j k)) ∧
                  (∀ j k : Fin d,
                    ‖(hHmem j k).toLp (fun z => H z j k)‖ ≤
                      Real.sqrt
                        (C_cac *
                          ((r₁ - r₀) +
                            (reverseTimeGalerkinPrimalRadius
                              r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                              initial) ^ 2))) ∧
                  ∃ U : TimeVelocity d → ℝ,
                    MemLp U (2 : ℝ≥0∞)
                      (timeVelocityVolumeOn
                        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
                    (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
                      ((fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
                        fun y => valueCLM hΩ (u τ) y) ∧
                      (∀ j,
                        (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
                          fun y => gradientCLM hΩ (u τ) y j)) ∧
                    (∀ j : Fin d,
                      HasWeakVelocityPartialDerivOn
                        (Set.Ioo τ₁ τ₂ ×ˢ O) j U (G j)) ∧
                    let W : TimeVelocity d → ℝ := fun z =>
                      (∑ i : Fin d, ∑ j : Fin d,
                        reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
                      (∑ j : Fin d,
                        reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
                      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
                      reverseTimeScalarCoefficient r₁ F z.1 z.2
                    ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                        (2 : ℝ≥0∞) W ∧
                      HasWeakTimeDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) U W := by
  obtain ⟨δ, hδ, hcarrier, hprev⟩ :=
    exists_gradientCoord_representatives_hessian_uniform_interior_caccioppoli
      hd r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOnonempty hOinner η χ
  refine ⟨δ, hδ, hcarrier, ?_⟩
  intro τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
  obtain ⟨C_cac, hC_cac, hprevC⟩ :=
    hprev τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
  refine ⟨C_cac, hC_cac, ?_⟩
  intro a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
    hA hB hBD hq hqD hfD initial u g hdu hu
  obtain ⟨G, hG, hGslice, H, hHmem, hHweak, hHbound⟩ :=
    hprevC a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu
  refine ⟨G, hG, H, hHmem, hHweak, hHbound, ?_⟩
  obtain ⟨U, hU, hUslice⟩ := exists_reverseTimeL2V_value_product_representative hΩ (r₁ - r₀) u
  have hslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ((fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y) ∧
      (∀ j, (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j) := by
    filter_upwards [hUslice, hGslice] with τ hUτ hGτ
    exact ⟨hUτ, hGτ⟩
  have htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀) := by
    intro τ hτ
    exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1), hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
  have hOΩ : O ⊆ Ω := hOinner.trans η.inner_subset_outer
  have hUGlobal :=
    reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
      hΩ (r₁ - r₀) u U hU hUslice G hG hGslice
  have hUweak : ∀ j : Fin d,
      HasWeakVelocityPartialDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) j U (G j) := by
    intro j
    exact (hUGlobal j).restrict (Set.prod_mono htime hOΩ)
  let W : TimeVelocity d → ℝ := fun z =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
    (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
    reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
    reverseTimeScalarCoefficient r₁ F z.1 z.2
  have hUlocal : ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) U :=
    hU.mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono htime hOΩ))
  have hGlocal : ∀ j,
      ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) (G j) := fun j =>
    (hG j).mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono htime hOΩ))
  have hW : ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) W :=
    hessianTimeDerivative_memLp r₀ r₁ τ₁ τ₂ hΩ hΩbounded hOopen hOΩ htime
      a b c F haSmooth hbSmooth hcSmooth hFSmooth U hUlocal G hGlocal H hHmem
  have hsep :=
    reverseTime_separated_hessian_coefficient_cancellation
      r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOΩ τ₁ τ₂ htime a b c F haSmooth hbSmooth
      hcSmooth hFSmooth initial u g hdu hu U hU hUslice G hG hGslice H hHmem hHweak
  have hWweak : HasWeakTimeDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) U W :=
    hasWeakTimeDerivOn_of_forall_separatedProduct hOopen hUlocal hW (by
      intro eta psi
      simpa only [W] using hsep eta psi)
  exact ⟨U, hU, hslice, hUweak, hW, hWweak⟩

end IsReverseTimeVariationalEnergySolution
end HypoellipticAleksandrov.Parabolic.Dirichlet
