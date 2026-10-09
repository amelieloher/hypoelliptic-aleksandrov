module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedProductDistribution
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientWeightedWeakIdentity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientCancellationAlgebra

/-! # Cancellation of divergence-form coefficient derivatives -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The divergence derivatives of the principal coefficients cancel against the weak spatial
Hessian identities for separated reverse-time tests. -/
theorem reverseTime_separated_hessian_coefficient_cancellation
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
    (H : TimeVelocity d → PDE.Mat d)
    (hHmem : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) (fun z => H z j i))
    (hHweak : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) i (G j) (fun z => H z j i)) :
    ∀ (eta : OriginalTimeScalarTest τ₁ τ₂)
        (psi : PDE.WeakTestFunction O),
      (∫ z in Set.Ioo τ₁ τ₂ ×ˢ O,
          U z * (eta.deriv z.1 * psi z.2)
          ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in Set.Ioo τ₁ τ₂ ×ˢ O,
          ((∑ i : Fin d, ∑ j : Fin d,
              reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
            (∑ j : Fin d,
              reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
            reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
            reverseTimeScalarCoefficient r₁ F z.1 z.2) *
            (eta z.1 * psi z.2)
          ∂(volume : Measure (TimeVelocity d)) := by
  intro eta psi
  let S : Set (TimeVelocity d) := Set.Ioo τ₁ τ₂ ×ˢ O
  let globalS : Set (TimeVelocity d) := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
  let μ : Measure (TimeVelocity d) := timeVelocityVolumeOn S
  let mass : TimeVelocity d → ℝ := fun z => U z * (eta.deriv z.1 * psi z.2)
  let grouped : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    G j z * (reverseTimeCoefficient r₁ a z.1 z.2 i j *
        (eta z.1 * psi.partialDeriv i z.2) +
      (eta z.1 * psi z.2) *
        (fderiv ℝ (fun y : PDE.Vec d =>
          reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i))
  let hessian : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    H z j i * (reverseTimeCoefficient r₁ a z.1 z.2 i j * (eta z.1 * psi z.2))
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z * (eta z.1 * psi z.2)
  let scalar : TimeVelocity d → ℝ := fun z =>
    reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z * (eta z.1 * psi z.2)
  let source : TimeVelocity d → ℝ := fun z =>
    reverseTimeScalarCoefficient r₁ F z.1 z.2 * (eta z.1 * psi z.2)
  have hSglobal : S ⊆ globalS := Set.prod_mono htime hOΩ
  have hGlocal (j : Fin d) : LocallyIntegrableOn (G j) S volume := by
    have hj : ParabolicMemLpOn S (2 : ℝ≥0∞) (G j) :=
      (hG j).mono_measure (Measure.restrict_mono_set volume hSglobal)
    exact hj.locallyIntegrableOn (by norm_num)
  have hHlocal (j i : Fin d) : LocallyIntegrableOn (fun z => H z j i) S volume :=
    (hHmem j i).locallyIntegrableOn (by norm_num)
  have hweighted (i j : Fin d) :=
    reverseTime_coefficient_weighted_weak_identity r₀ r₁ hO hOΩ τ₁ τ₂ htime a
      haSmooth (G j) (fun z => H z j i) (hGlocal j) (hHlocal j i) i j
      (hHweak j i) eta psi
  have hgrouped : ∀ i j : Fin d, Integrable (grouped i j) μ := by
    intro i j
    exact hweighted i j |>.1
  have hhessian : ∀ i j : Fin d, Integrable (hessian i j) μ := by
    intro i j
    exact hweighted i j |>.2.1
  have hweak : ∀ i j : Fin d,
      (∫ z, grouped i j z ∂μ) = -(∫ z, hessian i j z ∂μ) := by
    intro i j
    exact hweighted i j |>.2.2
  let etaGlobal := reverseTimeScalarTestOfLocal htime eta
  let psiGlobal := psi.mono hOΩ
  obtain ⟨hmassGlobal, hprincipalGlobal, hdriftDivGlobal, hscalarGlobal, hsourceGlobal⟩ :=
    raw_reverseTime_separated_product_families_integrable r₀ r₁ hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth U hU G hG etaGlobal psiGlobal
  have hμle : μ ≤ timeVelocityVolumeOn globalS := by
    exact Measure.restrict_mono hSglobal le_rfl
  have hmass : Integrable mass μ := by
    refine (hmassGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
    simp only [mass, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_deriv,
      PDE.WeakTestFunction.mono_apply]
    ring
  have hscalar : Integrable scalar μ := by
    refine (hscalarGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
    simp only [scalar, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
      PDE.WeakTestFunction.mono_apply]
    ring
  have hsource : Integrable source μ := by
    refine (hsourceGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
    simp only [source, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
      PDE.WeakTestFunction.mono_apply]
    ring
  have hdrift : ∀ j : Fin d, Integrable (drift j) μ := by
    intro j
    have hsumGrouped := integrable_finset_sum Finset.univ fun i _ => hgrouped i j
    have hprincipal (i : Fin d) : Integrable (fun z : TimeVelocity d =>
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2 * eta z.1) μ := by
      simpa only [etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
        PDE.WeakTestFunction.mono_partialDeriv] using
        (hprincipalGlobal i j).mono_measure hμle
    have hsumPrincipal := integrable_finset_sum Finset.univ fun i _ => hprincipal i
    have hdiv := (hdriftDivGlobal j).mono_measure hμle
    apply (hsumGrouped.sub hsumPrincipal |>.sub hdiv).congr
    filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod hO).measurableSet)] with z hz
    simp only [drift, grouped, etaGlobal, psiGlobal,
      reverseTimeScalarTestOfLocal_apply, PDE.WeakTestFunction.mono_apply,
      reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence, reverseTimeVectorCoefficient_apply, Pi.sub_apply]
    have hd : G j z * eta z.1 * psi z.2 *
          (∑ i : Fin d, (fderiv ℝ (fun y =>
            reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) =
        ∑ i : Fin d, G j z * eta z.1 * psi z.2 *
          (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) := by
      rw [Finset.mul_sum]
    ring_nf at hd ⊢
    rw [Finset.sum_add_distrib]
    rw [hd]
    ring
  have hrawAccepted :=
    reverseTime_separated_product_distribution_of_reverseTimeVariationalEnergy
      r₀ r₁ h₀₁ hΩ hΩbounded hO hOΩ τ₁ τ₂ htime a b c F haSmooth hbSmooth
      hcSmooth hFSmooth initial u g hdu hu U hU hUslice G hG hGslice eta psi
  have hraw : (∫ z, mass z -
        (∑ i : Fin d, ∑ j : Fin d, grouped i j z) +
        (∑ j : Fin d, drift j z) + scalar z - source z ∂μ) = 0 := by
    rw [← hrawAccepted.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod hO).measurableSet)] with z hz
    simp only [mass, grouped, drift, scalar, source,
      reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence, reverseTimeVectorCoefficient_apply, Pi.sub_apply]
    have hd (j : Fin d) : psi z.2 * eta z.1 *
          (∑ i : Fin d, (fderiv ℝ (fun y =>
            reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z =
        ∑ i : Fin d, psi z.2 * eta z.1 *
          (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) * G j z := by
      rw [Finset.mul_sum, Finset.sum_mul]
    ring_nf at hd ⊢
    have hdsum :
        (∑ j : Fin d, psi z.2 * eta z.1 *
            (∑ i : Fin d, (fderiv ℝ (fun y =>
              reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z) =
          ∑ j : Fin d, ∑ i : Fin d, psi z.2 * eta z.1 * G j z *
            (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
              (PDE.basisVec i) := by
      exact Finset.sum_congr rfl (fun j _ => hd j)
    ring_nf at hdsum
    rw [Finset.sum_comm] at hdsum
    have hd2 (j : Fin d) : eta z.1 *
          (∑ i : Fin d, psi z.2 *
            (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
              (PDE.basisVec i) * G j z) =
        psi z.2 * eta z.1 *
          (∑ i : Fin d, (fderiv ℝ (fun y =>
            reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z := by
      rw [Finset.mul_sum, hd j]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have houter :
        (∑ j : Fin d, eta z.1 *
            (∑ i : Fin d, psi z.2 *
              (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                (PDE.basisVec i) * G j z)) =
          ∑ j : Fin d, psi z.2 * eta z.1 *
            (∑ i : Fin d, (fderiv ℝ (fun y =>
              reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z := by
      exact Finset.sum_congr rfl (fun j _ => hd2 j)
    have hp :
        (∑ i : Fin d, ∑ j : Fin d, eta z.1 * G j z *
            reverseTimeCoefficient r₁ a z.1 z.2 i j * psi.partialDeriv i z.2) =
          ∑ i : Fin d, ∑ j : Fin d, eta z.1 *
            reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
              psi.partialDeriv i z.2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hbraw :
        (∑ j : Fin d, psi z.2 * eta z.1 * b (r₁ - z.1) z.2 j * G j z) =
          ∑ j : Fin d, psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hrhs :
        (∑ j : Fin d, eta z.1 *
            ((∑ i : Fin d, psi z.2 *
              (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                (PDE.basisVec i) * G j z) -
              psi z.2 * b (r₁ - z.1) z.2 j * G j z)) =
          (∑ j : Fin d, eta z.1 * (∑ i : Fin d, psi z.2 *
            (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
              (PDE.basisVec i) * G j z)) -
            ∑ j : Fin d, psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j := by
      calc
        _ = ∑ j : Fin d, (eta z.1 * (∑ i : Fin d, psi z.2 *
              (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                (PDE.basisVec i) * G j z) -
            psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by rw [Finset.sum_sub_distrib]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrhs]
    rw [← hdsum]
    rw [← houter]
    rw [hp, hbraw]
    ring
  have halgebra :=
    integral_mass_eq_neg_integral_hessian_add_drift_add_scalar_sub_source
      μ mass scalar source grouped hessian drift hmass hgrouped hhessian hdrift
      hscalar hsource hraw hweak
  calc
    _ = -(∫ z, (∑ i : Fin d, ∑ j : Fin d, hessian i j z) +
        (∑ j : Fin d, drift j z) + scalar z - source z ∂μ) := halgebra
    _ = _ := by
      congr 2
      funext z
      simp only [hessian, drift, scalar, source]
      have hh : (eta z.1 * psi z.2) *
            (∑ i : Fin d, ∑ j : Fin d,
              reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) =
          ∑ i : Fin d, ∑ j : Fin d,
            (eta z.1 * psi z.2) *
              (reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
        rw [Finset.mul_sum]
        congr 1
        funext i
        rw [Finset.mul_sum]
      have hb : (eta z.1 * psi z.2) *
            (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) =
          ∑ j : Fin d, (eta z.1 * psi z.2) *
            (reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) := by
        rw [Finset.mul_sum]
      have hhcomm :
          (∑ i : Fin d, ∑ j : Fin d,
            (eta z.1 * psi z.2) * H z j i *
              reverseTimeCoefficient r₁ a z.1 z.2 i j) =
          ∑ i : Fin d, ∑ j : Fin d,
            (eta z.1 * psi z.2) *
              reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      ring_nf at hh hb hhcomm ⊢
      rw [hh, hb, hhcomm]
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
