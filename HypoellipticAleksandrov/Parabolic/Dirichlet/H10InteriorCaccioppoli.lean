module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCutoffControl
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyArbitrarySolutionBound

/-! The uniform weighted interior spatial difference-quotient Caccioppoli estimate. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

private theorem integrable_norm_sq_timewise_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : H10HilbertGraph hΩ →L[ℝ] E) (u : ReverseTimeL2V hΩ T) :
    Integrable (fun τ => ‖L (u τ)‖ ^ 2) (reverseTimeVolume T) := by
  let Lu := L.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  have hLu : Lu =ᵐ[reverseTimeVolume T] fun τ => L (u τ) :=
    ContinuousLinearMap.coeFn_compLpL L u
  refine (show Integrable (fun τ => ‖Lu τ‖ ^ 2) (reverseTimeVolume T) by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) Lu Lu).congr ?_
  filter_upwards [hLu] with τ hτ
  rw [hτ]

private theorem integrable_weighted
    {T : ℝ} (ζ : ReverseTimeScalarTest T) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T)) :
    Integrable (fun τ => ζ τ * f τ) (reverseTimeVolume T) := by
  exact hf.bdd_mul ζ.contDiff.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hζunit)

private theorem integral_norm_sq_toLp
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) :
    (∫ τ, ‖u τ‖ ^ 2 ∂reverseTimeVolume T) = ‖u‖ ^ 2 := by
  have h := integral_norm_sq_eq_norm_sq_toLp (fun τ => u τ) (Lp.memLp u)
  rw [Lp.toLp_coeFn u (Lp.memLp u)] at h
  exact h

private theorem integral_weighted_const_mul
    {T a : ℝ} (ζ : ReverseTimeScalarTest T) (f : ℝ → ℝ) :
    (∫ τ, ζ τ * (a * f τ) ∂reverseTimeVolume T) =
      a * (∫ τ, ζ τ * f τ ∂reverseTimeVolume T) := by
  rw [show (fun τ : ℝ => ζ τ * (a * f τ)) =
      (fun τ => a * (ζ τ * f τ)) by funext τ; ring, integral_const_mul]

private theorem caccioppoli_scalar_closure
    {lam C K P L T U R J D S : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hbridge : (-(1 / 2 : ℝ) * D) + ((lam / 2) * J - L) ≤ S)
    (htime : (1 / 2 : ℝ) * D ≤ K * U) (hcutoff : L ≤ P * U)
    (hsource : S ≤ C * (T + U)) (hRadius : U ≤ R) :
    J ≤ (2 / lam) * (C + K + P) * (T + R) := by
  have hmain : (lam / 2) * J ≤ C * (T + U) + K * U + P * U := by
    linarith only [hbridge, htime, hcutoff, hsource]
  have hbase : U ≤ T + R := le_trans hRadius (by linarith)
  have hCU : C * (T + U) ≤ C * (T + R) :=
    mul_le_mul_of_nonneg_left (by linarith [hRadius]) hC
  have hKU : K * U ≤ K * (T + R) := mul_le_mul_of_nonneg_left hbase hK
  have hPU : P * U ≤ P * (T + R) := mul_le_mul_of_nonneg_left hbase hP
  have hscaled : (lam / 2) * J ≤ (C + K + P) * (T + R) := by
    calc
      (lam / 2) * J ≤ C * (T + U) + K * U + P * U := hmain
      _ ≤ C * (T + R) + K * (T + R) + P * (T + R) := by linarith only [hCU, hKU, hPU]
      _ = (C + K + P) * (T + R) := by ring
  calc
    J = (2 / lam) * ((lam / 2) * J) := by field_simp [ne_of_gt hlam]
    _ ≤ (2 / lam) * ((C + K + P) * (T + R)) :=
      mul_le_mul_of_nonneg_left hscaled (div_nonneg (by norm_num) hlam.le)
    _ = (2 / lam) * (C + K + P) * (T + R) := by ring

private theorem temporal_measure_radius_closure
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) {T : ℝ} (hT : 0 < T)
    (ζ : ReverseTimeScalarTest T) (Kζ lam Lam Kη C R : ℝ)
    (hlam : 0 < lam) (hKζ : 0 ≤ Kζ) (hLam : 0 ≤ Lam) (hC : 0 ≤ C)
    (u : ReverseTimeL2V hΩ T)
    (A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞))
    (hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume T))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1) (hζleOne : ∀ τ : ℝ, ζ τ ≤ 1)
    (hζderiv : ∀ τ : ℝ, |ζ.deriv τ| ≤ Kζ)
    (hValueBound : ∀ τ : ℝ,
      ‖valueCLM hΩ (A (u τ))‖ ^ 2 ≤ ‖gradientCLM hΩ (u τ)‖ ^ 2)
    (hbridge :
      -(1 / 2 : ℝ) *
          (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂reverseTimeVolume T) +
        (∫ τ, ζ τ *
            ((lam / 2) * ‖Gv τ‖ ^ 2 -
              Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
            ∂reverseTimeVolume T) ≤
          (∫ τ, ζ τ * (C * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume T))
    (hRadius : ‖u‖ ≤ R) :
    (∫ τ, ζ τ * ‖Gv τ‖ ^ 2 ∂reverseTimeVolume T) ≤
      (2 / lam) * (C + Kζ / 2 + Lam * Kη ^ 2) * (T + R ^ 2) := by
  have hVsq : Integrable (fun τ => ‖valueCLM hΩ (A (u τ))‖ ^ 2)
      (reverseTimeVolume T) := by
    exact integrable_norm_sq_timewise_apply hΩ T ((valueCLM hΩ).comp A) u
  have hGradUsq : Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume T) := by
    exact integrable_norm_sq_timewise_apply hΩ T (gradientCLM hΩ) u
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) (reverseTimeVolume T) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hUenergy := integral_norm_sq_toLp hΩ T u
  have hGradEnergy : (∫ τ, ‖gradientCLM hΩ (u τ)‖ ^ 2
      ∂reverseTimeVolume T) ≤ ‖u‖ ^ 2 := by
    rw [← hUenergy]
    apply integral_mono_ae hGradUsq hUsq
    filter_upwards with τ
    rw [norm_sq_h10HilbertGraph hΩ]
    linarith [sq_nonneg (‖valueCLM hΩ (u τ)‖)]
  have hderivInt : Integrable (fun τ => ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ)
      (reverseTimeVolume T) := by
    have hmul := hVsq.bdd_mul
      (ζ.contDiff.continuous_deriv (by norm_num)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs]
        exact hζderiv τ)
    simpa only [ReverseTimeScalarTest.deriv_apply, mul_comm] using hmul
  have htimeInt : Integrable (fun τ => (1 / 2 : ℝ) *
      (‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ)) (reverseTimeVolume T) :=
    hderivInt.const_mul (1 / 2 : ℝ)
  have htimePoint : ∀ᵐ τ ∂reverseTimeVolume T,
      (1 / 2 : ℝ) * (‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ) ≤
        (Kζ / 2) * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
    filter_upwards with τ
    have hv : 0 ≤ ‖valueCLM hΩ (A (u τ))‖ ^ 2 := sq_nonneg _
    have hd : ζ.deriv τ ≤ Kζ := (le_abs_self _).trans (hζderiv τ)
    have hmul := mul_le_mul_of_nonneg_left hd hv
    have hKg : Kζ * ‖valueCLM hΩ (A (u τ))‖ ^ 2 ≤
        Kζ * ‖gradientCLM hΩ (u τ)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hValueBound τ) hKζ
    calc
      (1 / 2 : ℝ) * (‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ) =
          (1 / 2 : ℝ) * (ζ.deriv τ * ‖valueCLM hΩ (A (u τ))‖ ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * (Kζ * ‖valueCLM hΩ (A (u τ))‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        simpa only [ReverseTimeScalarTest.deriv_apply, mul_comm] using hmul
        positivity
      _ ≤ (1 / 2 : ℝ) * (Kζ * ‖gradientCLM hΩ (u τ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hKg (by positivity)
      _ = (Kζ / 2) * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by ring
  have htime : (1 / 2 : ℝ) *
      (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂reverseTimeVolume T) ≤
        (Kζ / 2) * ‖u‖ ^ 2 := by
    calc
      (1 / 2 : ℝ) * (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume T) = ∫ τ, (1 / 2 : ℝ) *
          (‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ) ∂reverseTimeVolume T :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ τ, (Kζ / 2) * ‖gradientCLM hΩ (u τ)‖ ^ 2 ∂reverseTimeVolume T :=
        integral_mono_ae htimeInt (hGradUsq.const_mul (Kζ / 2)) htimePoint
      _ = (Kζ / 2) * ∫ τ, ‖gradientCLM hΩ (u τ)‖ ^ 2 ∂reverseTimeVolume T :=
        integral_const_mul _ _
      _ ≤ (Kζ / 2) * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hGradEnergy (by positivity)
  let Lcut : ℝ := Lam * Kη ^ 2
  have hLcut : 0 ≤ Lcut := by
    dsimp only [Lcut]
    positivity
  have hcutInt : Integrable (fun τ => ζ τ * (Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume T) :=
    integrable_weighted ζ hζunit (hGradUsq.const_mul Lcut)
  have hcutoff' : (∫ τ, ζ τ * (Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2)
      ∂reverseTimeVolume T) ≤ Lcut * ‖u‖ ^ 2 := by
    have hpoint : ∀ᵐ τ ∂reverseTimeVolume T,
        ζ τ * (Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2) ≤
          Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
      filter_upwards with τ
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hζleOne τ)
        (mul_nonneg hLcut (sq_nonneg _))
    calc
      (∫ τ, ζ τ * (Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2) ∂reverseTimeVolume T) ≤
          ∫ τ, Lcut * ‖gradientCLM hΩ (u τ)‖ ^ 2 ∂reverseTimeVolume T :=
        integral_mono_ae hcutInt (hGradUsq.const_mul Lcut) hpoint
      _ = Lcut * ∫ τ, ‖gradientCLM hΩ (u τ)‖ ^ 2 ∂reverseTimeVolume T :=
        integral_const_mul _ _
      _ ≤ Lcut * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hGradEnergy hLcut
  have hcutoff : (∫ τ, ζ τ *
      (Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ∂reverseTimeVolume T) ≤
      Lam * Kη ^ 2 * ‖u‖ ^ 2 := by
    simpa only [Lcut] using hcutoff'
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hsourceBase : Integrable (fun τ => C * (1 + ‖u τ‖ ^ 2)) (reverseTimeVolume T) := by
    simpa only [Pi.add_apply] using ((integrable_const (1 : ℝ)).add hUsq).const_mul C
  have hsourceInt : Integrable (fun τ => ζ τ * (C * (1 + ‖u τ‖ ^ 2)))
      (reverseTimeVolume T) := integrable_weighted ζ hζunit hsourceBase
  have hsource : (∫ τ, ζ τ * (C * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume T) ≤
      C * (T + ‖u‖ ^ 2) := by
    have hpoint : ∀ᵐ τ ∂reverseTimeVolume T,
        ζ τ * (C * (1 + ‖u τ‖ ^ 2)) ≤ C * (1 + ‖u τ‖ ^ 2) := by
      filter_upwards with τ
      have hbase : 0 ≤ C * (1 + ‖u τ‖ ^ 2) := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hζleOne τ) hbase
    calc
      (∫ τ, ζ τ * (C * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume T) ≤
          ∫ τ, C * (1 + ‖u τ‖ ^ 2) ∂reverseTimeVolume T :=
        integral_mono_ae hsourceInt hsourceBase hpoint
      _ = C * (T + ‖u‖ ^ 2) := by
        rw [show (fun τ : ℝ => C * (1 + ‖u τ‖ ^ 2)) =
            (fun τ => C * 1 + C * ‖u τ‖ ^ 2) by funext τ; ring,
          integral_add (integrable_const _) (hUsq.const_mul C), integral_const, smul_eq_mul,
          reverseTimeVolume_real_univ _ hT, integral_const_mul, hUenergy]
        ring
  have hhalfInt : Integrable (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume T) := integrable_weighted ζ hζunit (hGsq.const_mul (lam / 2))
  have hbulk : (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
      Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ∂reverseTimeVolume T) =
      (lam / 2) * (∫ τ, ζ τ * ‖Gv τ‖ ^ 2 ∂reverseTimeVolume T) -
      ∫ τ, ζ τ * (Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume T := by
    have hsub : (fun τ : ℝ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)) =
        (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2) -
          ζ τ * (Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)) := by
      funext τ
      ring
    rw [hsub]
    rw [integral_sub hhalfInt hcutInt]
    rw [integral_weighted_const_mul (a := lam / 2) ζ (fun τ => ‖Gv τ‖ ^ 2)]
  rw [hbulk] at hbridge
  have hRnonneg : 0 ≤ R := (norm_nonneg u).trans hRadius
  have huSq : ‖u‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hRnonneg).mpr hRadius
  exact caccioppoli_scalar_closure hlam hC (by positivity) hLcut hT.le
    hbridge htime hcutoff hsource huSq

/-- Uniform weighted interior Caccioppoli control for localized spatial difference quotients
of supplied reverse-time variational energy solutions. -/
theorem exists_uniform_interiorSpatialDifferenceQuotient_caccioppoli
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (hd : 0 < d)
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    ∃ (δ : ℝ) (hδ : 0 < δ)
        (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω),
      ∀ (Kζ : ℝ) (hKζ : 0 ≤ Kζ)
        (lam Lam M : ℝ) (hlam : 0 < lam)
        (hlamLam : lam ≤ Lam) (hM : 0 ≤ M),
        ∃ C_cac : ℝ, 0 ≤ C_cac ∧
          ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
            (hζnonneg : ∀ τ : ℝ, 0 ≤ ζ τ)
            (hζleOne : ∀ τ : ℝ, ζ τ ≤ 1)
            (hζderiv : ∀ τ : ℝ, |ζ.deriv τ| ≤ Kζ),
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
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
            (k : Fin d) (h : ℝ) (habs : 0 < |h|) (hh : |h| ≤ δ),
            let hχshift : Set.MapsTo
                (fun y : PDE.Vec d => y + h • PDE.basisVec k)
                (tsupport χ.toFun) Ω :=
              mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
                hcarrier k hh
            let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
              intro y hy
              apply subset_tsupport
              change χ y ≠ 0
              rw [χ.eq_one_on_inner y hy]
              exact one_ne_zero
            let hηshift : Set.MapsTo
                (fun y : PDE.Vec d => y + h • PDE.basisVec k)
                (tsupport η.toFun) Ω :=
              hχshift.mono_left hηχ
            let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
              localizedSpatialDifferenceQuotientH10CLM
                hΩ η k h η.tsupport_subset hηshift
            let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
              fun τ => gradientCLM hΩ (A (u τ))
            (∫ τ, ζ τ * ‖Gv τ‖ ^ 2
              ∂reverseTimeVolume (r₁ - r₀)) ≤
              C_cac *
                ((r₁ - r₀) +
                  (reverseTimeGalerkinPrimalRadius
                    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                    initial) ^ 2) := by
  have hχcompact : IsCompact (tsupport χ.toFun) := χ.hasCompactSupport
  obtain ⟨delta, hdelta, hcarrier⟩ :=
    IsCompact.exists_spatialCoordinateShiftCarrier_subset_open hχcompact hΩ χ.tsupport_subset
  refine ⟨delta, hdelta, hcarrier, ?_⟩
  intro Kζ hKζ lam Lam M hlam hlamLam hM
  obtain ⟨C_lam, hC_lam, hbridge⟩ :=
    exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_cutoffControl_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier lam hlam M hM
  refine ⟨(2 / lam) * (C_lam + Kζ / 2 + Lam * Kη ^ 2), ?_, ?_⟩
  · have hLam : 0 ≤ Lam := (le_of_lt hlam).trans hlamLam
    have hsum : 0 ≤ C_lam + Kζ / 2 + Lam * Kη ^ 2 := by positivity
    exact mul_nonneg (by positivity) hsum
  intro ζ hζnonneg hζleOne hζderiv a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hcNonpos hA hB hBD hq hqD hfD initial u g hdu hu k h habs hh
  dsimp
  let hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => gradientCLM hΩ (A (u τ))
  have hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1 := by
    intro τ
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [hζnonneg τ], hζleOne τ⟩
  have hζae : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ :=
    Filter.Eventually.of_forall hζnonneg
  have hbridge' := hbridge ζ hζunit Lam hlamLam a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hA hB hBD hq hqD hfD k h hh hζae initial u g hdu hu
  have hRadius := IsReverseTimeVariationalEnergySolution.norm_le_reverseTimeGalerkinPrimalRadius
    r₀ r₁ lam Lam h₀₁ hlam hlamLam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
      hFSmooth hLower hUpper hcNonpos initial u g hdu hu
  let R := reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  have hRadiusR : ‖u‖ ≤ R := by
    simpa only [R] using hRadius
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hValueBound : ∀ τ : ℝ,
      ‖valueCLM hΩ (A (u τ))‖ ^ 2 ≤ ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
    intro τ
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
        hΩ η k h η.tsupport_subset hηshift (u τ))
  simpa only [R, Gv, A, gradientCLM_apply] using!
    temporal_measure_radius_closure hΩ (sub_pos.mpr h₀₁) ζ Kζ lam Lam Kη C_lam R
      hlam hKζ ((le_of_lt hlam).trans hlamLam) hC_lam u A Gv hGsq hζunit hζleOne hζderiv
      hValueBound hbridge' hRadiusR

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
