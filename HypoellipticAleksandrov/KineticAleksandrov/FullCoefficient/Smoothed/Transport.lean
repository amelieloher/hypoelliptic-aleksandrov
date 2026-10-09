module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Test
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Densities
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Differentiation

/-!
# The transport term of the smoothed equation

The smoothed equation: write `v' = v - (v - v')` in the transport term of the forward
equation; the second part is the commutator of the Gaussian flow estimates at the point `y - y'`. 
Integrating
against the weights gives
`∫ v' · ∇_{z'}[η Φ_h(y - y')] dΓ' = -v·∇_z ρ + (λ h²/2) Δ_z ρ - λ h ∇_z·∇_v ρ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h τ : ℝ}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)}

theorem integrable_kernel_partial {m : Measure (EvolutionAmbientState d)} [IsFiniteMeasure m]
    (y : EvolutionAmbientState d) {G : EvolutionAmbientState d → ℝ} {C : ℝ}
    (hG : Continuous G) (hGb : ∀ w, |G w| ≤ C) :
    Integrable (fun y' => G (y - y')) m :=
  integrable_of_bounded_measurable' (hG.comp (continuous_const.sub continuous_id)).measurable
    (fun _ => hGb _)

/-- The transport integrand is the second marginal weight times a function of `y'`. -/
theorem transportDerivative_smoothingTest (hh : 0 < h) (y : EvolutionAmbientState d) (s : ℝ)
    (y' : EvolutionAmbientState d) :
    transportDerivative (smoothingTest Φ η h τ y s) y' =
      η (τ - s) * (-(∑ i, y'.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - y'))) := by
  unfold transportDerivative
  simp_rw [positionPartial_eq, coordPartial_smoothingTest Φ hh]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The transport term of the forward equation tested against the smoothing function. -/
theorem integral_transport_smoothingTest (hη : IsMollifier δ η)
    (hmarg : Γ'.map Prod.fst ≤ volume) (hh : 0 < h)
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) (y : EvolutionAmbientState d) :
    ∫ q, transportDerivative (smoothingTest Φ η h τ y q.1) q.2 ∂Γ' =
      -transportDerivative (smoothedDensity Φ η h Γ' τ) y +
        lam * h ^ 2 / 2 * positionLaplacian (smoothedDensity Φ η h Γ' τ) y -
          lam * h * mixedDivergence (smoothedDensity Φ η h Γ' τ) y := by
  have hfin := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  set ν := averagedSlice η τ Γ' with hν
  obtain ⟨C1, hC1⟩ := exists_partial_bound Φ hh
  obtain ⟨C2, hC2⟩ := exists_partial_two_bound Φ hh
  have hΦ := Φ.contDiff hh
  have hc1 : ∀ c, Continuous (coordPartial c (Φ.kernel h)) := fun c =>
    continuous_coordPartial hΦ c
  have hc2 : ∀ c c', Continuous (coordPartial c' (coordPartial c (Φ.kernel h))) := fun c c' =>
    continuous_coordPartial (contDiff_coordPartial hΦ c) c'
  have i1 : ∀ c, Integrable (fun y' => coordPartial c (Φ.kernel h) (y - y')) ν := fun c =>
    integrable_kernel_partial y (hc1 c) (hC1 c)
  have i2 : ∀ c c', Integrable (fun y' =>
      coordPartial c' (coordPartial c (Φ.kernel h)) (y - y')) ν := fun c c' =>
    integrable_kernel_partial y (hc2 c c') (hC2 c c')
  -- the integrand as `η (τ - t) * T y'`
  have hT : ∀ q : ℝ × EvolutionAmbientState d,
      transportDerivative (smoothingTest Φ η h τ y q.1) q.2 =
        η (τ - q.1) * (-(∑ i, q.2.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - q.2))) :=
    fun q => transportDerivative_smoothingTest Φ hh y q.1 q.2
  have hTm : Measurable fun y' : EvolutionAmbientState d =>
      -(∑ i, y'.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - y')) := by
    refine (Finset.measurable_sum _ fun i _ => ?_).neg
    exact ((continuous_apply i).comp continuous_fst).measurable.mul
      ((hc1 _).comp (continuous_const.sub continuous_id)).measurable
  simp_rw [hT]
  rw [← integral_averagedSlice hη hTm]
  -- pointwise decomposition of `T`
  have hdec : ∀ y' : EvolutionAmbientState d,
      -(∑ i, y'.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - y')) =
        -(∑ i, y.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - y')) +
          (lam * h ^ 2 / 2 * ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inr i) (Φ.kernel h))
              (y - y') -
            lam * h * ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inl i) (Φ.kernel h))
              (y - y')) := fun y' => by
    have := hcomm (y - y')
    simp only [transportDerivative, positionLaplacian, mixedDivergence, positionPartial_eq,
      velocityPartial_eq] at this
    rw [← this]
    have e : ∀ i, (y - y').1 i = y.1 i - y'.1 i := fun i => rfl
    simp_rw [e, sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  simp_rw [hdec]
  have e1 : ∫ y', -(∑ i, y.1 i * coordPartial (Sum.inr i) (Φ.kernel h) (y - y')) ∂ν =
      -transportDerivative (smoothedDensity Φ η h Γ' τ) y := by
    rw [integral_neg, integral_finsetSum _ fun i _ => (i1 _).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    congr 1
    exact (coordPartial_smoothDensity Φ ν hh (Sum.inr i) y).symm
  have e2 : ∫ y', lam * h ^ 2 / 2 * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inr i) (Φ.kernel h)) (y - y') ∂ν =
      lam * h ^ 2 / 2 * positionLaplacian (smoothedDensity Φ η h Γ' τ) y := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => i2 _ _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (coordPartial₂_smoothDensity Φ ν hh (Sum.inr i) (Sum.inr i) y).symm
  have e3 : ∫ y', lam * h * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inl i) (Φ.kernel h)) (y - y') ∂ν =
      lam * h * mixedDivergence (smoothedDensity Φ η h Γ' τ) y := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => i2 _ _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (coordPartial₂_smoothDensity Φ ν hh (Sum.inl i) (Sum.inr i) y).symm
  rw [integral_add, integral_sub, e1, e2, e3]
  · ring
  · exact (integrable_finsetSum _ fun i _ => i2 _ _).const_mul _
  · exact (integrable_finsetSum _ fun i _ => i2 _ _).const_mul _
  · exact (integrable_finsetSum _ fun i _ => (i1 _).const_mul _).neg
  · exact ((integrable_finsetSum _ fun i _ => i2 _ _).const_mul _).sub
      ((integrable_finsetSum _ fun i _ => i2 _ _).const_mul _)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
