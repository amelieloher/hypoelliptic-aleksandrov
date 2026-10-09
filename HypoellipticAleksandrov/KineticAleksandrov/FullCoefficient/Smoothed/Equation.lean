module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Transport
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Datum
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Smooth
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Admissible

/-!
# The smoothed equation

The smoothed equation: for `τ` with `[τ - δ, τ + δ] ⊂ (0, T)` and all
`y`,
`∂_τ ρ + v·∇_z ρ = (λ h²/2) Δ_z ρ - λ h ∇_z·∇_v ρ + ∑_{ij} ∂_{v_i} ∂_{v_j} J_{ij}`.
The forward equation is taken in the abstract form `IsForwardMeasure` (proved for the Green
measure in `Smoothed/Green.lean`), and the commutator property of the Gaussian flow as a hypothesis
on the
kernel (proved for the flow kernel there).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped MatrixOrder

variable {d : ℕ}

/-- The forward equation `∫ (∂_s φ + B : D_v² φ + v·∇_z φ) dΓ' = 0` for all admissible `φ`, for a
measure `Γ'` on `ℝ × ℝ^{2d}`. -/
def IsForwardMeasure (T : ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) : Prop :=
  ∀ φ : ℝ → EvolutionAmbientState d → ℝ, IsAdmissibleTest T φ →
    Integrable (fun q : ℝ × EvolutionAmbientState d => deriv (fun s => φ s q.2) q.1) Γ' ∧
    Integrable (fun q : ℝ × EvolutionAmbientState d =>
      velocityHessianContraction (Bt q.1 q.2) (φ q.1) q.2) Γ' ∧
    Integrable (fun q : ℝ × EvolutionAmbientState d => transportDerivative (φ q.1) q.2) Γ' ∧
    ∫ q, (deriv (fun s => φ s q.2) q.1 + velocityHessianContraction (Bt q.1 q.2) (φ q.1) q.2 +
      transportDerivative (φ q.1) q.2) ∂Γ' = 0

variable {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h τ T : ℝ}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)} {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- The diffusion term of the forward equation tested against the smoothing function. -/
theorem integral_hessian_smoothingTest (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') (hh : 0 < h) (y : EvolutionAmbientState d) :
    ∫ q, velocityHessianContraction (Bt q.1 q.2) (smoothingTest Φ η h τ y q.1) q.2 ∂Γ' =
      ∑ i, ∑ j, velocityPartial i (velocityPartial j
        (fun y => smoothedFlux Φ η Bt Lam h Γ' τ y i j)) y := by
  have := hD.finite
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hD.marginal
  have hLam := hD.lam_nonneg_Lam
  have hBb := hD.abs_apply_le
  have hcoef := isAdmissibleCoefficient_averagedCoefficient (η := η) (τ := τ) (Γ' := Γ')
    hD.symm hD.loewner
  obtain ⟨C2, hC2⟩ := exists_partial_two_bound Φ hh
  have hc2 : ∀ c c', Continuous (coordPartial c' (coordPartial c (Φ.kernel h))) := fun c c' =>
    continuous_coordPartial (contDiff_coordPartial (Φ.contDiff hh) c) c'
  have hmeas : ∀ i j, Measurable fun y' : EvolutionAmbientState d =>
      coordPartial (Sum.inl i) (coordPartial (Sum.inl j) (Φ.kernel h)) (y - y') := fun i j =>
    ((hc2 _ _).comp (continuous_const.sub continuous_id)).measurable
  have hb : ∀ i j (y' : EvolutionAmbientState d),
      |coordPartial (Sum.inl i) (coordPartial (Sum.inl j) (Φ.kernel h)) (y - y')| ≤ C2 :=
    fun i j y' => hC2 _ _ _
  have hpt : ∀ q : ℝ × EvolutionAmbientState d,
      velocityHessianContraction (Bt q.1 q.2) (smoothingTest Φ η h τ y q.1) q.2 =
        ∑ i, ∑ j, η (τ - q.1) * Bt q.1 q.2 i j *
          coordPartial (Sum.inl i) (coordPartial (Sum.inl j) (Φ.kernel h)) (y - q.2) := fun q => by
    unfold velocityHessianContraction
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [velocityPartial_eq, velocityPartial_eq, coordPartial₂_smoothingTest Φ hh]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_fluxIntegrand hη hD.measurable hBb i j (hmeas i j) (hb i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    integrable_fluxIntegrand hη hD.measurable hBb i j (hmeas i j) (hb i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_mul_averagedCoefficient hη hD.marginal hD.measurable hBb hLam hD.loewner i j
    (hmeas i j) (hb i j)]
  have := coordPartial₂_smoothFluxEntry Φ (averagedSlice η τ Γ') hD.lam_pos hcoef hh i j
    (Sum.inl j) (Sum.inl i) y
  rw [velocityPartial_eq, velocityPartial_eq]
  refine Eq.trans ?_ this.symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
  simp only [mul_comm]

/-- **The smoothed equation**.  For `τ` with
`[τ - δ, τ + δ] ⊂ (0, T)` and every `y`,
`∂_τ ρ + v·∇_z ρ = (λ h²/2) Δ_z ρ - λ h ∇_z·∇_v ρ + ∑_{ij} ∂_{v_i} ∂_{v_j} J_{ij}`. -/
theorem smoothed_equation (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hδ : 0 < δ) (hτ : δ < τ) (hτT : τ + δ < T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) (y : EvolutionAmbientState d) :
    deriv (fun τ' => smoothedDensity Φ η h Γ' τ' y) τ +
        transportDerivative (smoothedDensity Φ η h Γ' τ) y =
      lam * h ^ 2 / 2 * positionLaplacian (smoothedDensity Φ η h Γ' τ) y -
        lam * h * mixedDivergence (smoothedDensity Φ η h Γ' τ) y +
        ∑ i, ∑ j, velocityPartial i (velocityPartial j
          (fun y => smoothedFlux Φ η Bt Lam h Γ' τ y i j)) y := by
  have := hD.finite
  obtain ⟨hi1, hi2, hi3, hint⟩ := hfwd _ (isAdmissibleTest_smoothingTest Φ hη hh hδ hτ hτT y)
  have e1 := integral_add hi1 hi2
  have e2 := integral_add (hi1.add hi2) hi3
  simp only [Pi.add_apply] at e1 e2
  rw [e2, e1] at hint
  have h1 : ∫ q, deriv (fun s => smoothingTest Φ η h τ y s q.2) q.1 ∂Γ' =
      -deriv (fun τ' => smoothedDensity Φ η h Γ' τ' y) τ := by
    rw [(hasDerivAt_smoothedDensity Φ hη hh τ y (Γ' := Γ')).deriv, ← integral_neg]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun q => deriv_smoothingTest Φ hη y q.2 q.1)
  rw [h1, integral_hessian_smoothingTest Φ hη hD hh y,
    integral_transport_smoothingTest Φ hη hD.marginal hh hcomm y] at hint
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
