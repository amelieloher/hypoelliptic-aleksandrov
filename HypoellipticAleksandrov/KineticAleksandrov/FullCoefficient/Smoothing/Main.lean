module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Differentiation
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Uniform
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Flux
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FlowInstance
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Joint
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.HDeriv
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.IntegrationByParts

/-!
# Smoothing of finite measures: facade

The smoothing operation and the smoothing estimates. The statements are
proved for an arbitrary `SmoothingKernelFamily` (`Smoothing/Kernel`) and specialised to the Gaussian
flow kernel by `flowKernelFamily`.

* (i) smoothness and differentiation under the integral, heat equation: `contDiff_smoothDensity`,
  `contDiff_smoothFluxEntry`, `coordPartial_smoothDensity`, `coordPartial₂_smoothDensity`,
  `coordPartial_smoothFluxEntry`, `coordPartial₂_smoothFluxEntry`, `hasDerivAt_smoothDensity`,
  `hasDerivAt_smoothFluxEntry`, `heatOperator_smoothDensity`, `heatOperator_smoothFluxEntry`.
* (ii) positivity dichotomy, sup and `L¹` bounds, Loewner bounds, `|β|² ≤ dΛ²`:
  `smoothDensity_zero`, `smoothDensity_pos`, `smoothDensity_le`, `integral_smoothDensity`,
  `isSymm_smoothCoefficient`, `smoothCoefficient_loewner`, `frobeniusSq_smoothCoefficient_le`.
* (iii) Fisher-type bounds: `gradNormSq_smoothDensity_div_le`,
  `density_mul_coefficientGradNormSq_le`.
* (iv) integrability list and `W^{2,1}` membership: `PackageIntegrable`,
  `packageIntegrable_of_ne_zero`, `smoothW21_of_packageIntegrable`.
* (v) uniformity: `package_uniform`.
* Joint continuity: `continuousOn_smoothDensity_joint`, `continuousOn_smoothFluxEntry_joint`.
* `h`-differentiation of `∫ r^q`, `∫ r^q|β|²`: `hasDerivAt_integral_rpow_density`,
  `hasDerivAt_integral_powBeta`, `integral_rpow_density_sub`, `integral_powBeta_sub`,
  dominator `exists_heat_dominator`.
* Integration by parts: `integral_mul_coordPartial_eq_neg`, `integral_coordPartial_eq_zero`,
  `SmoothW21.integral_coordPartial`, `SmoothW21.integral_coordPartial₂`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

/-- The smoothing estimates for the Gaussian flow kernel: uniform integrability of the ten
integrands
over finite measures of mass at most `M` and `h` in a compact subset of `(0, ∞)`. -/
theorem flow_package_uniform {d : ℕ} {lam Lam q : ℝ} (hl : 0 < lam) (hLam : lam ≤ Lam)
    (hq : 1 < q) {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ (m : Measure (EvolutionAmbientState d)), IsFiniteMeasure m →
      m.real Set.univ ≤ M → ∀ F : EvolutionAmbientState d → PDE.Mat d,
        IsAdmissibleCoefficient lam Lam F → PackageIntegrable (flowKernelFamily hl) h F m q C :=
  package_uniform (flowKernelFamily hl) hl hLam hq hK hsub hM

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
