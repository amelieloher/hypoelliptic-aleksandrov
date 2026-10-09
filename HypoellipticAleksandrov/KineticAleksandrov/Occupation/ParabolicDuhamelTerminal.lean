module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelContinuity

/-!
# The terminal trace of a source slice against a test function

For a test `ψ` supported in `{(σ,v,z) : σ < T, v ∈ Ω_σ}`, the left limit at `σ = r` of
`u_r(σ, v) ψ(σ, v, z)` is `g(r, v) ψ(r, v, z)`, where `u_r` is the zero-extended slice integrand.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- The slice integrand has the terminal value `g(r,v)` as a left limit at interior points. -/
theorem slice_leftLimit {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) (v : PDE.Vec d)
    (hv : (r, v) ∈ duhamelFiber Ω γ T) :
    Tendsto (fun t : ℝ => parabolicDuhamelIntegrand K
        (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g (t, v) r) (𝓝[<] r)
      (𝓝 (g (r, v))) := by
  obtain ⟨V, -, hVc, -, -, hterm, hVeq⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
  have hU := isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hcl : (r, v) ∈ sliceClosedCylinder Ω γ r := ⟨le_rfl, subset_closure hv.2⟩
  have hev : ∀ᶠ t in 𝓝[<] r, (t, v) ∈ sliceClosedCylinder Ω γ r := by
    have hn : ∀ᶠ t in 𝓝 r, (t, v) ∈ duhamelFiber Ω γ T :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds hv)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht2
    exact ⟨le_of_lt ht2, subset_closure ht.2⟩
  have hcw : ContinuousWithinAt V (sliceClosedCylinder Ω γ r) (r, v) := hVc _ hcl
  have hmap : Tendsto (fun t : ℝ => (t, v)) (𝓝[<] r) (𝓝[sliceClosedCylinder Ω γ r] (r, v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hev⟩
    exact ((continuous_id.prodMk continuous_const).tendsto r).mono_left nhdsWithin_le_nhds
  have h1 := hcw.tendsto.comp hmap
  rw [hterm v (hcl.2)] at h1
  refine h1.congr' ?_
  filter_upwards [hev] with t ht
  exact (hVeq (t, v) ht).symm

/-- The left limit of `u_r ψ` at `σ = r` is `g(r,v) ψ(r,v,z)`. -/
theorem slice_terminal_limit {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (C : ℝ)
    (hub : ∀ p r, |parabolicDuhamelIntegrand K
        (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g p r| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : Continuous ψ)
    (hψs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' duhamelFiber Ω γ T)
    (r : ℝ) (w : PDE.Vec d × PDE.Vec d) :
    Tendsto (fun t : ℝ => parabolicDuhamelIntegrand K
        (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g (t, w.1) r * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (g (r, w.1) * ψ (packQ d (r, w)))) := by
  have hψt : Tendsto (fun t : ℝ => ψ (packQ d (t, w))) (𝓝[<] r) (𝓝 (ψ (packQ d (r, w)))) :=
    ((hψ.comp (continuous_packQ.comp (continuous_id.prodMk continuous_const))).tendsto r).mono_left
      nhdsWithin_le_nhds
  by_cases h0 : ψ (packQ d (r, w)) = 0
  · rw [h0, mul_zero]
    have hb : Tendsto (fun t : ℝ => C * |ψ (packQ d (t, w))|) (𝓝[<] r) (𝓝 0) := by
      have := (hψt.abs).const_mul C
      simpa [h0] using this
    refine squeeze_zero_norm (fun t => ?_) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hub _ _) (abs_nonneg _)
  · have hsupp : packQ d (r, w) ∈ tsupport ψ := subset_closure h0
    have hfib := hψs hsupp
    have hv : (r, w.1) ∈ duhamelFiber Ω γ T := by
      simpa only [mem_preimage, evolutionToTimeVelocity_packQ] using hfib
    exact (slice_leftLimit K hΩa hγ hP g hgs hgc T hgU r w.1 hv).mul hψt

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
