module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit

/-! # Terminal-layer weak identities for full kinetic source slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ}

/-- Testing a classical kinetic slice with the terminal-layer cutoff gives its weak identity. -/
theorem kinetic_slice_cutoff_identity {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (EvolutionVec d)} (hD : IsOpen D) {V u : EvolutionVec d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, transportedOperator B b V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u)
    (C : ℝ) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (h : ℝ) (hh : 0 < h) :
    (∫ x, u x * (layerStep ((r - timeCoord d x) / h) * transportedAdjoint B b ψ x)) +
      ∫ x, u x * (h⁻¹ * layerKernel ((r - timeCoord d x) / h) * ψ x) = 0 := by
  set Ladj := transportedAdjoint B b with hLadj
  have hU : IsOpen D := hD
  have hχ := contDiff_sliceCutoff r h
  let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
  have hφc : HasCompactSupport φ := hc.mul_left
  have hφsub : tsupport φ ⊆ D := by
    intro x hx
    have h1 : x ∈ tsupport ψ := tsupport_mul_subset_right hx
    have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
      apply closure_minimal
      · intro y hy
        have hy1 : sliceCutoff r h (Evolution.timeCoord d y) ≠ 0 := left_ne_zero_of_mul hy
        exact (lt_of_sliceCutoff_ne_zero hh hy1).le
      · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
    exact hψD x h1 (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
  have key := integral_transportedAdjoint_contDiffOn hD hB hBs hb hV φ hφs hφc hφsub
  have hR : (∫ x in D, transportedOperator B b V x * φ x) = 0 := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      simp only [hVeq _ hx, zero_mul]
  rw [hR] at key
  have hL : (∫ x in D, V x * Ladj φ x) = ∫ x, u x * Ladj φ x := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => u x * Ladj φ x)]
    · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : x ∉ tsupport φ := fun h' => hx (hφsub h')
      rw [hLadj, transportedAdjoint_eq_zero_of_notMem_tsupport φ this, mul_zero]
    · intro x hx
      simp only [huV _ hx]
  rw [hL] at key
  have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
      h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
    intro x
    simp only [hLadj, φ]
    rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
    ring
  simp_rw [hexp, mul_add] at key
  have hLc : Continuous (Ladj ψ) := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
  have hmeasu : Measurable (fun x => u x) := hum
  have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u x‖ ≤ C :=
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hub x
  have i1 : Integrable (fun x => u x * (sliceCutoff r h (Evolution.timeCoord d x) *
      Ladj ψ x)) := by
    have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
      ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul hLc
        ).integrable_of_hasCompactSupport hLcs.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  have i2 : Integrable (fun x => u x * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
      * ψ x)) := by
    have hk : Continuous (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      (continuous_const.mul (continuous_layerKernel.comp
        ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
    have : Integrable (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      hk.integrable_of_hasCompactSupport hc.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  exact (integral_add i1 i2).symm.trans key

/-- Passing the kinetic cutoff identity to the limit retains the terminal source term. -/
theorem kinetic_slice_weak_identity {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (EvolutionVec d)} (hD : IsOpen D) {V u : EvolutionVec d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, transportedOperator B b V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u)
    (C : ℝ) (hC0 : 0 ≤ C) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (m₀ : EvolutionAmbientState d → ℝ)
    (hlim : ∀ w, Tendsto (fun t => u (packQ d (t, w)) * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × EvolutionAmbientState d,
      {q : ℝ × EvolutionAmbientState d | q.1 < r}.indicator
        (fun q => u (packQ d q) * transportedAdjoint B b ψ (packQ d q)) q) +
      ∫ w, m₀ w = 0 := by
  have hLc := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs := hasCompactSupport_transportedAdjoint (B := B) (b := b) hc
  refine layer_slice_identity (volume : Measure (EvolutionAmbientState d)) r
    (fun q => u (packQ d q)) (fun q => ψ (packQ d q))
    (fun q => transportedAdjoint B b ψ (packQ d q))
    (hum.comp continuous_packQ.measurable) C hC0 (fun q => hub _)
    (hψ.continuous.comp continuous_packQ) (hasCompactSupport_comp_packQ hc)
    (hLc.comp continuous_packQ) (hasCompactSupport_comp_packQ hLcs) ?_ m₀ hlim
  intro h hh
  have h1 := kinetic_slice_cutoff_identity hB hBs hb hD hV hVeq huV hum C hub
    hψ hc r hψD h hh
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h1
  simp only [timeCoord_packQ] at h1
  rw [← h1]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
