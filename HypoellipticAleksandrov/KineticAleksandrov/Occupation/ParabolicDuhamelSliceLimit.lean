module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayerLimit

/-!
# The weak identity of one source slice, with its terminal boundary term

Passing to the limit `h ↓ 0` in the cut-off identity of `ParabolicDuhamelSliceWeak` (the
terminal-layer limit of `ParabolicDuhamelLayerLimit`) gives, for the bounded Borel extension `u`
of the slice solution,
`∫_{σ < r} u Lop^* ψ + ∫ g(r,·) ψ(r,·) = 0`, in the product coordinates `(σ, (v, z))`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- Packing product coordinates `(σ, (v, z))` into the packed evolution space. -/
def packQ (d : ℕ) (q : ℝ × (PDE.Vec d × PDE.Vec d)) : EvolutionVec d :=
  packPoint q.1 q.2.1 q.2.2

@[simp] theorem timeCoord_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    Evolution.timeCoord d (packQ d q) = q.1 := timeCoord_packPoint _ _ _

@[simp] theorem diffusedCoord_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    diffusedCoord d (packQ d q) = q.2.1 := diffusedCoord_packPoint _ _ _

@[simp] theorem evolutionToTimeVelocity_packQ (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    evolutionToTimeVelocity d (packQ d q) = (q.1, q.2.1) :=
  Prod.ext (timeCoord_packQ q) (diffusedCoord_packQ q)

theorem packQ_eq_symm (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    packQ d q = (evolutionProdMeasurableEquiv d).symm q := by
  rw [MeasurableEquiv.eq_symm_apply, evolutionProdMeasurableEquiv_apply]
  simp [packQ]

theorem continuous_packQ : Continuous (packQ d) := by
  have : packQ d = (evolutionProdCLE d).symm := by
    funext q; rfl
  rw [this]
  exact (evolutionProdCLE d).symm.continuous

/-- Integrals over the packed space are integrals over product coordinates. -/
theorem integral_evolution_eq_prod (F : EvolutionVec d → ℝ) :
    ∫ x, F x = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F (packQ d q) := by
  have h := (measurePreserving_evolutionProdMeasurableEquiv (n := d)).integral_comp'
    (fun q => F ((evolutionProdMeasurableEquiv d).symm q))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [h]
  simp only [← packQ_eq_symm]

theorem hasCompactSupport_comp_packQ {f : EvolutionVec d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun q => f (packQ d q)) := by
  have : (fun q => f (packQ d q)) = f ∘ (evolutionProdCLE d).symm.toHomeomorph := by
    funext q; rfl
  rw [this]
  exact hf.comp_homeomorph _

/-- **The weak identity of one source slice.**  In product coordinates the integral of the bounded
Borel extension `u` of the slice solution against `Lop^* ψ` over the slab `σ < r` equals minus the
terminal boundary term `∫ m₀`, where `m₀` is the left limit of `u ψ` at `σ = r`. -/
theorem slice_weak_identity {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {V u : TimeVelocity d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, scalarParabolicOperator B' (fun _ _ => 0) V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u) (C : ℝ) (hC0 : 0 ≤ C)
    (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, Evolution.timeCoord d x < r →
      evolutionToTimeVelocity d x ∈ D)
    (m₀ : PDE.Vec d × PDE.Vec d → ℝ)
    (hlim : ∀ w : PDE.Vec d × PDE.Vec d,
      Tendsto (fun t => u (t, w.1) * ψ (packQ d (t, w))) (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × (PDE.Vec d × PDE.Vec d), {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => u (q.1, q.2.1) *
          transportedAdjoint (zIndependentCoefficient B') b ψ (packQ d q)) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, m₀ w = 0 := by
  have hLc : Continuous (transportedAdjoint (zIndependentCoefficient B') b ψ) :=
    (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs := hasCompactSupport_transportedAdjoint (B := zIndependentCoefficient B') (b := b) hc
  refine layer_slice_identity (volume : Measure (PDE.Vec d × PDE.Vec d)) r
    (fun q => u (q.1, q.2.1)) (fun q => ψ (packQ d q))
    (fun q => transportedAdjoint (zIndependentCoefficient B') b ψ (packQ d q))
    (hum.comp (measurable_fst.prodMk (measurable_snd.fst))) C hC0 (fun q => hub _)
    (hψ.continuous.comp continuous_packQ) (hasCompactSupport_comp_packQ hc)
    (hLc.comp continuous_packQ) (hasCompactSupport_comp_packQ hLcs) ?_ m₀ hlim
  intro h hh
  have h1 := slice_cutoff_identity hB hb hD hV hVeq huV hum C hub hψ hc r hψD h hh
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h1
  simp only [evolutionToTimeVelocity_packQ, timeCoord_packQ] at h1
  rw [← h1]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
