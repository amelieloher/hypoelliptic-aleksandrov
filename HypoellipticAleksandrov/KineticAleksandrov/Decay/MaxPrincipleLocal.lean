module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleGeometry

/-!
# One-sided time calculus at a moving-tube maximum

The fixed diffused coordinate remains inside the moving domain for nearby
times by continuity. No derivative of the boundary curve is required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/-- The transported operator is nonpositive at a tube maximum strictly before
terminal time, with differentiability only in the slices required by the source. -/
theorem transportedForwardOperator_nonpos_at_tube_max {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b : ℝ}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hΩ : IsOpen Ω) (hγ : ContinuousAt γ p.time)
    (ht : p.time ∈ Ico a b) (hv : p.position ∈ movingDomain Ω γ p.time)
    (hmax : IsMaxOn u (maximumClosedTube Ω γ a b) p)
    (hut : DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time)
    (huv : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (huz : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : (B p.time p.position p.velocity).PosSemidef) :
    transportedForwardOperator B drift u p ≤ 0 := by
  have hvmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position := by
    filter_upwards [(isOpen_movingDomain hΩ p.time).mem_nhds hv] with y hy
    exact hmax ⟨⟨ht.1, ht.2.le⟩, subset_closure hy⟩
  have hzmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity := by
    exact Filter.Eventually.of_forall (fun z =>
      hmax ⟨⟨ht.1, ht.2.le⟩, subset_closure hv⟩)
  have hmove : ∀ᶠ t in 𝓝 p.time, p.position ∈ movingDomain Ω γ t := by
    have hsub : p.position - γ p.time ∈ Ω :=
      (PDE.mem_translateSet_iff_sub_mem).mp hv
    have hevent := (continuousAt_const.sub hγ) (hΩ.mem_nhds hsub)
    simp only [Filter.mem_map] at hevent
    filter_upwards [hevent] with t ht
    exact PDE.mem_translateSet_iff_sub_mem.mpr ht
  have htmax : IsLocalMaxOn (fun t => u ⟨t, p.position, p.velocity⟩)
      (Icc a b) p.time := by
    filter_upwards [hmove.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t htm hti
    exact hmax ⟨hti, subset_closure htm⟩
  have hdir : b - p.time ∈ posTangentConeAt (Icc a b) p.time := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    intro t hti
    exact ⟨le_trans ht.1 (segment_subset_Icc (𝕜 := ℝ) ht.2.le hti).1,
      (segment_subset_Icc (𝕜 := ℝ) ht.2.le hti).2⟩
  have htprod := htmax.hasFDerivWithinAt_nonpos hut.hasDerivAt.hasFDerivAt.hasFDerivWithinAt hdir
  have htime : kineticTimeDerivative u p ≤ 0 := by
    have hproduct : (b - p.time) * kineticTimeDerivative u p ≤ 0 := by
      simpa only [kineticTimeDerivative, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul] using htprod
    exact nonpos_of_mul_nonpos_right hproduct (sub_pos.mpr ht.2)
  exact transportedForwardOperator_nonpos_of_slice_localMax htime huv huz hvmax hzmax hB

end HypoellipticAleksandrov.KineticAleksandrov.Decay
