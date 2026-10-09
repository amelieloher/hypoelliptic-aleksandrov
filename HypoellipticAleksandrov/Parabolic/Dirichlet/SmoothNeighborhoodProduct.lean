module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness

/-!
# Products with locally smooth coefficients

This module promotes smoothness near a prescribed set to global smoothness
after multiplication by a globally smooth function supported in that set.
-/

@[expose] public section

open Filter Set Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem contDiff_mul_of_contDiffOn_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {V : Set E}
    (hV : IsOpen V) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsub : tsupport g ⊆ V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact (hf.contDiffAt (hV.mem_nhds hx)).mul hg.contDiffAt
  · have hxt : x ∉ tsupport g := fun h => hx (hsub h)
    have heg : g =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [heg] with y hy
    rw [hy]
    simp only [Pi.zero_apply, mul_zero]

/-- Multiplying a function smooth near a set by a globally smooth function
supported in that set produces a globally smooth function. -/
theorem IsSmoothOnNeighborhood.contDiff_mul_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {K : Set E}
    (hf : IsSmoothOnNeighborhood f K) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsub : tsupport g ⊆ K) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * g x) := by
  rcases hf with ⟨V, hV, hKV, hfV⟩
  exact contDiff_mul_of_contDiffOn_of_tsupport_subset hV hfV hg
    (hsub.trans hKV)

end HypoellipticAleksandrov.Parabolic.Dirichlet
