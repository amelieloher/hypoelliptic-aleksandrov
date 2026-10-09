module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockBoundary
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Closed top-face and adjacent-block geometry -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set Filter
open scoped Topology

/-- Interior spatial coordinates and the closed terminal time belong to the cylinder closure. -/
theorem mem_closure_backwardCylinder_of_strict_spatial {d : ℕ}
    (P₀ P : KineticPoint d) {R : ℝ} (_hR : 0 < R)
    (htlo : P₀.time - R ^ 2 < P.time) (htup : P.time ≤ P₀.time)
    (hv : P.velocity ∈ PDE.euclideanBall P₀.velocity R)
    (hx : relativePosition P₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3)) :
    P ∈ closure (backwardCylinder P₀ R) := by
  by_cases ht : P.time < P₀.time
  · exact subset_closure ⟨htlo, ht, hv, hx⟩
  have heq : P.time = P₀.time := le_antisymm htup (le_of_not_gt ht)
  let f : ℝ → KineticPoint d := fun r =>
    ⟨P.time + r, P.position + r • P₀.velocity, P.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk
    (continuous_const.add continuous_id)
    (continuous_const.add (continuous_id.smul continuous_const)) continuous_const
  have hf0 : f 0 = P := by simp [f]
  have hlimit : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 P) :=
    hf0 ▸ hf.continuousAt.tendsto.mono_left inf_le_left
  apply mem_closure_of_tendsto hlimit
  have hcont : ContinuousAt (fun r : ℝ => P.time + r) 0 :=
    continuousAt_const.add continuousAt_id
  have hlow : ∀ᶠ r in 𝓝[<] (0 : ℝ), P₀.time - R ^ 2 < P.time + r :=
    hcont.eventually
      (lt_mem_nhds (by simpa only [add_zero] using htlo)) |>.filter_mono inf_le_left
  filter_upwards [hlow, self_mem_nhdsWithin] with r hr hneg
  refine ⟨hr, ?_, hv, ?_⟩
  · change P.time + r < P₀.time
    rw [heq]
    change r < 0 at hneg
    linarith only [hneg]
  · have hrel : relativePosition P₀ (f r) = relativePosition P₀ P := by
      ext i
      simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simpa only [hrel] using hx

end HypoellipticAleksandrov.KineticAleksandrov.Holder
