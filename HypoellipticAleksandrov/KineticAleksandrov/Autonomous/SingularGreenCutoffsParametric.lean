module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # C² parameter integration with integrable jet bounds and a null exceptional set -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology

/-- Dominated C² jets give actual C² regularity of their parameter integral. -/
theorem singular_parameter_integral_contDiffOn_two
    {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace A] (mu : Measure A)
    {U : Set E} (hU : IsOpen U)
    (f : E → A → F) (f' : E → A → E →L[ℝ] F)
    (f'' : E → A → E →L[ℝ] (E →L[ℝ] F))
    (b0 b1 b2 : A → ℝ) (hb0 : Integrable b0 mu) (hb1 : Integrable b1 mu)
    (hb2 : Integrable b2 mu)
    (hm0 : ∀ x ∈ U, AEStronglyMeasurable (f x) mu)
    (hm1 : ∀ x ∈ U, AEStronglyMeasurable (f' x) mu)
    (hm2 : ∀ x ∈ U, AEStronglyMeasurable (f'' x) mu)
    (hn0 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f x a‖ ≤ b0 a)
    (hn1 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f' x a‖ ≤ b1 a)
    (hn2 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f'' x a‖ ≤ b2 a)
    (hd0 : ∀ᵐ a ∂mu, ∀ x ∈ U, HasFDerivAt (fun y => f y a) (f' x a) x)
    (hd1 : ∀ᵐ a ∂mu, ∀ x ∈ U, HasFDerivAt (fun y => f' y a) (f'' x a) x)
    (hc2 : ∀ᵐ a ∂mu, ContinuousOn (fun x => f'' x a) U) :
    ContDiffOn ℝ 2 (fun x => ∫ a, f x a ∂mu) U ∧
      (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, f y a ∂mu) (∫ a, f' x a ∂mu) x) ∧
      (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, f' y a ∂mu) (∫ a, f'' x a ∂mu) x) := by
  have hi0 x (hx : x ∈ U) : Integrable (f x) mu :=
    hb0.mono' (hm0 x hx) (hn0.mono (fun a ha => ha x hx))
  have hi1 x (hx : x ∈ U) : Integrable (f' x) mu :=
    hb1.mono' (hm1 x hx) (hn1.mono (fun a ha => ha x hx))
  have hd0I x (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ a, f y a ∂mu) (∫ a, f' x a ∂mu) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hx)
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm0 y hy
    · exact hi0 x hx
    · exact hm1 x hx
    · exact hn1
    · exact hb1
    · exact hd0
  have hd1I x (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ a, f' y a ∂mu) (∫ a, f'' x a ∂mu) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hx)
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm1 y hy
    · exact hi1 x hx
    · exact hm2 x hx
    · exact hn2
    · exact hb2
    · exact hd1
  have hcI : ContinuousOn (fun x => ∫ a, f'' x a ∂mu) U := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm2 y hy
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hn2.mono (fun a ha => ha y hy)
    · exact hb2
    · exact hc2.mono (fun a ha => ha.continuousAt (hU.mem_nhds hx))
  refine ⟨?_, hd0I, hd1I⟩
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, f' y a ∂mu, ⟨U, hU.mem_nhds hx, hd0I⟩, ?_⟩
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, f'' y a ∂mu, ⟨U, hU.mem_nhds hx, hd1I⟩, ?_⟩
  exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hx, hcI⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
