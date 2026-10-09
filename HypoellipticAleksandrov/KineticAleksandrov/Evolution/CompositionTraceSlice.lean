module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
public import Mathlib.Topology.Algebra.Indicator

/-!
# Intermediate slices of a classical terminal solution

Zero extension across the lateral boundary is continuous. Strictly earlier slices
are smooth on the open state fiber. These facts justify compact interior cutoff data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Function
open scoped Topology

/-- A classical solution restricted to any earlier state slice is continuous on the
closed state fiber. -/
theorem IsClassicalTerminalSolution.continuousOn_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r ≤ τ) :
    ContinuousOn (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (closure (evolutionStateSet Ω γ r)) := by
  refine hu.2.1.comp
    (KineticPoint.continuous_mk continuous_const continuous_fst continuous_snd).continuousOn ?_
  intro x hx
  have hx' : x ∈ closure (movingDomain Ω γ r) ×ˢ (univ : Set (PDE.Vec n)) := by
    simpa only [evolutionStateSet, closure_prod_eq, closure_univ] using hx
  exact ⟨hrτ, hx'.1⟩

/-- Extending an intermediate slice by zero outside its state fiber is continuous. -/
theorem IsClassicalTerminalSolution.continuous_zeroExtended_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r ≤ τ) :
    Continuous ((evolutionStateSet Ω γ r).indicator
      (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)) := by
  apply continuous_indicator ?_ (hu.continuousOn_slice hrτ)
  intro x hx
  have hx' : x ∈ frontier (movingDomain Ω γ r) ×ˢ (univ : Set (PDE.Vec n)) := by
    simpa only [evolutionStateSet, frontier_prod_univ_eq] using hx
  exact hu.2.2.2.2.2 ⟨r, x.1, x.2⟩ ⟨hrτ, hx'.1⟩

/-- A strictly earlier slice is smooth on the open state fiber. -/
theorem IsClassicalTerminalSolution.contDiffOn_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r < τ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (evolutionStateSet Ω γ r) := by
  exact hu.2.2.1.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun x hx => ⟨hrτ, hx.1⟩)

/-- Multiplying an interior-smooth function by an interior-supported smooth cutoff gives
an ambient smooth function, irrespective of the original function outside the open set. -/
theorem contDiff_mul_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {χ g : E → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hs : tsupport χ ⊆ U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hs hx)))
  · have he : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hz : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℝ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov
