module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflectedRetraction
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Boundary limits under the Section-5 retractions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- Uniform continuity transfers a compact-boundary upper bound through a close map. -/
theorem boundary_value_le_of_close_map {E : Type*} [MetricSpace E]
    {K S : Set E} {u : E → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    (hSK : S ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ T : E → E,
      (∀ x ∈ S, T x ∈ K) → (∀ x ∈ S, dist (T x) x < η) →
      ∀ x ∈ S, max (u (T x)) 0 ≤ sSup ((fun x => max (u x) 0) '' S) + ε := by
  have hc : ContinuousOn (fun x => max (u x) 0) K := hu.sup continuousOn_const
  obtain ⟨η,hη,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨η,hη,?_⟩
  intro T hTK hdist x hx
  have hd := hclose (T x) (hTK x hx) x (hSK hx) (hdist x hx)
  have hb : BddAbove ((fun x => max (u x) 0) '' S) :=
    (hK.bddAbove_image hc).mono (image_mono hSK)
  have hs := le_csSup hb (mem_image_of_mem (fun x => max (u x) 0) hx)
  rw [Real.dist_eq] at hd
  have hle := (abs_lt.mp hd).2
  linarith

/-- Exit-boundary values on inner cylinders approach the original exit-boundary bound. -/
theorem comparison_exit_boundary_approx {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2),
      δ < η → ∀ P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt,
        max (u P) 0 ≤ sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) + ε := by
  have hS : exitBoundary Z₀ R hR ⊆ closure (forwardCylinder Z₀ R hR) :=
    fun _ h => h.1
  obtain ⟨r,hr,hbound⟩ := boundary_value_le_of_close_map
    (isCompact_closure_forwardCylinder Z₀ R hR) hu hS hε
  obtain ⟨η,hη,hclose⟩ := innerRetraction_uniformly_to_identity Z₀ R hR r hr
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  rw [← innerRetraction_image_exitBoundary Z₀ R hR δ hδ0 hδlt] at hP
  obtain ⟨x,hx,rfl⟩ := hP
  apply hbound (innerRetraction Z₀ R hR δ hδ0 hδlt) ?_ ?_ x hx
  · intro y hy
    apply subset_closure (closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt ?_)
    rw [← innerRetraction_image_closure Z₀ R hR δ hδ0 hδlt]
    exact mem_image_of_mem _ (hS hy)
  · exact fun y hy => hclose δ hδ0 hδlt hδη y (hS hy)

/-- The same compact-boundary passage in the backward kinetic geometry. -/
theorem comparison_kinetic_boundary_approx {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (backwardCylinder P₀ R)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2),
      δ < η → ∀ P ∈ kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R),
        max (u P) 0 ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + ε := by
  have hS : kineticBoundary P₀ R ⊆ closure (backwardCylinder P₀ R) := fun _ h => h.1
  have hcompact : IsCompact (closure (backwardCylinder P₀ R)) := by
    have h := (isCompact_closure_forwardCylinder (kineticReflection P₀) R hR).image
      (continuous_kineticReflection d)
    rw [kineticReflection_image_closure, kineticReflection_image_forwardCylinder,
      kineticReflection_involutive P₀] at h
    exact h
  obtain ⟨r,hr,hbound⟩ := boundary_value_le_of_close_map hcompact hu hS hε
  obtain ⟨η,hη,hclose⟩ := reflectedInnerRetraction_uniformly_to_identity P₀ R hR r hr
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  rw [← reflectedInnerRetraction_image_kineticBoundary P₀ R hR δ hδ0 hδlt] at hP
  obtain ⟨x,hx,rfl⟩ := hP
  apply hbound (reflectedInnerRetraction P₀ R hR δ hδ0 hδlt) ?_ ?_ x hx
  · intro y hy
    have hi := closure_reflected_innerCylinder_subset P₀ R hR δ hδ0 hδlt
    apply subset_closure (hi ?_)
    rw [kineticReflection_image_innerCylinder P₀ R hR δ hδ0 hδlt]
    rw [← reflectedInnerRetraction_image_closure P₀ R hR δ hδ0 hδlt]
    exact mem_image_of_mem _ (hS hy)
  · exact fun y hy => hclose δ hδ0 hδlt hδη y (hS hy)

end HypoellipticAleksandrov.KineticAleksandrov
