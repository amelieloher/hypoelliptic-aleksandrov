module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness

/-!
# Spatial slices of smooth neighborhood data

This module transfers the supplied smooth-neighborhood regularity on a closed
parabolic cylinder to the fixed-time spatial coefficient slices used in local
residual identities.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped Matrix.Norms.Elementwise

/-- A matrix-coefficient entry is spatially `C¹` at each time in the closed
time interval when the matrix field is smooth near the closed cylinder. -/
theorem contDiffOn_one_coefficientEntry_spatialSlice_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ r : ℝ) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hr : r ∈ Set.Icc r₀ r₁) (i j : Fin d) :
    ContDiffOn ℝ 1 (fun y => a r y i j) Ω := by
  obtain ⟨U, _, hQU, haU⟩ := ha
  have hai : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => a z.1 z.2 i) U :=
    (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haU
      (fun _ _ => Set.mem_univ _)
  have haij : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hai
      (fun _ _ => Set.mem_univ _)
  have hembedding : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => (r, y)) :=
    contDiff_const.prodMk contDiff_id
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => a r y i j) Ω :=
    haij.comp hembedding.contDiffOn fun y hy =>
      hQU ⟨hr, subset_closure hy⟩
  exact hslice.of_le (by simp)

/-- A vector-field entry is continuous on each spatial slice at a time in the
closed interval when the vector field is smooth near the closed cylinder. -/
theorem continuousOn_vectorEntry_spatialSlice_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ r : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hr : r ∈ Set.Icc r₀ r₁) (j : Fin d) :
    ContinuousOn (fun y => b r y j) Ω := by
  obtain ⟨U, _, hQU, hbU⟩ := hb
  have hbj : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => b z.1 z.2 j) U :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hbU
      (fun _ _ => Set.mem_univ _)
  have hembedding : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => (r, y)) :=
    contDiff_const.prodMk contDiff_id
  exact (hbj.comp hembedding.contDiffOn fun y hy =>
    hQU ⟨hr, subset_closure hy⟩).continuousOn

/-- A scalar field is continuous on each spatial slice at a time in the closed
interval when it is smooth near the closed cylinder. -/
theorem continuousOn_scalar_spatialSlice_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ r : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hr : r ∈ Set.Icc r₀ r₁) :
    ContinuousOn (fun y => c r y) Ω := by
  obtain ⟨U, _, hQU, hcU⟩ := hc
  have hembedding : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => (r, y)) :=
    contDiff_const.prodMk contDiff_id
  exact (hcU.comp hembedding.contDiffOn fun y hy =>
    hQU ⟨hr, subset_closure hy⟩).continuousOn

end HypoellipticAleksandrov.Parabolic.Dirichlet
