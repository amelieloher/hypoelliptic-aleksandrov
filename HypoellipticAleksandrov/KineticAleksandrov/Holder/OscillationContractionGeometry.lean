module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Nested source cylinders and a finite half-density alternative -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- Increasing a positive radius enlarges the literal Euclidean kinetic cylinder. -/
theorem backwardCylinder_radius_mono {d : ℕ} (P0 : KineticPoint d) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) : backwardCylinder P0 r ⊆ backwardCylinder P0 R := by
  have hR := hr.trans_le hrR
  have hsq := pow_le_pow_left₀ hr.le hrR 2
  have hcube := pow_le_pow_left₀ hr.le hrR 3
  intro P hP
  refine ⟨by linarith only [hP.1, hsq], hP.2.1, ?_, ?_⟩
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
    exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hP.2.2.1).trans_le hrR
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
    exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp
      hP.2.2.2).trans_le hcube

/-- At least one side of a real value threshold occupies half a finite sampling region. -/
theorem half_density_alternative {d : ℕ} (u : KineticPoint d → ℝ)
    (E : Set (KineticPoint d)) (b : ℝ) :
    (1 / 2 : ℝ) * (volume E).toReal ≤ (volume ({P | u P ≤ b} ∩ E)).toReal ∨
      (1 / 2 : ℝ) * (volume E).toReal ≤ (volume ({P | b ≤ u P} ∩ E)).toReal := by
  have heq : ({P | u P ≤ b} ∩ E) ∪ ({P | b ≤ u P} ∩ E) = E := by
    ext P
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro h
      rcases le_total (u P) b with hb | hb
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
  have hb := measureReal_union_le (μ := volume) ({P | u P ≤ b} ∩ E) ({P | b ≤ u P} ∩ E)
  rw [heq] at hb
  change (volume E).toReal ≤ (volume ({P | u P ≤ b} ∩ E)).toReal +
    (volume ({P | b ≤ u P} ∩ E)).toReal at hb
  by_cases h : (1 / 2 : ℝ) * (volume E).toReal ≤ (volume ({P | u P ≤ b} ∩ E)).toReal
  · exact Or.inl h
  · exact Or.inr (by linarith only [hb, h])

end HypoellipticAleksandrov.KineticAleksandrov.Holder
