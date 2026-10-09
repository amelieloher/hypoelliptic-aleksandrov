module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Support
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

/-!
# The non-negative source splitting of the forward equation

The forward equation: for a smooth compactly supported test function `Φ` in the open slab,
the source `g = -𝓛Φ` is the difference `g₁ - g₂` of two non-negative, smooth, compactly
supported sources, `g₁ = g + cχ` and `g₂ = cχ`, with `χ` a smooth cut-off equal to one on the
support of `Φ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ}

/-- The two non-negative smooth compactly supported sources of the forward equation. -/
theorem exists_source_split (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (σ₀ T : ℝ) {Φ : ℝ × EvolutionAmbientState d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ioo σ₀ T ×ˢ univ) :
    ∃ g₁ g₂ : ℝ × EvolutionAmbientState d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ ContDiff ℝ (⊤ : ℕ∞) g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧
      tsupport g₁ ⊆ Ioo σ₀ T ×ˢ univ ∧ tsupport g₂ ⊆ Ioo σ₀ T ×ˢ univ ∧
      (∀ q, 0 ≤ g₁ q) ∧ (∀ q, 0 ≤ g₂ q) ∧
      ∀ q, g₁ q - g₂ q = -forwardRepr B (SectionTwo.identityDrift d) Φ q := by
  set L := forwardRepr B (SectionTwo.identityDrift d) Φ with hLdef
  have hL : ContDiff ℝ (⊤ : ℕ∞) L :=
    contDiff_forwardRepr hB (SectionTwo.identityDrift_smooth d) hΦ
  have hLs : tsupport L ⊆ tsupport Φ := tsupport_forwardRepr_subset B _ Φ
  have hLc : HasCompactSupport L := hΦc.mono' ((subset_tsupport L).trans hLs)
  obtain ⟨c0, hc0⟩ := hL.continuous.bounded_above_of_compact_support hLc
  set c : ℝ := max c0 0 with hc
  have hc0' : 0 ≤ c := le_max_right _ _
  have hLc' : ∀ q, |L q| ≤ c := fun q =>
    (by simpa using hc0 q : |L q| ≤ c0).trans (le_max_left _ _)
  have hV : IsOpen (Ioo σ₀ T ×ˢ (univ : Set (EvolutionAmbientState d))) :=
    isOpen_Ioo.prod isOpen_univ
  obtain ⟨χ, hχ, hχc, hχs, hχ01, hχ1⟩ := SectionTwo.exists_smooth_cutoff hΦc hV hΦs
  have hΦχ : tsupport Φ ⊆ tsupport χ := fun q hq =>
    subset_tsupport _ (by rw [Function.mem_support, hχ1 q hq]; exact one_ne_zero)
  have hLz : ∀ q, q ∉ tsupport χ → L q = 0 := fun q hq =>
    forwardRepr_eq_zero_of_notMem_tsupport B _ Φ (fun h => hq (hΦχ h))
  have hχz : ∀ q, q ∉ tsupport χ → χ q = 0 := fun q hq => image_eq_zero_of_notMem_tsupport hq
  have hsupp1 : Function.support (fun q => -L q + c * χ q) ⊆ tsupport χ := by
    intro q hq
    by_contra h
    exact hq (by simp [hLz q h, hχz q h])
  have hsupp2 : Function.support (fun q => c * χ q) ⊆ tsupport χ := by
    intro q hq
    by_contra h
    exact hq (by simp [hχz q h])
  refine ⟨fun q => -L q + c * χ q, fun q => c * χ q, hL.neg.add (contDiff_const.mul hχ),
    contDiff_const.mul hχ, hχc.mono' hsupp1, hχc.mono' hsupp2, ?_, ?_, ?_, ?_, fun q => by ring⟩
  · exact (closure_minimal hsupp1 (isClosed_tsupport χ)).trans hχs
  · exact (closure_minimal hsupp2 (isClosed_tsupport χ)).trans hχs
  · intro q
    by_cases hq : q ∈ tsupport Φ
    · have h1 := (abs_le.mp (hLc' q)).2
      simp only [hχ1 q hq, mul_one]
      linarith
    · have h0 : L q = 0 := forwardRepr_eq_zero_of_notMem_tsupport B _ Φ hq
      show 0 ≤ -L q + c * χ q
      rw [h0]
      simpa using mul_nonneg hc0' (hχ01 q).1
  · exact fun q => mul_nonneg hc0' (hχ01 q).1

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
